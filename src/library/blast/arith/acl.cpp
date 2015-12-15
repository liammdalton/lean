/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include <vector>
#include <algorithm>
#include <memory>
#include "util/sexpr/option_declarations.h"
#include "util/numerics/mpz.h"
#include "library/constants.h"
#include "library/blast/arith/acl.h"
#include "library/blast/arith/num.h"
#include "library/blast/blast.h"
#include "library/blast/trace.h"
#include "library/blast/options.h"
#include "library/blast/simplifier/simplifier.h"
#include "library/num.h"

#ifndef LEAN_DEFAULT_ACL_MAX_STEPS_PER_ACTION
#define LEAN_DEFAULT_ACL_MAX_STEPS_PER_ACTION 10
#endif

/* Description:

This module performs linear and some non-linear arithmetic, as described in the paper [ACL2].

The architecture is as follows:

When the action [assert_acl_action(hypothesis_idx)] is called, we
call the [linearizer] to construct a list of polynomial inequalities, of the form

<<
0 < Sum_i [<numeral_i> * <unknown_i>] + <numeral>
>>

where the inequality may or may not be strict.

The linearizer stores a [lazy_proof] in each polynomial inequality that it creates, so that
we can construct a fully formal proof of any contradiction we find.

Then, we proceed to create new polynomial inequalities from old polynomial inequaities, all the while
maintaining a trace of how the new polynomial inequalities can be justified in terms of the old ones.

If we do construct a polynomial inequality of the form [0 < 0, 0 < - <pos>, 0 <= - <pos>], we have
found a contradiction, and we must start to construct a formal proof of this fact.
*/

namespace lean {
namespace blast {

/** Globals */
static name * g_acl_trace_name           = nullptr;
static name * g_acl_max_steps_per_action = nullptr;

/** Option getters */
unsigned get_acl_max_steps_per_action() {
    return ios().get_options().get_unsigned(*g_acl_max_steps_per_action, LEAN_DEFAULT_ACL_MAX_STEPS_PER_ACTION);
}

/** Basic data-structures **/

/* Monomials */
class monomial {
    mpz      m_coeff;
    unsigned m_unknown_idx;
public:
    monomial(mpz coeff, unsigned unknown_idx): m_coeff(coeff), m_unknown_idx(unknown_idx) {}
    mpz const & get_coeff() const { return m_coeff; }
    unsigned get_unknown_idx() const { return m_unknown_idx; }
};

struct monomial_lt {
    bool operator()(monomial const & m1, monomial const & m2) const {
        return m2.get_unknown_idx() < m1.get_unknown_idx();
    }
};

bool is_lt(monomial const & m1, monomial const & m2) {
    return monomial_lt()(m1, m2);
}

std::ostream & operator<<(std::ostream & out, monomial const & m) {
    out << "(" << m.get_coeff() << ", " << m.get_unknown_idx() << ")";
    return out;
}

/* Proof trails */
typedef std::function<expr()> lazy_proof;

class poly;
struct poly_parents {
    std::shared_ptr<poly> m_p, m_q;
    mpz m_p_scale, m_q_scale;
public:
    poly_parents(poly const & p, poly const & q, mpz const & p_scale, mpz const & q_scale);

    poly const & get_p() const { return *(m_p.get()); }
    poly const & get_q() const { return *(m_q.get()); }
    mpz const & get_p_scale() const { return m_p_scale; }
    mpz const & get_q_scale() const { return m_q_scale; }
};

/* Polynomial inequalities */
enum class poly_kind { Normal, Contradiction, Trivial };

class poly {
    /* Represents a polynomial inequality of the following form:
       0 [<, <=] sum_i (m_monomials[i].coeff * m_monomials[i].unknown) + m_offset
       where the inequality is strict iff `m_strict = true`. */
    expr m_A;
    list<monomial> m_monomials;
    mpz m_offset;
    bool m_strict;

    /* Since we need to prove any resulting "contradicting" polynomial we derive,
       we need to track a justification for each such polynomial.
       There are two cases:
       1. A polynomial inequality may be a "linearization" of an existing hypothesis. In this case
       we store the [hypothesis_idx] of this existing hypothesis. The "linearization"
       module will be responsible for this stage of the proof.
       2. A polynomial inequality may be the result of resolving two existing polynomial inequalities
       together. In this case, we store the two parents along with the scaling factors. To reconstruct
       the proof, we use the "poly_cancel" lemmas. */

    // Poor man's union
    optional<lazy_proof>   m_lazy_proof;    // Case 1
    optional<poly_parents> m_parents;       // Case 2
public:
    poly(poly const & p):
        m_A(p.m_A), m_monomials(p.m_monomials), m_offset(p.m_offset),
        m_strict(p.m_strict), m_lazy_proof(p.m_lazy_proof), m_parents(p.m_parents) {}

    poly(expr const & A, buffer<monomial> const & monomials, mpz offset, poly_parents const & parents):
        m_A(A), m_monomials(to_list(monomials)), m_offset(offset),
        m_strict(parents.get_p().is_strict() || parents.get_q().is_strict()), m_parents(parents) {}

    poly(expr const & A, buffer<monomial> const & monomials, mpz offset, bool strict, lazy_proof const & lproof):
        m_A(A), m_monomials(to_list(monomials)), m_offset(offset), m_strict(strict), m_lazy_proof(lproof) {}

    list<monomial> const & get_monomials() const { return m_monomials; }
    bool is_strict() const { return m_strict; }
    mpz const & get_offset() const { return m_offset; }

    poly_kind kind() const {
        if (!is_nil(m_monomials)) return poly_kind::Normal;
        else if (is_strict() && m_offset.is_nonpos()) return poly_kind::Contradiction;
        else if (!is_strict() && m_offset.is_neg()) return poly_kind::Contradiction;
        else return poly_kind::Trivial;
    }

    name get_resolve_name() const {
        lean_assert(m_parents);
        if (m_parents->get_p().is_strict() && m_parents->get_q().is_strict()) {
            return get_ordered_arith_resolve_lt_lt_name();
        } else if (m_parents->get_p().is_strict()) {
            return get_ordered_arith_resolve_lt_le_name();
        } else if (m_parents->get_q().is_strict()) {
            return get_ordered_arith_resolve_le_lt_name();
        } else {
            return get_ordered_arith_resolve_le_le_name();
        }
    }

    expr const & get_A() const { return m_A; }

    expr get_clean_thm() const {
        return get_app_builder().mk_lt(m_A, get_app_builder().mk_zero(m_A), mpz_to_expr(m_offset, m_A));
    }

    /* This function returns a proof of the polynomial inequality, except it does not
       take into account the cancellations at each resolution step, hence the name
       [get_proof_messy()]. We have the following proof:

       original_hypotheses -> greatest ancestor                     (linearizer's responsibility, base case)
                           -> this polynomial with no cancellations (recursive case)
                           =  this polynomial                       (by fusion, outside this method)
                           -> false                                 (by some variation of `0 < c -> false`
                                                                     for e.g. `c <= 0`)
    */
    expr get_proof_messy() const {
        if (m_lazy_proof) {
            return (*m_lazy_proof)();
        } else {
            lean_assert(m_parents);
            poly const & p = m_parents->get_p();
            poly const & q = m_parents->get_q();
            expr p_proof = p.get_proof_messy();
            expr q_proof = q.get_proof_messy();
            expr p_scale_pos = prove_positive(m_parents->get_p_scale(), m_A);
            expr q_scale_pos = prove_positive(m_parents->get_q_scale(), m_A);
            expr pf_messy = get_app_builder().mk_app(get_resolve_name(), {p_proof, q_proof, p_scale_pos, q_scale_pos});
            return pf_messy;
        }
    }

    /* Only valid if [m_monomials] is non-empty */
    bool is_positive() const { return get_major_coeff().is_pos(); }
    unsigned get_major_idx() const { return head(m_monomials).get_unknown_idx(); }
    mpz const & get_major_coeff() const { return head(m_monomials).get_coeff(); }
};

std::ostream & operator<<(std::ostream & out, poly const & p) {
    out << "0 " << (p.is_strict() ? "<" : "<=") << " ";
    for (auto m : p.get_monomials()) out << m << " + ";
    out << p.get_offset();
    return out;
}

poly_parents::poly_parents(poly const & p, poly const & q, mpz const & p_scale, mpz const & q_scale):
    m_p(new poly(p)), m_q(new poly(q)), m_p_scale(p_scale), m_q_scale(q_scale) {}

/* Linearizer */
class linearizer {
    typedef rb_map<expr, unsigned, expr_quick_cmp> unknown_map;
    unknown_map       m_unknown_to_idx;
    unsigned          m_num_unknowns{0};

    bool type_ok(expr const & A) {
        blast_tmp_type_context m_tmp_tctx;
        return static_cast<bool>(m_tmp_tctx->mk_class_instance(get_app_builder().mk_linear_ordered_comm_ring(A)));
    }

    unsigned get_unknown_idx(expr const & e) {
        if (auto i = m_unknown_to_idx.find(e)) {
            return *i;
        } else {
            unsigned idx = m_num_unknowns;
            m_unknown_to_idx.insert(e, idx);
            m_num_unknowns++;
            return idx;
        }
    }

    list<poly> linearize(expr const & A, expr const & rhs, bool strict, hypothesis_idx hidx, lazy_proof const & lproof) {
        /* TODO(dhs): we are temporarily assuming the input comes in the form of
           [0 [<,<=] Sum_i (<numeral_i> * <unknown_i>)], pre-fused and everything.
           We will implement the downstream processing, test, and then implement the
           linearization in earnest. */
        buffer<monomial> monomials;
        mpz offset{0};
        bool found_offset = false;
        expr e = rhs;

        expr e1, e2;
        while (is_add(e, e1, e2)) {
            expr numeral, unknown;
            if (is_mul(e1, numeral, unknown)) {
                optional<mpz> num = to_num(numeral);
                if (!num) throw exception("[TODO] ACL requires (num * unknown) monomials");
                monomials.emplace_back(*num, get_unknown_idx(unknown));
            } else {
                optional<mpz> num = to_num(e1);
                if (!num) throw exception(sstream() << "[TODO] Any non-mul must be a numeral during development: " << e1);
                offset = *num;
            }
            e = e2;
        }
        // TODO(dhs): avoid code duplication
        expr numeral, unknown;
        if (is_mul(e, numeral, unknown)) {
            optional<mpz> num = to_num(numeral);
            if (!num) throw exception("[TODO] ACL requires (num * unknown) monomials");
            monomials.emplace_back(*num, get_unknown_idx(unknown));
        } else {
            optional<mpz> num = to_num(e);
            if (!num) throw exception(sstream() << "[TODO] Any non-mul must be a numeral during development: " << e1);
            offset = *num;
        }

        std::sort(monomials.begin(), monomials.end(), monomial_lt());

        return list<poly>(poly(A, monomials, offset, strict, lproof));
    }

public:
    list<poly> linearize(hypothesis_idx hidx) {
        hypothesis const & h = curr_state().get_hypothesis_decl(hidx);
        /* TODO(dhs): as a pre-process step, put 0 on the LHS of the inequality.
           For now we assume it is already in this form. */
        expr A, lhs, rhs;
        bool strict;
        // TODO(dhs): handle equality
        if (is_lt(h.get_type(), A, lhs, rhs) && type_ok(A)) {
            return linearize(A, rhs, true, hidx, [=]() { return h.get_self(); });
        } else if (is_le(h.get_type(), A, lhs, rhs) && type_ok(A)) {
            return linearize(A, rhs, false, hidx, [=]() { return h.get_self(); });
        } else {
            return list<poly>();
        }
    }
};

/* Poly-pot */
class poly_pot {
    list<poly> m_positives;
    list<poly> m_negatives;
public:
    void insert(poly const & p) {
        if (p.is_positive()) {
            m_positives = cons(p, m_positives);
        } else {
            m_negatives = cons(p, m_negatives);
        }
    }
    list<poly> get_positives() { return m_positives; }
    list<poly> get_negatives() { return m_negatives; }
};

/* acl_branch_extension */
static unsigned g_ext_id = 0;

struct acl_branch_extension : public branch_extension {
private:
    typedef rb_map<unsigned, poly_pot, unsigned_cmp>    poly_pot_map;
    linearizer        m_linearizer;
    poly_pot_map      m_poly_pot_map;
    list<poly>        m_todo;

public:
    acl_branch_extension() {}
    acl_branch_extension(acl_branch_extension const & ext):
        m_linearizer(ext.m_linearizer), m_poly_pot_map(ext.m_poly_pot_map), m_todo(ext.m_todo) {}
    virtual branch_extension * clone() override { return new acl_branch_extension(*this); }

    void put_todo(buffer<poly> const & todo) { m_todo = to_list(todo); }
    void get_todo(buffer<poly> & todo) {
        to_buffer(m_todo, todo);
        m_todo = list<poly>();
    }

    list<poly> linearize(hypothesis_idx hidx) { return m_linearizer.linearize(hidx); }

    poly_pot insert_poly_into_pot(poly const & p) {
        poly_pot const * pot_p = m_poly_pot_map.find(p.get_major_idx());
        poly_pot pot = (pot_p ? *pot_p : poly_pot());
        pot.insert(p);
        m_poly_pot_map.insert(p.get_major_idx(), pot);
        return pot;
    }
};

static acl_branch_extension & get_acl_extension() {
    return static_cast<acl_branch_extension&>(curr_state().get_extension(g_ext_id));
}

/* Contradictions */
struct found_contradiction {
    poly m_contradiction;
public:
    found_contradiction(poly const & p): m_contradiction(p) {}
    poly const & get_contradiction() const { return m_contradiction; }
};

/* ACL function */
class acl_fn {
    acl_branch_extension &        m_ext;
    buffer<poly>                  m_todo;
    unsigned                      m_num_steps{0};

    optional<poly>                m_contradiction;

    /* Options */
    unsigned                      m_max_steps{get_acl_max_steps_per_action()};

    void register_todo(poly const & p) {
        switch (p.kind()) {
        case poly_kind::Normal:
            m_todo.push_back(p);
            lean_trace(*g_acl_trace_name, ios().get_diagnostic_channel() << "todo: " << p << "\n";);
            break;
        case poly_kind::Contradiction:
            lean_trace(*g_acl_trace_name, ios().get_diagnostic_channel() << "contradiction: " << p << "\n";);
            throw found_contradiction(p);
            break;
        case poly_kind::Trivial:
            lean_trace(*g_acl_trace_name, ios().get_diagnostic_channel() << "trivial: " << p << "\n";);
            break;
        }
    }

    void scale_monomials(list<monomial> const & monomials, mpz const & scale, buffer<monomial> & new_monomials) {
        lean_assert(!is_nil(monomials));
        list<monomial> ms = monomials;
        while (!is_nil(ms)) {
            monomial m = head(ms);
            mpz new_coeff{0};
            new_coeff.addmul(scale, m.get_coeff());
            new_monomials.emplace_back(new_coeff, m.get_unknown_idx());
            ms = tail(ms);
        }
    }

    void resolve_polys(poly const & p, poly const & q) {
        mpz p_coeff{p.get_major_coeff()};
        mpz q_coeff{q.get_major_coeff()};
        p_coeff.abs();
        q_coeff.abs();
        mpz p_scale{lcm(p_coeff, q_coeff)};
        mpz q_scale{p_scale};
        p_scale /= p_coeff;
        q_scale /= q_coeff;

        lean_trace(*g_acl_trace_name, ios().get_diagnostic_channel() << p << " |***| " << q
                   << " -- (" << p_scale << ", " << q_scale << ")\n";);

        // TODO(dhs): clean this up! This is ridiculous.

        list<monomial> p_monomials = p.get_monomials();
        list<monomial> q_monomials = q.get_monomials();

        lean_assert(!is_nil(p_monomials));
        lean_assert(!is_nil(q_monomials));

        buffer<monomial> new_monomials;

        /* We can skip the first element, since we know they will cancel */
        monomial p_major = head(p_monomials);
        monomial q_major = head(p_monomials);

        lean_assert(p_major.get_unknown_idx() == q_major.get_unknown_idx());
        if (p_major.get_unknown_idx() != q_major.get_unknown_idx()) throw exception("ACL::resolving wrong polys");

        p_monomials = tail(p_monomials);
        q_monomials = tail(q_monomials);

        /* Now, we proceed, advancing one iterator at a time */
        while (true) {
            if (is_nil(p_monomials) && is_nil(q_monomials)) {
                break;
            } else if (is_nil(p_monomials)) {
                scale_monomials(q_monomials, q_scale, new_monomials);
                break;
            } else if (is_nil(q_monomials)) {
                scale_monomials(p_monomials, p_scale, new_monomials);
                break;
            } else {
                monomial const & p_m = head(p_monomials);
                monomial const & q_m = head(q_monomials);
                mpz new_coeff{0};
                if (is_lt(p_m, q_m)) {
                    new_coeff.addmul(p_scale, p_m.get_coeff());
                    if (!new_coeff.is_zero()) new_monomials.emplace_back(new_coeff, p_m.get_unknown_idx());
                    p_monomials = tail(p_monomials);
                } else if (is_lt(q_m, p_m)) {
                    new_coeff.addmul(q_scale, q_m.get_coeff());
                    if (!new_coeff.is_zero()) new_monomials.emplace_back(new_coeff, q_m.get_unknown_idx());
                    q_monomials = tail(q_monomials);
                } else {
                    new_coeff.addmul(p_scale, p_m.get_coeff());
                    new_coeff.addmul(q_scale, q_m.get_coeff());
                    if (!new_coeff.is_zero()) new_monomials.emplace_back(new_coeff, p_m.get_unknown_idx());
                    p_monomials = tail(p_monomials);
                    q_monomials = tail(q_monomials);
                }
            }
        }
        mpz new_offset{0};
        new_offset.addmul(p_scale, p.get_offset());
        new_offset.addmul(q_scale, q.get_offset());

        register_todo(poly(p.get_A(), new_monomials, new_offset, poly_parents(p, q, p_scale, q_scale)));
    }

    void process_poly(poly const & p) {
        lean_assert(p.kind() == poly_kind::Normal);
        lean_assert(!is_nil(p.get_monomials()));
        poly_pot pot = m_ext.insert_poly_into_pot(p);
        list<poly> to_resolve_with = (p.is_positive() ? pot.get_negatives() : pot.get_positives());
        for (poly const & q : to_resolve_with) resolve_polys(p, q);
    }

public:
    acl_fn(): m_ext(get_acl_extension()) {}

    action_result operator()(hypothesis_idx hidx) {
        try {
            /* There may me some TODO items remaining from the previous invocation. */
            m_ext.get_todo(m_todo);

            /* We convert the new hypothesis into 0, 1, or 2 polynormial inequalities. */
            list<poly> new_todo = m_ext.linearize(hidx);
            for (poly const & p : new_todo) {
                register_todo(p);
            }

            while (!m_todo.empty()) {
                m_num_steps++;
                if (m_num_steps > m_max_steps) {
                    m_ext.put_todo(m_todo);
                    break;
                }
                poly p = m_todo.back();
                m_todo.pop_back();
                process_poly(p);
            }
            // TODO(dhs): If I infer new equalities, add them as hypotheses and return a new branch.
            // (not even checking for equalities yet)
            return action_result::failed();
        } catch (found_contradiction fc) {
            poly const & p = fc.get_contradiction();
            expr const & A = p.get_A();

            expr pf_messy = p.get_proof_messy();
            expr type_messy = infer_type(pf_messy);

            expr type_clean = p.get_clean_thm();
            optional<expr> pf_messy_eq_clean = prove_eq_som_fuse(type_messy, type_clean);
            lean_assert(pf_messy_eq_clean);
            expr id_motive = mk_app(mk_constant(get_id_name(), mk_level_one()), mk_Prop());
            expr pf_clean = get_app_builder().mk_eq_rec(id_motive, pf_messy, *pf_messy_eq_clean);

            expr pf_clean_of_false;

            if (p.is_strict()) {
                if (p.get_offset().is_zero()) pf_clean_of_false = prove_zero_not_lt_zero(A);
                else pf_clean_of_false = prove_zero_not_lt_neg(A, p.get_offset());
            } else {
                pf_clean_of_false = prove_zero_not_le_neg(A, p.get_offset());
            }

            return action_result::solved(mk_app(pf_clean_of_false, pf_clean));
        }
    }
};

/* Setup and teardown */
void initialize_acl() {
    g_acl_trace_name           = new name{"blast", "acl"};
    g_acl_max_steps_per_action = new name{"blast", "acl", "max_steps_per_action"};

    register_unsigned_option(*g_acl_max_steps_per_action, LEAN_DEFAULT_ACL_MAX_STEPS_PER_ACTION,
                             "(blast::acl) max steps of acl per action");

    g_ext_id = register_branch_extension(new acl_branch_extension());
    register_trace_class(*g_acl_trace_name);
}

void finalize_acl() {
    delete g_acl_max_steps_per_action;
    delete g_acl_trace_name;
}

/* Entry points */
action_result assert_acl_action(hypothesis_idx hidx) {
    if (!get_config().m_acl) return action_result::failed();
    return acl_fn()(hidx);
}

}}
