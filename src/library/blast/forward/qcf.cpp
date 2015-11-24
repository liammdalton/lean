/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/expr_sets.h"
#include "library/constants.h"
#include "library/blast/blast.h"
#include "library/blast/action_result.h"
#include "library/blast/congruence_closure.h"
#include "library/blast/forward/forward_actions.h"
#include "library/blast/proof_expr.h"
#include "library/blast/choice_point.h"
#include "library/blast/hypothesis.h"
#include "library/blast/util.h"
#include "library/expr_lt.h"
#include "library/head_map.h"
#include "util/list.h"

namespace lean {
namespace blast {

/* Questions
1. Lazy? Or instantiate all?
2. Expose CC?
3. Exhaustive?
*/

class qcf {
    expr         m_type, m_proof;

    list<expr>   m_locals;
    expr_set     m_matched;

    static expr polarize(expr const & e, bool neg) {
        expr not_e;
        if (neg && is_not(e, not_e)) {
            return not_e;
        } else if (neg) {
            return get_app_builder().mk_not(e);
        } else {
            return e;
        }
    }

    list<congruence_closure> falsify(expr const & phi, bool neg, congruence_closure const & cc) {
        expr lhs, rhs, not_phi;
        if (is_and(phi, lhs, rhs)) {

        } else if (is_or(phi, lhs, rhs)) {

        } else if (is_not(phi, not_phi)) {
            return falsify(not_phi, !neg, cc);
        } else if (is_pi(phi)) {

        } else if (is_iff(phi)) {
            // TODO(dhs): split into two implications

        } else if (!is_prop(phi)) {
            // TODO(dhs): do I return [to_list(cc)] in both cases?
            if (neg) { return to_list(cc); }
            else { return list<congruence_closure>(); }
        } else if (!has_local(phi)) {
            congruence_closure new_cc = cc;
            new_cc.assume(phi);
            if (new_cc.is_inconsistent()) { return to_list(new_cc); }
            else { return list<congruence_closure>(); }
        } else {
            congruence_closure new_cc = cc;
            new_cc.assume(polarize(phi, neg));
            if (new_cc.is_inconsistent()) { return list<congruence_closure>(); }
            else { // } return match(
                    // bool is_relation_app(expr const & e, name & rop, expr & lhs, expr & rhs);


        }

    }

        // TODO(dhs): finish
        return list<congruence_closure>(); // FIXME
    }

    list<congruence_closure> match(list<expr> const & es, congruence_closure const & cc) {
        // TODO(dhs): implement
        return list<congruence_closure>(); // FIXME
    }

    // TODO(dhs): we probably want to return the new expressions
    // instead of adding them to state directly, since we might want
    // to simplify them or otherwise post-filter first.
    void mk_hypothesis(congruence_closure const & cc) {
        expr proof = m_proof;
        expr type = m_type;
        for_each(m_locals, [&](expr const & local) {
                expr value = cc.get_root(get_eq_name(), local);
                lean_assert(!is_local(value));
                proof = mk_app(proof, value);
                type = instantiate(binding_body(type), value);
            });
        curr_state().mk_hypothesis(type, proof);
    }

    /* Sets [m_type] and [m_proof] */
    void gather_universals(expr const & type, expr const & proof) {
        // TODO(dhs): implement
        expr m_type = type;
        expr m_proof = proof;
    }

    /* Populates [m_locals] */
    expr telescope_type() {
        expr type = whnf(m_type);
        buffer<expr> ls;
        while (is_pi(type)) {
            expr d = instantiate_rev(binding_domain(m_type), ls.size(), ls.data());
            expr l = mk_fresh_local(d, binding_info(type));
            ls.push_back(l);
            type = whnf(instantiate(binding_body(m_type), l));
        }
        m_locals = to_list(ls);
        return type;
    }

public:
    // TODO(dhs): what do I do about polymorphic constants?
    // [tmp_type_context] with urefs?
    action_result operator()(expr const & type, expr const & proof) {
        gather_universals(type, proof);
        expr phi = telescope_type();

        list<congruence_closure> ccs = falsify(phi, false, get_cc());
        if (is_nil(ccs)) {
            return action_result::failed();
        } else {
            for_each(ccs, [&](congruence_closure const & cc) {
                    mk_hypothesis(cc);
                });
            return action_result::new_branch();
        }
    }
};

action_result qfc_action(list<gexpr> const & lemmas) {
    return action_result::failed();
}

}}
