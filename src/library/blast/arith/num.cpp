/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include <iostream>
#include "library/blast/arith/num.h"
#include "library/blast/blast_exception.h"
#include "library/blast/trace.h"
#include "library/blast/blast.h"
#include "library/constants.h"
#include "library/num.h"

namespace lean {
namespace blast {

static name * g_num_trace_name = nullptr;
static name * g_num_trace_simplify_name = nullptr;

/* Convert to Lean expressions */
expr mpz_to_expr_core(mpz const & n, expr const & A) {
    lean_assert(n > 0);
    if (n == 1) return get_app_builder().mk_one(A);
    expr rec = mpz_to_expr_core(n/2, A);
    if (n % mpz(2) == 1) return get_app_builder().mk_bit1(A, rec);
    else return get_app_builder().mk_bit0(A, rec);
}

expr mpz_to_expr(mpz const & n, expr const & A) {
    if (n == 0) return get_app_builder().mk_zero(A);
    else if (n < 0) return get_app_builder().mk_neg(A, mpz_to_expr_core(neg(n), A));
    else return mpz_to_expr_core(n, A);
}

expr mpq_to_expr(mpq const & n, expr const & A) {
    if (n == 0) {
        return get_app_builder().mk_zero(A);
    } else if (n < 0) {
        return get_app_builder().mk_neg(A, mpq_to_expr(neg(n), A));
    } else if (n.is_integer()) {
        return mpz_to_expr_core(n.get_numerator(), A);
    } else if (n.get_numerator() == 1) {
        return get_app_builder().mk_inv(A, mpz_to_expr(n.get_denominator(), A));
    } else {
        return get_app_builder().mk_mul(A,
                                        mpz_to_expr(n.get_numerator(), A),
                                        get_app_builder().mk_inv(A, mpz_to_expr(n.get_denominator(), A)));
    }
}

/* Convert from Lean expressions */
mpq expr_to_mpq(expr const & e) {
    expr arg, arg1, arg2;
    if (auto n = to_num(e)) {
        return mpq(*n);
    } else if (is_add(e, arg1, arg2)) {
        return expr_to_mpq(arg1) + expr_to_mpq(arg2);
    } else if (is_mul(e, arg1, arg2)) {
        return expr_to_mpq(arg1) * expr_to_mpq(arg2);
    } else if (is_inv(e, arg)) {
        return inv(expr_to_mpq(arg));
    } else if (is_neg(e, arg)) {
        return neg(expr_to_mpq(arg));
    } else {
        lean_trace(*g_num_trace_name, tout() << "expression in expr_to_mpq is malformed: " << ppb(e) << "\n";);
        throw blast_exception("expression in expr_to_mpq is malfomed", e);
    }
}

/* Prove positive */
/*
  theorem pos_bit0 {A : Type} [s : linear_ordered_comm_ring A] (a : A) (H : 0 < a) : 0 < bit0 a := sorry
  theorem pos_bit1 {A : Type} [s : linear_ordered_comm_ring A] (a : A) (H : 0 < a) : 0 < bit1 a := sorry
  theorem zero_lt_one {A : Type} [s : linear_ordered_comm_ring A] : 0 < 1 := sorry
*/
pair<expr, expr> prove_positive_core(mpz const & n, expr const & A) {
    lean_assert(n > 0);
    if (n == 1) {
        expr one = get_app_builder().mk_one(A);
        expr pf = get_app_builder().mk_zero_lt_one(A);
        return mk_pair(one, pf);
    } else if (n % mpz(2) == 1) {
        pair<expr, expr> rec = prove_positive_core(n/2, A);
        expr new_num = get_app_builder().mk_bit1(A, rec.first);
        expr new_pf = get_app_builder().mk_app(get_numeral_pos_bit1_name(), {rec.first, rec.second});
        return mk_pair(new_num, new_pf);
    } else {
        pair<expr, expr> rec = prove_positive_core(n/2, A);
        expr new_num = get_app_builder().mk_bit0(A, rec.first);
        expr new_pf = get_app_builder().mk_app(get_numeral_pos_bit0_name(), {rec.first, rec.second});
        return mk_pair(new_num, new_pf);
    }
}

expr prove_positive(mpz const & n, expr const & A) {
    return prove_positive_core(n, A).second;
}

expr prove_positive(mpq const & n, expr const & A) {
    if (n.is_integer()) {
        return prove_positive(n.get_numerator(), A);
    } else {
        expr pf_a = prove_positive(n.get_numerator(), A);
        expr pf_b = prove_positive(n.get_denominator(), A);
        return get_app_builder().mk_app(get_ordered_arith_mulinv_pos_of_pos_pos_name(), {pf_a, pf_b});
    }
}

/* Prove a contradiction */
/*
  theorem zero_not_lt_zero [s : linear_ordered_comm_ring A] : 0 < 0 → false := sorry
  theorem pos_not_neg [s : linear_ordered_comm_ring A] (c : A) : 0 < c → 0 < - c → false := sorry
  theorem pos_not_nonpos [s : linear_ordered_comm_ring A] (c : A) : 0 < c → 0 ≤ - c → false := sorry
*/

// TODO(dhs): clean this up, stop synthesizing and checking everywhere
expr prove_zero_not_lt_zero(expr const & A) {
    return get_app_builder().mk_zero_not_lt_zero(A);
}

expr prove_zero_not_lt_neg(expr const & A, mpq const & nc) {
    return get_app_builder().mk_app(get_ordered_arith_zero_not_lt_neg_name(), 4, {prove_positive(neg(nc), A)});
}

expr prove_zero_not_le_neg(expr const & A, mpq const & nc) {
    return get_app_builder().mk_app(get_ordered_arith_zero_not_le_neg_name(), 4, {prove_positive(neg(nc), A)});
}

/* Note: this must be called on a numeral, not any numeral expression */
expr prove_num_positive(expr const & e, expr const & type) {
    expr arg;
    if (is_bit0(e, arg)) {
        return get_app_builder().mk_app(get_numeral_pos_bit0_name(), prove_num_positive(arg, type));
    } else if (is_bit1(e, arg)) {
        return get_app_builder().mk_app(get_numeral_pos_bit1_name(), prove_num_positive(arg, type));
    } else if (is_one(e)) {
        return get_app_builder().mk_zero_lt_one(type);
    } else {
        lean_trace(*g_num_trace_name, tout() << "prove_num_positive called on zero or non_numeral: " << ppb(e) << "\n";);
        throw exception("prove_num_positive called on zero or non_numeral");
    }
}

/* Note: must be called on a normalized numeral */
expr prove_ne_zero(expr const & e, expr const & type) {
    expr neg_e, inv_e, num, den;
    if (is_neg(e, neg_e)) {
        return get_app_builder().mk_app(get_ordered_arith_nonzero_of_neg_name(), 4, {prove_ne_zero(neg_e, type)});
    } else if (is_inv(e, inv_e)) {
        return get_app_builder().mk_app(get_inv_ne_zero_name(), 4, {prove_ne_zero(inv_e, type)});
    } else if (is_mulinv(e, num, den)) {
        expr pf_num_ne_zero = prove_ne_zero(num, type);
        expr pf_den_ne_zero = prove_ne_zero(den, type);
        return get_app_builder().mk_app(get_numeral_mulinv_ne_zero_of_ne_zero_ne_zero_name(), 6, {pf_num_ne_zero, pf_den_ne_zero});
    } else  {
        return get_app_builder().mk_app(get_ordered_arith_nonzero_of_pos_name(), 4, {prove_num_positive(e, type)});
    }
}

/* Testers */
bool is_mulinv(expr const & e) {
    expr arg1, arg2;
    return is_mul(e, arg1, arg2) && is_inv(arg2);
}

bool is_mulinv(expr const & e, expr & n, expr & d) {
    expr arg1, arg2, arg;
    if (is_mul(e, arg1, arg2) && is_inv(arg2, arg)) {
        n = arg1;
        d = arg;
        return true;
    } else {
        return false;
    }
}

bool is_numeral_expr(expr const & e) {
    if (is_num(e)) return true;
    expr arg, arg1, arg2;
    if (is_add(e, arg1, arg2)) return is_numeral_expr(arg1) && is_numeral_expr(arg2);
    else if (is_mul(e, arg1, arg2)) return is_numeral_expr(arg1) && is_numeral_expr(arg2);
    else if (is_neg(e, arg)) return is_numeral_expr(arg);
    else if (is_inv(e, arg)) return is_numeral_expr(arg);
    else return false;
}

/* Simplifier */
class simplify_numeral_expr_fn {
    expr m_type;
    unsigned m_count{0};

    expr compute_target(expr const & e) {
        mpq mpq_target = expr_to_mpq(e);
        if (mpq_target >= 0) return mpq_to_expr(mpq_target, m_type);
        else return get_app_builder().mk_neg(m_type, mpq_to_expr(neg(mpq_target), m_type));
    }

    void fail(expr const & e) {
        lean_trace(*g_num_trace_name, tout() << "tried to simplify non-numeral expr " << ppb(e) << "\n";);
        throw blast_exception("tried to simplify non-numeral expr", e);
    }

    expr simplify_add_core(expr const & e1, expr const & e2) {
        expr arg1, arg2, arg;
        if (is_one(e1) && is_one(e2)) {
            // 1 + 1 = 2
            return get_app_builder().mk_one_add_one(m_type);
        } else if (is_one(e1) && is_bit0(e2, arg2)) {
            // 1 + bit0 a = bit1 a
            expr_pair r = simplify(arg2);
            return get_app_builder().mk_app(get_numeral_one_add_bit0_name(), {arg2, r.first, r.second});
        } else if (is_bit0(e1, arg1) && is_one(e2)) {
            // bit0 a + 1 = bit1 a
            expr_pair r = simplify(arg1);
            return get_app_builder().mk_app(get_numeral_bit0_add_one_name(), {arg1, r.first, r.second});
        } else if (is_one(e1) && is_bit1(e2, arg2)) {
            // 1 + bit1 a = bit0 (a + 1)
            // lemma one_add_bit1 (a b : A) : 1 + a = b → 1 + bit1 a = bit0 b
            expr pf_simp = simplify_add_core(get_app_builder().mk_one(m_type), arg2);
            return get_app_builder().mk_app(get_numeral_one_add_bit1_name(), {pf_simp});
        } else if (is_bit1(e1, arg1) && is_one(e2)) {
            // bit1 a + 1 = bit1 a
            // lemma bit1_add_one (a b : A) : a + 1 = b → (bit1 a) + 1 = bit0 b
            expr pf_simp = simplify_add_core(arg1, get_app_builder().mk_one(m_type));
            return get_app_builder().mk_app(get_numeral_bit1_add_one_name(), {pf_simp});
        } else if (is_bit0(e1, arg1) && is_bit0(e2, arg2)) {
            // bit0 a + bit0 b = bit0 (a + b)
            // lemma bit0_add_bit0 [add_comm_semigroup A] (a b c : A) : a + b = c → bit0 a + bit0 b = bit0 c
            expr pf_simp = simplify_add_core(arg1, arg2);
            return get_app_builder().mk_app(get_numeral_bit0_add_bit0_name(), {pf_simp});
        } else if (is_bit0(e1, arg1) && is_bit1(e2, arg2)) {
            // bit0 a + bit1 b = bit1 (a + b)
            // lemma bit0_add_one (a b : A) : a = b → bit0 a + 1 = bit1 b
            expr pf_simp = simplify_add_core(arg1, arg2);
            return get_app_builder().mk_app(get_numeral_bit0_add_bit1_name(), {pf_simp});
        } else if (is_bit1(e1, arg1) && is_bit0(e2, arg2)) {
            // bit1 a + bit0 b = bit1 (a + b)
            // lemma bit1_add_bit0 (a b c : A) : a + b = c → bit1 a + bit0 b = bit1 c
            expr pf_simp = simplify_add_core(arg1, arg2);
            return get_app_builder().mk_app(get_numeral_bit1_add_bit0_name(), {pf_simp});
        } else if (is_bit1(e1, arg1) && is_bit1(e2, arg2)) {
            // bit1 a + bit1 b = bit1 (a + b) + 1
            // lemma bit1_add_bit1 (a b c d : A) : a + b = c → c + 1 = d → bit1 a + bit1 b = bit0 d
            expr pf_simp1 = simplify_add_core(arg1, arg2);
            expr pf_simp2 = simplify_add_core(r_sum.first, get_app_builder().mk_one(m_type);
            return get_app_builder().mk_app(get_numeral_bit1_add_bit1_name(), {pf_simp1});
        } else {
            lean_trace(*g_num_trace_name, tout() << "invalid arguments to add: " << e1 << ", " << e2 << "\n";);
            throw blast_exception("invalid arguments to add", e1);
        }
    }

    expr simplify_add(expr const & e1, expr const & e2, expr const & e_target) {
        expr_pair r1 = simplify(e1);
        expr_pair r2 = simplify(e2);
        expr const & e1_simp = r1.first;
        expr const & e2_simp = r2.first;
        expr neg_e1_simp, neg_e2_simp, neg_e_target;
        expr e1_simp_n, e1_simp_d, e2_simp_n, e2_simp_d, inv_e1_simp, inv_e2_simp;
        expr pf;
        if (is_zero(e1_simp)) {
            // 0 + a = a (a anything)
            pf = get_app_builder().mk_app(get_zero_add_name(), e2_simp);
        } else if (is_zero(e2_simp)) {
            // a + 0 = a (a anything)
            pf = get_app_builder().mk_app(get_add_zero_name(), e1_simp);
        } else if (is_neg(e1_simp, neg_e1_simp) && is_neg(e2_simp, neg_e2_simp)) {
            // -a + -b
            // lemma neg_add_neg (a b c : A) : a + b = c → -a + -b = -c
            expr simp_target; lean_verify(is_neg(e_target, simp_target));
            expr pf_of_sum_simp = simplify_add(neg_e1_simp, neg_e2_simp, simp_target).second;
            pf = get_app_builder().mk_app(get_numeral_neg_add_neg_name(), pf_of_sum_simp);
        } else if (is_neg(e1_simp, neg_e1_simp) && is_neg(e_target, neg_e_target)) {
            // -a + b = -c
            // lemma neg_add_pos_eq_neg (a b c : A) : b + c = a → -a + b = -c
            expr pf_of_sum_simp = simplify_add(e2_simp, neg_e_target, e1_simp).second;
            pf = get_app_builder().mk_app(get_numeral_neg_add_pos_eq_neg_name(), pf_of_sum_simp);
        } else if (is_neg(e1_simp, neg_e1_simp)) {
            // -a + b = c
            // lemma neg_add_pos_eq_pos (a b c : A) : a + c = b → -a + b = c
            expr pf_of_sum_simp = simplify_add(neg_e1_simp, e_target, e2_simp).second;
            pf = get_app_builder().mk_app(get_numeral_neg_add_pos_eq_pos_name(), pf_of_sum_simp);
        } else if (is_neg(e2_simp, neg_e2_simp) && is_neg(e_target, neg_e_target)) {
            // a + -b = -c
            // lemma pos_add_neg_eq_neg (a b c : A) : a + c = b → a + -b = -c
            expr pf_of_sum_simp = simplify_add(e1_simp, neg_e_target, e2_simp).second;
            pf = get_app_builder().mk_app(get_numeral_pos_add_neg_eq_neg_name(), pf_of_sum_simp);
        } else if (is_neg(e2_simp, neg_e2_simp)) {
            // a + -b = c
            // lemma pos_add_neg_eq_pos (a b c : A) : b + c = a → a + -b = c
            expr pf_of_sum_simp = simplify_add(neg_e2_simp, e_target, e1_simp).second;
            pf = get_app_builder().mk_app(get_numeral_pos_add_neg_eq_pos_name(), pf_of_sum_simp);
        } else if (is_inv(e1_simp, inv_e1_simp)) {
            // d^-1 + b
            // lemma inv_add {d b c val : A} (Hd : d ≠ 0) (H1 : 1 + b * d = val) (H2 : c * d = val) : d⁻¹ + b = c
            expr pf_ne_zero = prove_ne_zero(inv_e1_simp, m_type);
            expr_pair r_of_lhs_simp = simplify(get_app_builder().mk_add(m_type, get_app_builder().mk_one(m_type),
                                                                        get_app_builder().mk_mul(m_type, e2_simp, inv_e1_simp)));
            expr_pair r_of_rhs_simp = simplify(get_app_builder().mk_mul(m_type, e_target, inv_e1_simp));
            lean_assert(r_of_lhs_simp.first == r_of_rhs_simp.first);
            pf = get_app_builder().mk_app(get_numeral_inv_add_name(), pf_ne_zero, r_of_lhs_simp.second, r_of_rhs_simp.second);
        } else if (is_inv(e2_simp, inv_e2_simp)) {
            // b + d^-1
            // lemma add_inv {d b c val : A} (Hd : d ≠ 0) (H1 : d * b + 1 = val) (H2 : d * c = val) : b + d⁻¹ = c
            expr pf_ne_zero = prove_ne_zero(inv_e2_simp, m_type);
            expr_pair r_of_lhs_simp = simplify(get_app_builder().mk_add(m_type, get_app_builder().mk_mul(m_type, inv_e2_simp, e1_simp),
                                                                        get_app_builder().mk_one(m_type)));
            expr_pair r_of_rhs_simp = simplify(get_app_builder().mk_mul(m_type, inv_e2_simp, e_target));
            lean_assert(r_of_lhs_simp.first == r_of_rhs_simp.first);
            pf = get_app_builder().mk_app(get_numeral_add_inv_name(), pf_ne_zero, r_of_lhs_simp.second, r_of_rhs_simp.second);
        } else if (is_mulinv(e1_simp, e1_simp_n, e1_simp_d)) {
            // (a * b^-1) + c
            // lemma mulinv_add {n d b c val : A} (Hd : d ≠ 0) (H1 : n + b * d = val) (H2 : c * d = val) : n * d⁻¹ + b = c
            expr pf_ne_zero = prove_ne_zero(e1_simp_d, m_type);
            expr pf_of_lhs_simp = simplify(get_app_builder().mk_add(m_type, e1_simp_n, get_app_builder().mk_mul(m_type, e2_simp, e1_simp_d))).second;
            expr pf_of_rhs_simp = simplify(get_app_builder().mk_mul(m_type, e_target, e1_simp_d)).second;
            pf = get_app_builder().mk_app(get_numeral_mulinv_add_name(), pf_ne_zero, pf_of_lhs_simp, pf_of_rhs_simp);
        } else if (is_mulinv(e2_simp, e2_simp_n, e2_simp_d)) {
            // a + (b * c^-1)
            // lemma add_mulinv {n d b c val : A} (Hd : d ≠ 0) (H1 : d * b + n = val) (H2 : d * c = val) : b + n * d⁻¹ = c
            expr pf_ne_zero = prove_ne_zero(e2_simp_d, m_type);
            expr pf_of_lhs_simp = simplify(get_app_builder().mk_add(m_type, get_app_builder().mk_mul(m_type, e2_simp_d, e1_simp), e2_simp_n)).second;
            expr pf_of_rhs_simp = simplify(get_app_builder().mk_mul(m_type, e2_simp_d, e_target)).second;
            pf = get_app_builder().mk_app(get_numeral_add_mulinv_name(), pf_ne_zero, pf_of_lhs_simp, pf_of_rhs_simp);
        } else {
            // a + b
            pf = simplify_add_core(e1_simp, e2_simp, e_target);
        }
        return get_app_builder().mk_app(get_numeral_add_congr_name(), r1.second, r2.second, pf);
    }

    expr simplify_mul_core(expr const & e1, expr const & e2, expr const &) {
        expr arg1, arg2, arg;
        if (is_bit0(e2, arg2)) {
            // a * bit0 b
            expr_pair r = simplify(get_app_builder().mk_mul(m_type, e1, arg2));
            return get_app_builder().mk_app(get_numeral_mul_bit0_name(), {r.second});
        } else if (is_bit1(e2, arg2)) {
            // a * bit1 b
            expr_pair r1 = simplify(get_app_builder().mk_mul(m_type, e1, arg2));
            expr_pair r2 = simplify(get_app_builder().mk_add(m_type, get_app_builder().mk_bit0(m_type, r1.first), e1));
            return get_app_builder().mk_app(get_numeral_mul_bit1_name(), {r1.second, r2.second});
        } else {
            lean_trace(*g_num_trace_name, tout() << "invalid arguments to mul: " << e1 << ", " << e2 << "\n";);
            throw blast_exception("invalid arguments to mul", e1);
        }
    }

    expr simplify_mul(expr const & e1, expr const & e2, expr const & e_target) {
        expr_pair r1 = simplify(e1);
        expr_pair r2 = simplify(e2);
        expr const & e1_simp = r1.first;
        expr const & e2_simp = r2.first;
        expr neg_e1_simp, neg_e2_simp, neg_e_target;
        expr e1_simp_n, e1_simp_d, e2_simp_n, e2_simp_d, e2_simp_inv, inv_e1_simp, inv_e2_simp;
        expr e_target_n, e_target_d;
        expr pf;
        if (is_zero(e1_simp)) {
            // 0 * a = 0
            pf = get_app_builder().mk_app(get_zero_mul_name(), e2_simp);
        } else if (is_zero(e2_simp)) {
            // a + 0 = 0
            pf = get_app_builder().mk_app(get_mul_zero_name(), e1_simp);
        } else if (is_one(e1_simp)) {
            // 1 * a = a
            pf = get_app_builder().mk_app(get_one_mul_name(), e2_simp);
        } else if (is_one(e2_simp)) {
            // a * 1 = a
            pf = get_app_builder().mk_app(get_mul_one_name(), e1_simp);
        } else if (is_neg(e1_simp, neg_e1_simp) && is_neg(e2_simp, neg_e2_simp)) {
            /* -a * -b */
            expr pf_of_prod_simp = simplify(get_app_builder().mk_mul(m_type, neg_e1_simp, neg_e2_simp)).second;
            pf = get_app_builder().mk_app(get_numeral_neg_mul_neg_name(), pf_of_prod_simp);
        } else if (is_neg(e1_simp, neg_e1_simp) && !is_neg(e2_simp)) {
            /* -a * b */
            expr pf_of_prod_simp = simplify(get_app_builder().mk_mul(m_type, neg_e1_simp, e2_simp)).second;
            pf = get_app_builder().mk_app(get_numeral_neg_mul_pos_name(), pf_of_prod_simp);
        } else if (!is_neg(e1_simp) && is_neg(e2_simp, neg_e2_simp)) {
            /* a * -b */
            expr pf_of_prod_simp = simplify(get_app_builder().mk_mul(m_type, e1_simp, neg_e2_simp)).second;
            pf = get_app_builder().mk_app(get_numeral_pos_mul_neg_name(), pf_of_prod_simp);
        } else if (is_inv(e1_simp) && !is_inv(e2_simp)) {
            // a^-1 * b
            // lemma inv_mul_comm (n d v : A) (H : n * d⁻¹ = v) : d⁻¹ * n = v
            expr pf_of_comm = simplify(get_app_builder().mk_mul(m_type, e2_simp, e1_simp)).second;
            pf = get_app_builder().mk_app(get_numeral_inv_mul_comm_name(), pf_of_comm);
        } else if (!is_inv(e1_simp) && is_inv(e2_simp, inv_e2_simp) && is_mulinv(e_target, e_target_n, e_target_d)) {
            // a * b^-1 = c * d^-1
            // lemma mul_inv_eq_inv (a b c d v : A) (Hb : b ≠ 0) (Hd : d ≠ 0) (H1 : a * d = v) (H2 : c * b = v) : a * b⁻¹ = c * d⁻¹
            expr pf_ne_zero1 = prove_ne_zero(inv_e2_simp, m_type);
            expr pf_ne_zero2 = prove_ne_zero(e_target_d, m_type);
            expr pf_of_lhs_simp = simplify(get_app_builder().mk_mul(m_type, e1_simp, e_target_d)).second;
            expr pf_of_rhs_simp = simplify(get_app_builder().mk_mul(m_type, e_target_n, inv_e2_simp)).second;
            pf = get_app_builder().mk_app(get_numeral_mul_inv_eq_inv_name(), {pf_ne_zero1, pf_ne_zero2, pf_of_lhs_simp, pf_of_rhs_simp});
        } else if (!is_inv(e1_simp) && is_inv(e2_simp, inv_e2_simp) /* && !is_mulinv(e_target) */) {
            // a * b^-1 = c (not mulinv)
            // lemma mul_inv_eq_noninv (n d v : A) (Hd : d ≠ 0) (H : v * d = n) : n * d⁻¹ = v
            expr pf_ne_zero = prove_ne_zero(inv_e2_simp, m_type);
            expr pf_of_prod = simplify(get_app_builder().mk_mul(m_type, e_target, inv_e2_simp)).second;
            pf = get_app_builder().mk_app(get_numeral_mul_inv_eq_noninv_name(), pf_ne_zero, pf_of_prod);
        } else if (is_inv(e1_simp, inv_e1_simp) && is_inv(e2_simp, inv_e2_simp)) {
            // a^-1 * b^-1
            // lemma inv_mul_inv (a b c : A) (Ha : a ≠ 0) (Hb : b ≠ 0) (H : a * b = c) : a⁻¹ * b⁻¹ = c⁻¹
            expr pf_ne_zero1 = prove_ne_zero(inv_e1_simp, m_type);
            expr pf_ne_zero2 = prove_ne_zero(inv_e2_simp, m_type);
            expr pf_of_inv = simplify(get_app_builder().mk_mul(m_type, inv_e1_simp, inv_e2_simp)).second;
            pf = get_app_builder().mk_app(get_numeral_inv_mul_inv_name(), pf_ne_zero1, pf_ne_zero2, pf_of_inv);
        } else if (is_mulinv(e1_simp, e1_simp_n, e1_simp_d)) {
            // (a * b^-1) * c
            // lemma mulinv_mul {n d c v : A} (H : (n * c) * d⁻¹ = v) : (n * d⁻¹) * c = v
            expr pf_of_shuffle = simplify(get_app_builder().mk_mul(m_type, get_app_builder().mk_mul(m_type, e1_simp_n, e2_simp), get_app_builder().mk_inv(m_type, e1_simp_d))).second;
            pf = get_app_builder().mk_app(get_numeral_mulinv_mul_name(), pf_of_shuffle);
        } else if (is_mulinv(e2_simp, e2_simp_n, e2_simp_d)) {
            // a * (b * c^-1)
            // lemma mul_mulinv (c n d v : A) (Hd : d ≠ 0) (H : (c * n) * d⁻¹ = v) : c * (n * d⁻¹) = v
            expr pf_ne_zero = prove_ne_zero(e2_simp_d, m_type);
            expr pf_of_shuffle = simplify(get_app_builder().mk_mul(m_type, get_app_builder().mk_mul(m_type, e1_simp, e2_simp_n), get_app_builder().mk_inv(m_type, e2_simp_d))).second;
            pf = get_app_builder().mk_app(get_numeral_mul_mulinv_name(), {pf_ne_zero, pf_of_shuffle});
        } else if (is_inv(e2_simp, e2_simp_inv) && is_mulinv(e_target, e_target_n, e_target_d)) {
            throw exception("wasn't expecting this case");
            /* a * b^-1 = c * d^-1*/
/*            expr pf_of_lhs_simp = simplify(get_app_builder().mk_mul(m_type, e1_simp, e_target_d)).second;
            expr pf_of_rhs_simp = simplify(get_app_builder().mk_mul(m_type, e_target_n, e2_simp_inv)).second;
            pf = get_app_builder().mk_app(get_numeral_mulinv_eq_mulinv_name(), pf_of_lhs_simp, pf_of_rhs_simp);
*/
        } else {
            /* a * b */
            pf = simplify_mul_core(e1_simp, e2_simp, e_target);
        }
        return get_app_builder().mk_app(get_numeral_mul_congr_name(), r1.second, r2.second, pf);
    }

    expr simplify_neg(expr const & neg_e, expr const & e_target) {
        expr_pair r = simplify(neg_e);
        if (is_zero(e_target)) {
            return get_app_builder().mk_app(get_numeral_neg_eq_zero_name(), r.second);
        } else if (is_neg(e_target)) {
            return get_app_builder().mk_app(get_numeral_neg_eq_neg_name(), r.second);
        } else {
            return get_app_builder().mk_app(get_numeral_neg_eq_pos_name(), r.second);
        }
    }

    expr simplify_inv(expr const & inv_e, expr const & e_target) {
        expr_pair r = simplify(inv_e);
        expr inv_e_simp = r.first;
        expr inv_e_n, inv_e_d;
        expr e_target_n, e_target_d;
        expr neg_inv_e_simp;
        if (is_one(inv_e_simp)) {
            // a^1 where a = 1
            lean_assert(is_one(e_target));
            return get_app_builder().mk_app(get_numeral_inv_simp_one_name(), r.second);
        } else if (is_neg(inv_e_simp, neg_inv_e_simp)) {
            // (- a)^1
            // lemma inv_neg_eq_neg_inv (a b c : A) (Hb : -b ≠ 0) (H1 : a = -b) (H2 : b⁻¹ = c) : a⁻¹ = -c
            expr pf_ne_zero = prove_ne_zero(inv_e_simp, m_type);
            expr pf_inv_simp_simp = simplify(get_app_builder().mk_inv(m_type, neg_inv_e_simp)).second;
            return get_app_builder().mk_app(get_numeral_inv_neg_eq_neg_inv_name(), {pf_ne_zero, r.second, pf_inv_simp_simp});
        } else if (is_inv(inv_e_simp)) {
            // a^1 where a = b^1
            // lemma inv_simp_inv (a b : A) (Hb : b ≠ 0) (H : a = b⁻¹) : a⁻¹ = b
            expr pf_ne_zero = prove_ne_zero(e_target, m_type);
            return get_app_builder().mk_app(get_numeral_inv_simp_inv_name(), {pf_ne_zero, r.second});
        } else if (is_mulinv(inv_e_simp, inv_e_n, inv_e_d)) {
            // a^1 where a = b * c^-1
            // lemma inv_simp_mulinv (a b c : A) (Hb : b ≠ 0) (Hc : c ≠ 0) (H : a = c * b⁻¹) : a⁻¹ = b * c⁻¹
            lean_verify(is_mulinv(e_target, e_target_n, e_target_d));
            expr pf_ne_zero1 = prove_ne_zero(e_target_n, m_type);
            expr pf_ne_zero2 = prove_ne_zero(e_target_d, m_type);
            return get_app_builder().mk_app(get_numeral_inv_simp_mulinv_name(), {pf_ne_zero1, pf_ne_zero2, r.second});
        } else {
            /* a^1 where a = b */
            return get_app_builder().mk_app(get_numeral_inv_simp_name(), r.second);
        }
    }

    expr_pair simplify(expr const & e) {
        m_count++;
        if (is_num(e)) return mk_pair(e, get_app_builder().mk_eq_refl(e));
        expr e_target = compute_target(e);
        lean_trace(*g_num_trace_simplify_name, tout() << "simplify: " << e << " ==> " << e_target << "\n";);
        expr arg, arg1, arg2;
        expr pf;
        if (is_add(e, arg1, arg2)) {
            pf = simplify_add(arg1, arg2, e_target);
        } else if (is_mul(e, arg1, arg2)) {
            pf = simplify_mul(arg1, arg2, e_target);
        } else if (is_neg(e, arg)) {
            pf = simplify_neg(arg, e_target);
        } else if (is_inv(e, arg)) {
            pf = simplify_inv(arg, e_target);
        } else {
            fail(e);
            lean_unreachable();
        }
        return mk_pair(e_target, pf);
    }
public:
    unsigned get_count() const { return m_count; }
    expr_pair operator()(expr const & e) {
        buffer<expr> args;
        get_app_args(e, args);
        if (args.empty()) {
            fail(e);
            lean_unreachable();
        } else {
            m_type = args[0];
            return simplify(e);
        }
    }
};

/* Entry points */
simp::result simplify_numeral_expr(expr const & e) {
    // TODO(dhs): avoid the equality check
    auto c = simplify_numeral_expr_fn();
    expr_pair r = c(e);
    std::cout << c.get_count() << std::endl;
    if (r.first == e) return simp::result(e);
    else return simp::result(r.first, r.second);
}

/* Setup and teardown */
void initialize_num() {
    g_num_trace_name = new name{"blast", "num"};
    g_num_trace_simplify_name = new name{"blast", "num", "simplify"};
    register_trace_class(*g_num_trace_name);
    register_trace_class(*g_num_trace_simplify_name);
}

void finalize_num() {
    delete g_num_trace_name;
}

}}
