/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "library/blast/arith/num.h"
#include "library/blast/blast_exception.h"
#include "library/blast/blast.h"
#include "library/constants.h"

namespace lean {
namespace blast {

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
    if (n.is_integer()) {
        return mpz_to_expr(n.get_numerator(), A);
    } else {
        return get_app_builder().mk_mul(A,
                                        mpz_to_expr(n.get_numerator(), A),
                                        get_app_builder().mk_inv(A, mpz_to_expr(n.get_denominator(), A)));
    }
}

/*
  theorem pos_bit0 {A : Type} [s : linear_ordered_comm_ring A] (a : A) (H : 0 < a) : 0 < bit0 a := sorry
  theorem pos_bit1 {A : Type} [s : linear_ordered_comm_ring A] (a : A) (H : 0 < a) : 0 < bit1 a := sorry
  theorem zero_lt_one {A : Type} [s : linear_ordered_comm_ring A] : 0 < 1 := sorry
*/
pair<expr, expr> prove_positive_core(mpz const & n, expr const & A, expr const & A_linear_ordered_comm_ring) {
    lean_assert(n > 0);
    if (n == 1) {
        expr one = get_app_builder().mk_one(A);
        expr pf = get_app_builder().mk_app(get_ordered_arith_zero_lt_one_name(), {A, A_linear_ordered_comm_ring});
        return mk_pair(one, pf);
    } else if (n % mpz(2) == 1) {
        pair<expr, expr> rec = prove_positive_core(n/2, A, A_linear_ordered_comm_ring);
        expr new_num = get_app_builder().mk_bit1(A, rec.first);
        expr new_pf = get_app_builder().mk_app(get_ordered_arith_pos_bit1_name(),
                                               {A, A_linear_ordered_comm_ring, rec.first, rec.second});
        return mk_pair(new_num, new_pf);
    } else {
        pair<expr, expr> rec = prove_positive_core(n/2, A, A_linear_ordered_comm_ring);
        expr new_num = get_app_builder().mk_bit0(A, rec.first);
        expr new_pf = get_app_builder().mk_app(get_ordered_arith_pos_bit0_name(),
                                               {A, A_linear_ordered_comm_ring, rec.first, rec.second});
        return mk_pair(new_num, new_pf);
    }
}

expr prove_positive(mpz const & n, expr const & A) {
    blast_tmp_type_context tmp_tctx;
    optional<expr> A_linear_ordered_comm_ring = tmp_tctx->mk_class_instance(get_app_builder().mk_linear_ordered_comm_ring(A));
    if (!A_linear_ordered_comm_ring) throw blast_exception("Can't synthesize linear_ordered_comm_ring", A);
    return prove_positive_core(n, A, *A_linear_ordered_comm_ring).second;
}

expr prove_positive(mpq const & n, expr const & A) {
    if (n.is_integer()) {
        return prove_positive(n.get_numerator(), A);
    } else {
        expr pf_a = prove_positive(n.get_numerator(), A);
        expr pf_b = prove_positive(n.get_denominator(), A);
        return get_app_builder().mk_app(get_ordered_arith_div_pos_of_pos_name(), {pf_a, pf_b});
    }
}

/*
  theorem zero_not_lt_zero [s : linear_ordered_comm_ring A] : 0 < 0 → false := sorry
  theorem pos_not_neg [s : linear_ordered_comm_ring A] (c : A) : 0 < c → 0 < - c → false := sorry
  theorem pos_not_nonpos [s : linear_ordered_comm_ring A] (c : A) : 0 < c → 0 ≤ - c → false := sorry
*/

// TODO(dhs): clean this up, stop synthesizing and checking everywhere
expr prove_zero_not_lt_zero(expr const & A) {
    blast_tmp_type_context tmp_tctx;
    optional<expr> A_linear_ordered_comm_ring = tmp_tctx->mk_class_instance(get_app_builder().mk_linear_ordered_comm_ring(A));
    if (!A_linear_ordered_comm_ring) throw blast_exception("Can't synthesize linear_ordered_comm_ring", A);
    return mk_app(mk_constant(get_ordered_arith_zero_not_lt_zero_name(), get_level(A)),
                  {A, *A_linear_ordered_comm_ring});
}

expr prove_zero_not_lt_neg(expr const & A, mpq const & nc) {
    auto c_pos = prove_positive(neg(nc), A);
    return get_app_builder().mk_app(get_ordered_arith_zero_not_lt_neg_name(), 4, {c_pos});
}

expr prove_zero_not_le_neg(expr const & A, mpq const & nc) {
    auto c_pos = prove_positive(neg(nc), A);
    return get_app_builder().mk_app(get_ordered_arith_zero_not_le_neg_name(), 4, {c_pos});
}

}}
