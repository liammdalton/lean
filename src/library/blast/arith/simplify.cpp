/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "library/blast/simplifier/simplifier.h"
#include "library/blast/arith/simplify.h"
#include "library/blast/blast.h"

namespace lean {
namespace blast {

/* Monomials */
class monomial {
    mpz      m_coeff;
    expr     m_unknown;
public:
    monomial(mpz const & coeff, expr const & unknown): m_coeff(coeff), m_unknown(unknown) {}
    mpz const & get_coeff() const { return m_coeff; }
    expr const & get_unknown() const { return m_unknown; }
};
/*
struct monomial_lt {
    // TODO(dhs): we may need to compare the coefficients if the expressions are the same
    bool operator()(monomial const & m1, monomial const & m2) const {
        return m1.get_unknown() < m2.get_unknown();
    }
};

bool is_lt(monomial const & m1, monomial const & m2) {
    return monomial_lt()(m1, m2);
}
*/
/* Polynomials */
class polynomial {
    expr m_type;
    buffer<monomial> m_monomials;
    mpz m_offset;
public:
    polynomial(expr const & type, buffer<monomial> const & monomials, mpz const & offset):
        m_type(type), m_monomials(monomials), m_offset(offset) {}
    expr const & get_type() const { return m_type; }
    buffer<monomial> const & get_monomials() const { return m_monomials; }
    mpz const & get_offset() const { return m_offset; }
};

class field_simplify_fn {
    bool m_proof{false};
    simp::result field_simplify_core(expr const & e);

public:
    simp::result operator()(expr const & e, bool proof) {
        m_proof = proof;
        return field_simplify_core(e);
    }
};

simp::result field_simplify_fn::field_simplify_core(expr const & e) {
    // TODO(dhs): implement!
    throw exception("TODO(dhs): field_simplify_fn::field_simplify_core");
    return simp::result(e);
}

/* Entry points */
expr field_simplify(expr const & e) { return field_simplify_fn()(e, false).get_new(); }
expr prove_eq_field(expr const & lhs, expr const & rhs) {
    simp::result r_lhs = field_simplify_fn()(lhs, true);
    simp::result r_rhs = field_simplify_fn()(rhs, true);
    lean_assert(r_lhs.get_new() == r_rhs.get_new());
    if (r_lhs.has_proof() && r_rhs.has_proof()) {
        return get_app_builder().mk_eq_trans(r_lhs.get_proof(), get_app_builder().mk_eq_symm(r_rhs.get_proof()));
    } else if (r_lhs.has_proof()) {
        return r_lhs.get_proof();
    } else if (r_rhs.has_proof()) {
        return r_rhs.get_proof();
    } else {
        return get_app_builder().mk_eq_refl(lhs);
    }
}
}}
