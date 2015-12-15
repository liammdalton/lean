/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include <memory>
#include "kernel/expr.h"

namespace lean {
namespace blast {

enum class polynomial_kind { Term, Numeral, Monomial, Sum };
class polynomial_cell {
protected:
    polynomial_kind    m_kind;
    bool               m_neg{false};
    bool               m_inv{false};
public:
    polynomial_cell(polynomial_kind kind): m_kind(kind) {}
    void flip_neg() { m_neg = !m_neg; }
    void flip_inv() { m_inv = !m_inv; }
};

class polynomial {
    // TODO(dhs): switch to reference counting once we have MK_BLAST_RC
    std::shared_ptr<polynomial_cell> m_ptr;
public:
    polynomial(polynomial_cell * ptr): m_ptr(ptr) {}
};

class polynomial_leaf : public polynomial_cell {};

class polynomial_term : public polynomial_leaf {
    expr m_term;
public:
    polynomial_term(expr const & term, bool inv): polynomial_cell(polynomial_kind::Term), m_term(term), m_inv(inv) {}
    expr const & get_term() const { return m_term; }
};

class polynomial_numeral : public polynomial_leaf {
    mpz m_numeral;
public:
    polynomial_numeral(mpz const & numeral): polynomial_cell(polynomial_kind::Numeral), m_numeral(numeral) {}
    mpz const & get_numeral() const { return m_numeral; }
};

class polynomial_monomial : public polynomial_cell {
    polynomial_numeral m_coefficient;
    polynomial_term    m_term;
public:
    polynomial_monomial(mpz const & coefficient, expr const & term):
        polynomial_cell(polynomial_kind::Monomial), m_coefficient(coefficient), m_term(term) {}
    mpz const & get_coefficient() const { return m_coefficient; }
    mpz const & get_term() const { return m_term; }
};

class polynomial_sum : public polynomial_cell {
    buffer<polynomial_monomial> m_monomials;
    polynomial_numeral          m_offset;
public:
    polynomial_sum(): polynomial_cell(polynomial_kind::Sum) {}
    // TODO(dhs): need [add] and [mul]
    buffer<polynomial_monomial> const & get_monomials() const { return m_monomials; }
    polynomial_numeral const & get_offset() constn { return m_offset; }
};

polynomial mk_numeral(expr const & n) {
    return polynomial(new polynomial_numeral(num_of_expr(get_type_context(), n)));
}

polynomial mk_term(expr const & e) {
    return polynomial(new polynomial_term(e));
}

polynomial mk_monomial(polynomial_numeral const & coefficient, polynomial_term const & term) {
    return polynomial(new polynomial_monomial(coefficient, term));
}

polynomial mk_polynomial() {
    return polynomial(new polynomial_sum());
}

polynomial field_simplify(expr const & e, expr const & type);

}}
