/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "library/blast/arith/polynomial.h"

namespace lean {
namespace blast {
namespace arith {

/* add */
std::vector<monomial> add_monomials(std::vector<monomial> const & ms1, std::vector<monomial> const & ms2) {
    std::vector<monomial> new_monomials;
    int i = 0, j = 0;
    while (i < ms1.size() && j < ms2.size()) {
        monomial const & m1 = ms1[i];
        monomial const & m2 = ms2[i];
        if (monomial_is_lt(m1, m2)) {
            new_monomials.push_back(m1);
            i++;
        } else if (monomial_is_lt(m2, m1)) {
            new_monomials.push_back(m2);
            j++;
        } else {
            lean_assert(m1.get_atoms() == m2.get_atoms());
            mpz new_coefficient = m1.get_coefficient(); new_coefficient += m2.get_coefficient();
            if (!new_coefficient.is_zero()) new_monomials.emplace_back(new_coefficient, m1.get_atoms());
            i++;
            j++;
        }
    }
    return new_monomials;
}

polynomial add(polynomial p, polynomial q) {
    mpz new_offset = p.get_offset(); new_offset += q.get_offset();
    return polynomial(new_offset, add_monomials(p.get_monomials(), q.get_monomials()));
}

/* mul */
std::vector<atom> mul_atoms(std::vector<atom> const & as1, std::vector<atom> const & as2) {
    std::vector<atom> new_atoms;
    int i = 0, j = 0;
    while (i < as1.size() && j < as2.size()) {
        atom const & a1 = as1[i];
        atom const & a2 = as2[i];
        if (atom_is_lt(a1, a2)) {
            new_atoms.push_back(a1);
            i++;
        } else if (atom_is_lt(a2, a1)) {
            new_monomials.push_back(a2);
            j++;
        } else {
            lean_assert(a1.get_expr() == a2.get_expr());
            mpz new_power = a1.get_power(); new_power += m2.get_power();
            if (!new_power.is_zero()) new_atoms.emplace_back(m1.get_expr(), new_power);
            i++;
            j++;
        }
    }
    return new_atoms;
}

void polynomial::mul(polynomial p) {
    std::vector<monomial> new_monomials;
    for (monomial m1 : m_monomials) {
        mpq new_coefficient = m1.get_coefficient(); new_coefficient *= p.get_offset();
        if (!new_coefficient.is_zero()) new_monomials.emplace_back(new_coefficient, m1.get_atoms());
        for (monomial m2 : p.m_monomials) {
            mpq new_coefficient = m1.get_coefficient(); new_coefficient *= m2.get_coefficient();
            std::vector<atom> new_atoms;
            new_atoms.insert(new_atoms.end(), m1.get_atoms().begin(), m1.get_atoms().end());
            new_atoms.insert(new_atoms.end(), m2.get_atoms().begin(), m2.get_atoms().end());
            new_monomials.emplace_back(new_coefficient, new_atoms);
        }
    }
    for (monomial m2 : p.m_monomials) {
        mpq new_coefficient{m2.get_coefficient()}; new_coefficient *= get_offset();
        if (!new_coefficient.is_zero()) new_monomials.emplace_back(new_coefficient, m2.get_atoms());
    }
    m_offset *= p.get_offset();
    m_monomials = new_monomials;
}

/* Printing */
std::ostream & operator<<(std::ostream & out, atom const & a) {
    if (a.is_inv()) out << "inv(" << a.get_expr() << ")";
    else out << a.get_expr();
    return out;
}

std::ostream & operator<<(std::ostream & out, monomial const & _m) {
    monomial m = _m;
    out << "(" << m.get_coefficient() << ", ";
    bool first = true;
    for (atom const & a : m.get_atoms()) {
        if (!first) out << " * ";
        first = false;
        out << a;
    }
    out << ")";
    return out;
}

std::ostream & operator<<(std::ostream & out, polynomial const & _p) {
    polynomial p = _p;
    out << "{" << p.get_offset();
    for (monomial const & m : p.get_monomials()) {
        out << ", " << m;
    }
    out << "}";
    return out;
}
}}}
