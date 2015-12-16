/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "library/blast/arith/polynomial.h"
#include "kernel/expr_maps.h"
#include <map>

namespace lean {
namespace blast {
namespace arith {

/* add */
void polynomial::add(polynomial p) {
    m_monomials.insert(m_monomials.end(), p.get_monomials().begin(), p.get_monomials().end());
    m_offset += p.m_offset;
}

/* mul */
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

/* fuse */
monomial monomial::cancel() const {
    std::vector<atom> new_atoms;
    std::map<expr, int, expr_quick_lt> expr_to_count;
    for (atom a : get_atoms()) {
        expr_to_count[a.get_expr()] += (a.is_inv() ? -1 : 1);
    }
    for (auto p : expr_to_count) {
        if (p.second > 0) {
            for (auto i = 0; i < p.second; i++) {
                new_atoms.emplace_back(p.first, false);
            }
        } else if (p.second < 0) {
            for (auto i = 0; i < -p.second; i++) {
                new_atoms.emplace_back(p.first, true);
            }
        }
    }
    return monomial(get_coefficient(), new_atoms);
}

void polynomial::fuse() {
    std::vector<monomial> new_monomials;
    std::map<monomial, count, monomial_quick_lt> monomial_to_coefficient;
    for (monomial m : get_monomials()) {
        monomial m_cancelled = m.cancel();
        auto it = atoms_to_numerals.find(m_cancelled(variables[i]);
        if (it != variable_to_numerals.end()) it->second = cons(numerals[i], it->second);
        else variable_to_numerals.insert({variables[i], list<expr>(numerals[i])});


    }
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
