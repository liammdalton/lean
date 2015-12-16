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
void monomial::fuse_atoms() const {
    std::sort(m_atoms.begin(), m_atoms.end(), atom_lt);
    std::vector<atom> new_atoms;
    int i = 0;
    while (i < m_atoms.size()) {
        atom a = m_atoms[i];
        while (i < m_atoms.size() && m_atoms[i+1] == m_atoms[i]) {
            i++;
            a.add_power(m_atoms[i].get_power());
        }
        new_atoms.push_back(a);
    }
    m_atoms = new_atoms;
}

polynomial polynomial::fuse_monomials() const {
    for (monomial & m : m_monomials) m.fuse_atoms();
    std::sort(m_monomials.begin(), m_monomials.end(), monomial_lt);
    std::vector<monomial> new_monomials;
    int i = 0;
    while (i < m_monomials.size()) {
        monomial m = m_monomials[i];
        while (i < m_monomials.size() && m_monomials[i+1] == m_monomials[i]) {
            i++;
            m.add_coefficient(m_monomials[i].get_coefficient());
        }
        new_monomials.push_back(m);
    }
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
