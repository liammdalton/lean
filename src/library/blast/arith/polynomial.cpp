/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "library/blast/arith/polynomial.h"

namespace lean {
namespace blast {
namespace arith {

/* inv */
void monomial::push_inv() {
    if (!m_coefficient.is_zero()) m_coefficient.inv();
    for (atom & a : get_atoms()) a.flip_inv();
    flip_inv();
}

void polynomial::push_inv() {
    lean_assert(is_inv());
    std::vector<atom> new_atoms;
    for (monomial const & m : get_monomials()) {
        new_atoms.emplace_back(get_app_builder().mk_mul(m.ge
    }

    new_monomials.emplace_back(1,
    if (!m_offset.is_zero()) m_offset.inv();
    for (monomial & m : get_monomials()) m.flip_inv();
    unset_inv();
}

static void normalize_inv(polynomial & p, polynomial & q) {
    if (p.is_inv() && !q.is_inv()) p.push_inv();
    else if (!p.is_inv() && q.is_inv()) q.push_inv();
    lean_assert(p.is_inv() == q.is_inv());
}

enum class inv_undo { Undo_m1, Undo_m2, Okay };

static inv_undo normalize_inv(monomial & m1, monomial & m2) {
    if (m1.is_inv() && !m2.is_inv()) {
        m1.push_inv();
        lean_assert(m1.is_inv() == m2.is_inv());
        return inv_undo::Undo_m1;
    }
    else if (!m1.is_inv() && m2.is_inv()) {
        m2.push_inv();
        lean_assert(m1.is_inv() == m2.is_inv());
        return inv_undo::Undo_m2;
    }
    lean_assert(m1.is_inv() == m2.is_inv());
    return inv_undo::Okay;
}

/* neg */
void monomial::push_neg() { m_coefficient.neg(); }

void polynomial::push_neg() {
    lean_assert(is_neg());
    m_offset.neg();
    for (monomial & m : get_monomials()) m.push_neg();
    unset_neg();
}

static void normalize_neg(polynomial & p, polynomial & q) {
    if (p.is_neg() && !q.is_neg()) p.push_neg();
    else if (!p.is_neg() && q.is_neg()) q.push_neg();
    lean_assert(p.is_neg() == q.is_neg());
}

/* add */
void polynomial::add(polynomial p) {
    normalize_inv(*this, p);
    normalize_neg(*this, p);
    m_monomials.insert(m_monomials.end(), p.get_monomials().begin(), p.get_monomials().end());
    m_offset += p.m_offset;
}

void undo_inv(monomial & m1, monomial & m2, inv_undo undo) {
    switch (undo) {
    case inv_undo::Undo_m1: m1.push_inv(); break;
    case inv_undo::Undo_m2: m2.push_inv(); break;
    case inv_undo::Okay: break;
    }
}

/* mul */
void polynomial::mul(polynomial p) {
    normalize_inv(*this, p);
    normalize_neg(*this, p);
    std::vector<monomial> new_monomials;

    for (monomial m1 : m_monomials) {
        mpq new_coefficient = m1.get_coefficient(); new_coefficient *= p.get_offset();
        new_monomials.emplace_back(new_coefficient, m1.get_atoms(), m1.is_inv());
        for (monomial m2 : p.m_monomials) {
            inv_undo undo = normalize_inv(m1, m2);
            mpq new_coefficient = m1.get_coefficient(); new_coefficient *= m2.get_coefficient();
            std::vector<atom> new_atoms;
            new_atoms.insert(new_atoms.end(), m1.get_atoms().begin(), m1.get_atoms().end());
            new_atoms.insert(new_atoms.end(), m2.get_atoms().begin(), m2.get_atoms().end());
            new_monomials.emplace_back(new_coefficient, new_atoms, m1.is_inv());
            undo_inv(m1, m2, undo);
        }
    }
    for (monomial m2 : p.m_monomials) {
        mpq new_coefficient{m2.get_coefficient()}; new_coefficient *= get_offset();
        new_monomials.emplace_back(new_coefficient, m2.get_atoms(), m2.is_inv());
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
    if (m.is_inv()) m.push_inv();
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
    if (p.is_inv()) p.push_inv();
    if (p.is_neg()) p.push_neg();
    out << "{" << p.get_offset();
    for (monomial const & m : p.get_monomials()) {
        out << ", " << m;
    }
    out << "}";
    return out;
}

}}}
