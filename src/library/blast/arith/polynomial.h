/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include <memory>
#include <vector>
#include "kernel/expr.h"
#include "util/numerics/mpq.h"

namespace lean {
namespace blast {
namespace arith {

class atom {
    expr                     m_e;
    bool                     m_inv{false};
public:
    atom(expr const & e): m_e(e) {}
    atom(atom const & a): m_e(a.m_e), m_inv(a.m_inv) {}
    expr const & get_expr() const { return m_e; }
    bool is_inv() const { return m_inv; }
    void flip_inv() { m_inv = !m_inv; }
};



class monomial {
    mpq                      m_coefficient;
    std::vector<atom>        m_atoms;
    bool                     m_inv{false};
public:
    monomial(mpq const & coefficient, std::vector<atom> const & atoms):
        m_coefficient(coefficient), m_atoms(atoms) {}
    monomial(mpq const & coefficient, std::vector<atom> const & atoms, bool inv):
        m_coefficient(coefficient), m_atoms(atoms), m_inv(inv) {}
    monomial(monomial const & m): m_coefficient(m.m_coefficient), m_atoms(m.m_atoms), m_inv(m.m_inv) {}

    mpq const & get_coefficient() const { return m_coefficient; }
    std::vector<atom> const & get_atoms() const { return m_atoms; }
    std::vector<atom> & get_atoms() { return m_atoms; }
    bool is_inv() const { return m_inv; }
    void flip_inv() { m_inv = !m_inv; }
    void unset_inv() { lean_assert(m_inv); m_inv = false; }
    void push_inv();

    void push_neg();
};

class polynomial {
    mpq                      m_offset{0};
    std::vector<monomial>    m_monomials;
    bool                     m_neg{false};
    bool                     m_inv{false};
 public:
    polynomial() {}
    polynomial(mpq const & offset, bool inv): m_offset(offset) {
        if (inv && !m_offset.is_zero()) m_offset.inv();
    }
    polynomial(expr const & e, inv) {
        std::vector<atom> atoms;
        atoms.emplace_back(e, inv);
        m_monomials.emplace_back(mpq(1), atoms);
    }
    polynomial(polynomial const & p):
        m_offset(p.m_offset), m_monomials(p.m_monomials), m_neg(p.m_neg), m_inv(p.m_inv) {}

    mpq const & get_offset() const { return m_offset; }
    std::vector<monomial> const & get_monomials() const { return m_monomials; }
    std::vector<monomial> & get_monomials() { return m_monomials; }
    void add(polynomial p);
    void mul(polynomial p);
    bool is_inv() const { return m_inv; }
    void flip_inv() { m_inv = !m_inv; }
    void unset_inv() { lean_assert(m_inv); m_inv = false; }
    void push_inv();

    bool is_neg() const { return m_neg; }
    void flip_neg() { m_neg = !m_neg; }
    void unset_neg() { lean_assert(m_neg); m_neg = false; }
    void push_neg();
};

std::ostream & operator<<(std::ostream & out, atom const & a);
std::ostream & operator<<(std::ostream & out, monomial const & m);
std::ostream & operator<<(std::ostream & out, polynomial const & p);

}}}
