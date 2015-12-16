/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include <memory>
#include <vector>
#include "kernel/expr.h"
#include "library/expr_lt.h"
#include "util/numerics/mpq.h"

namespace lean {
namespace blast {
namespace arith {

class atom {
    expr                    m_e;
    int                     m_pow;
public:
    atom(expr const & e, int pow): m_e(e), m_pow(pow) {}
    atom(atom const & a): m_e(a.m_e), m_pow(a.m_pow) {}
    expr const & get_expr() const { return m_e; }
    int get_power() const { return m_pow; }
    void add_power(int pow) { m_pow += pow; }
};

bool operator==(atom const & a1, atom const & a2);
inline bool operator!=(atom const & a1, atom const & a2) { return !(a1 == a2); }

struct atom_quick_lt {
    bool operator()(atom const & a1, atom const & a2) const {
        // TODO(dhs): confirm that we do not need to make this a total order
        // (only used for fusing right now)
        return expr_quick_lt()(a1.get_expr(), a2.get_expr());
    }
};

class monomial {
    mpq                      m_coefficient;
    std::vector<atom>        m_atoms;
public:
    monomial(mpq const & coefficient, std::vector<atom> const & atoms):
        m_coefficient(coefficient), m_atoms(atoms) {}
    monomial(monomial const & m): m_coefficient(m.m_coefficient), m_atoms(m.m_atoms) {}

    mpq const & get_coefficient() const { return m_coefficient; }
    std::vector<atom> const & get_atoms() const { return m_atoms; }
    void add_coefficient(mpq const & coefficient) { m_coefficient += coefficient; }
    void fuse_atoms();
};

struct monomial_quick_lt {
    bool operator()(monomial const & m1, monomial const & m2) {
        std::vector<atom> const & as1 = m1.get_atoms();
        std::vector<atom> const & as2 = m2.get_atoms();
        if (as1.size() != as2.size()) {
            return as1.size() < as2.size();
        } else {
            for (unsigned i = 0; i < as1.size(); i++) {
                if (as1[i].get_expr() != as2[i].get_expr()) {
                    return expr_quick_lt()(as1[i].get_expr(), as2[i].get_expr());
                } else if (as1[i].get_power() != as2[i].get_power()) {
                    return as1[i].get_power() < as2[i].get_power();
                }
            }
        }
        return m2.get_coefficient() < m1.get_coefficient();
    }
};

class polynomial {
    mpq                      m_offset{0};
    std::vector<monomial>    m_monomials;
 public:
    polynomial() {}
    polynomial(mpq const & offset, bool inv, bool neg): m_offset(offset) {
        if (inv && !m_offset.is_zero()) m_offset.inv();
        if (neg) m_offset.neg();
    }
    polynomial(expr const & e, bool inv, bool neg) {
        std::vector<atom> atoms;
        atoms.emplace_back(e, inv ? -1 : 1);
        mpq coefficient(1);
        if (neg) coefficient.neg();
        m_monomials.emplace_back(coefficient, atoms);
    }
    polynomial(polynomial const & p): m_offset(p.m_offset), m_monomials(p.m_monomials) {}

    mpq const & get_offset() const { return m_offset; }
    std::vector<monomial> const & get_monomials() const { return m_monomials; }
    void add(polynomial p);
    void mul(polynomial p);
    void fuse_monomials();
};

std::ostream & operator<<(std::ostream & out, atom const & a);
std::ostream & operator<<(std::ostream & out, monomial const & m);
std::ostream & operator<<(std::ostream & out, polynomial const & p);

}}}
