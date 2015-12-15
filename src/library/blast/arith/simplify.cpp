/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "library/num.h"
#include "library/blast/simplifier/simplifier.h"
#include "library/blast/arith/simplify.h"
#include "library/blast/blast.h"

namespace lean {
namespace blast {


class field_simplify_fn {
    expr m_type;

    bool is_numeral(name const & n) {
        return n == get_one_name() || n == get_zero_name() || n == get_bit0_name() || n = get_bit1_name();
    }

    bool is_arithmetic(name const & n) {
        // TODO(dhs): is [sub] always going to be reducible? How about [div]? I hope so for both.
        // TODO(dhs): power? probably all sorts of other things too
        return n == get_add_name() || n == get_mul_name() || n == get_neg_name() || n == get_inv_name();
    }

    void simplify_add_core(expr const & e, polynomial & p) {
        expr e1, e2;
        if (is_add(e, e1, e2)) {
            simplify_add_core(e1, p);
            simplify_add_core(e2, p);
        } else {
            p += simplify(e);
        }
    }

    polynomial simplify_add(expr const & e) {
        lean_assert(is_add(e));
        polynomial p;
        simplify_add_core(e, p);
        return p;
    }

    void simplify_mul_core(expr const & e, polynomial & p) {
        expr e1, e2;
        if (is_mul(e, e1, e2)) {
            simplify_mul_core(e1, p);
            simplify_mul_core(e2, p);
        } else {
            p *= simplify(e);
        }
    }

    polynomial simplify_mul(expr const & e) {
        lean_assert(is_mul(e));
        polynomial p;
        simplify_mul_core(e, p);
        return p;
    }

    polynomial simplify_neg(expr const & e) {
        polynomial arg = simplify(app_arg(e));
        arg.flip_neg();
        return arg;
    }

    polynomial simplify_inv(expr const & e) {
        polynomial arg = simplify(app_arg(e));
        arg.flip_inv();
        return arg;
    }

    polynomial simplify(expr const & e) {
        expr f = get_app_fn(e);
        if (!is_constant(f)) return mk_polynomial_term(e);
        else if (is_numeral(const_name(f))) return mk_polynomial_numeral(f);
        else if (!is_arithmetic(const_name(f))) return mk_polynomial_term(e);
        else if (const_name(f) == get_add_name()) return simplify_add(e);
        else if (const_name(f) == get_mul_name()) return simplify_mul(e);
        else if (const_name(f) == get_neg_name()) return simplify_neg(e);
        else if (const_name(f) == get_inv_name()) return simplify_inv(e);
        else throw exception("TODO(dhs): some case not handled");
    }
        buffer<expr> expr_args;
        get_app_args(e, expr_args);

        buffer<polynomial> poly_args;
        for (auto arg : args) poly_args.push_back(field_simplify(arg));


//        if

            }
public:
    polynomial operator()(expr const & e) { return simplify(e); }

};

/* Entry point */
polynomial field_simplify(expr const & e, expr const & type) {
    return field_simplify_fn(type)(e);
}

}}
