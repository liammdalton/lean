/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "library/norm_num.h"
#include "library/constants.h"
#include "library/blast/simplifier/simplifier.h"
#include "library/blast/arith/simplify.h"
#include "library/blast/blast.h"

namespace lean {
namespace blast {
namespace arith {

static bool is_numeral(name const & n) {
    return n == get_one_name() || n == get_zero_name() || n == get_bit0_name() || n == get_bit1_name();
}

static bool is_arithmetic(name const & n) {
    // TODO(dhs): is [sub] always going to be reducible? How about [div]? I hope so for both.
    // TODO(dhs): power? probably all sorts of other things too
    return n == get_add_name() || n == get_mul_name() || n == get_neg_name() || n == get_inv_name();
}

polynomial simplify(expr const & e, bool inv, bool neg);

static void simplify_add_core(expr const & e, polynomial & p, bool inv, bool neg) {
    expr e1, e2;
    if (is_add(e, e1, e2)) {
        simplify_add_core(e1, p, inv, neg);
        simplify_add_core(e2, p, inv, neg);
    } else {
        p.add(simplify(e, inv, neg));
    }
}

static polynomial simplify_add(expr const & e, bool inv, bool neg) {
    lean_assert(is_add(e));
    if (inv) {
        return polynomial(e, inv, neg);
    } else {
        polynomial p;
        simplify_add_core(e, p, inv, neg);
        return p;
    }
}

static void simplify_mul_core(expr const & e, polynomial & p, bool inv, bool neg) {
    expr e1, e2;
    if (is_mul(e, e1, e2)) {
        simplify_mul_core(e1, p, inv, neg);
        simplify_mul_core(e2, p, inv, neg);
    } else {
        p.mul(simplify(e, inv, neg));
    }
}

static polynomial simplify_mul(expr const & e, bool inv, bool neg) {
    lean_assert(is_mul(e));
    polynomial p(mpq(1), inv, neg);
    simplify_mul_core(e, p, inv, false);
    return p;
}

polynomial simplify(expr const & e, bool inv, bool neg) {
    expr f = get_app_fn(e);
    if (!is_constant(f)) {
        return polynomial(e, inv, neg);
    } else if (is_numeral(const_name(f))) {
        return polynomial(mpq_of_expr(get_type_context(), e), inv, neg);
    } else if (!is_arithmetic(const_name(f))) {
        return polynomial(e, inv, neg);
    } else if (const_name(f) == get_add_name()) {
        return simplify_add(e, inv, neg);
    } else if (const_name(f) == get_mul_name()) {
        return simplify_mul(e, inv, neg);
    } else if (const_name(f) == get_neg_name()) {
        return simplify(app_arg(e), inv, !neg);
    } else if (const_name(f) == get_inv_name()) {
        return simplify(app_arg(e), !inv, neg);
    } else {
        throw exception("TODO(dhs): some case not handled");
    }
}

/* Entry point */
polynomial simplify(expr const & e) {
    polynomial p = simplify(e, false, false);
    p.fuse_monomials();
    return p;
}

}}}
