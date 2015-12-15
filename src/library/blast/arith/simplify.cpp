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

static void simplify_add_core(expr const & e, polynomial & p) {
    expr e1, e2;
    if (is_add(e, e1, e2)) {
        simplify_add_core(e1, p);
        simplify_add_core(e2, p);
    } else {
        p.add(simplify(e));
    }
}

static polynomial simplify_add(expr const & e) {
    lean_assert(is_add(e));
    polynomial p;
    simplify_add_core(e, p);
    return p;
}

static void simplify_mul_core(expr const & e, polynomial & p) {
    expr e1, e2;
    if (is_mul(e, e1, e2)) {
        simplify_mul_core(e1, p);
        simplify_mul_core(e2, p);
    } else {
        p.mul(simplify(e));
    }
}

static polynomial simplify_mul(expr const & e) {
    lean_assert(is_mul(e));
    polynomial p;
    simplify_mul_core(e, p);
    return p;
}

static polynomial simplify_neg(expr const & e) {
    polynomial arg = simplify(app_arg(e));
    arg.flip_neg();
    return arg;
}

static polynomial simplify_inv(expr const & e) {
    polynomial arg = simplify(app_arg(e));
    arg.flip_inv();
    return arg;
}

/* Entry point */
polynomial simplify(expr const & e) {
    expr f = get_app_fn(e);
    if (!is_constant(f)) return polynomial(e);
    else if (is_numeral(const_name(f))) return polynomial(mpq_of_expr(get_type_context(), e));
    else if (!is_arithmetic(const_name(f))) return polynomial(e);
    else if (const_name(f) == get_add_name()) return simplify_add(e);
    else if (const_name(f) == get_mul_name()) return simplify_mul(e);
    else if (const_name(f) == get_neg_name()) return simplify_neg(e);
    else if (const_name(f) == get_inv_name()) return simplify_inv(e);
    else throw exception("TODO(dhs): some case not handled");
}
}}}
