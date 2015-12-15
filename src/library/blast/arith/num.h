/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include "library/num.h"

namespace lean {
namespace blast {
namespace arith {

expr mpz_to_expr(mpz const & n, expr const & A);

/* Given a positive mpz integer [n], returns a proof that [0 < (n:A)] */
expr prove_positive(mpz const & n, expr const & A);

expr prove_zero_not_lt_zero(expr const & A);
expr prove_zero_not_lt_neg(expr const & A, mpz const & nc);
expr prove_zero_not_le_neg(expr const & A, mpz const & nc);

}}}
