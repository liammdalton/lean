/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include "library/blast/arith/polynomial.h"

namespace lean {
namespace blast {
namespace arith {
/* API */
polynomial simplify(expr const & e);

}}}
