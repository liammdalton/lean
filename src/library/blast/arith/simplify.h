/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
namespace blast {

expr field_simplify(expr const & e);
expr prove_eq_field(expr const & lhs, expr const & rhs);

}}
