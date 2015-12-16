/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "library/blast/arith/acl.h"

namespace lean {
namespace blast {

void initialize_arith_module() {
    initialize_acl();
}

void finalize_arith_module() {
    finalize_acl();
}
}}