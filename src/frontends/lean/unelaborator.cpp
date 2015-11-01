/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "frontends/lean/unelaborator.h"
#include "library/type_context.h"
#include "library/app_builder.h"

namespace lean {

expr unelaborate(environment const & env, io_state const & ios,
                 list<expr> const & ctx, expr const & e) {
    default_type_inference tc(env,ios,ctx);
    app_builder builder(tc);

    

    return e;
}








}
