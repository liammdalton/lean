/*
Copyright (c) 2016 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Gallagher, Daniel Selsam
*/
#pragma once

namespace lean {
class expr;
expr mk_quoted_expr(expr const & e);
bool is_quoted_expr(expr const & e);
expr get_quoted_expr_expr(expr const & e);

void initialize_quoted_expr();
void finalize_quoted_expr();
}
