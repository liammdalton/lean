/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once

namespace lean {
class expr;
/** \brief Create an expression definitionally equal to \c e, but it must have type \c t. */
expr mk_quoted_expr(expr const & e);
/** \brief Return true iff \c e was created using #mk_quoted_expr */
bool is_quoted_expr(expr const & e);
/** \brief Return the type of a quoted expression

    \remark get_quoted_expr_type(mk_quoted_expr(t, e)) == t
*/
expr get_quoted_expr_expr(expr const & e);

void initialize_quoted_expr();
void finalize_quoted_expr();
}
