/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "kernel/kernel_exception.h"
#include "library/util.h"
#include "library/constants.h"
#include "library/kernel_serializer.h"

namespace lean {
static name * g_quoted_expr_name = nullptr;
static std::string * g_quoted_expr_opcode = nullptr;
static macro_definition * g_quoted_expr = nullptr;

name const & get_quoted_expr_name() { return *g_quoted_expr_name; }
std::string const & get_quoted_expr_opcode() { return *g_quoted_expr_opcode; }

/** \brief This macro is used to "enforce" a given type to an expression.
    It is equivalent to

        definition quoted_expr (A : Type) (a : A) := a

    We use a macro instead of the definition because we want to be able
    to use in any environment, even one that does not contain the
    definition such as quoted_expr.

    The macro is also slightly for efficient because we don't need a
    universe parameter.
*/
class quoted_expr_macro_definition_cell : public macro_definition_cell {
    void check_macro(expr const & m) const {
        if (!is_macro(m) || macro_num_args(m) != 1)
            throw exception("invalid quoted-expr, incorrect number of arguments");
    }

    expr quote_bool(bool b) {
        return mk_constant(b ? get_bool_tt_name() : get_bool_ff_name());
    }

    expr quote_char(char c) { 
        expr r_c = quote_bool(c & 1);
        for (int i = 1; i < 8; ++i) {
            r_c = mk_app(r_c, quote_bool(c & (1 << i)));
        }
        return r_c;
    }

    expr quote_string(string const & s) {
        expr r_s = mk_constant(get_string_empty_name());
        for (char c : s.data()) {
            r_s = mk_app(mk_constant(get_string_str_name()), {quote_char(c), r_s});
        }
        return r_s;
    }

    expr quote_name(name const & n) {
        if (n.is_anonymous()) {
            return mk_constant(get_name_nil_name());
        } else if (n.is_string()) {
            return mk_app(mk_constant(get_name_cons_name()), 
                          {quote_string(n.get_string()), quote_name(n.get_prefix())});
        }
        lean_unreachable();
    }

    expr quote_level(level const & l) {
        assert(false);
        return mk_var(0);
    }

    expr quote_expr(expr const & e) {
        expr r_id;
        switch (e.kind()) {
        case expr_kind::Local: lean_unreachable();  // LCOV_EXCL_LINE
        case expr_kind::Meta:  lean_unreachable();  // LCOV_EXCL_LINE
        case expr_kind::Var: assert(false); break;
        case expr_kind::Sort: assert(false); break;
        case expr_kind::Constant:
            r_id = quote_name(const_name(e));
            return mk_app(mk_constant(get_expr_const_name()), r_id);
        case expr_kind::Macro: assert(false); break;
        case expr_kind::Lambda: assert(false); break;
        case expr_kind::Pi: assert(false); break;
        case expr_kind::App: assert(false); break;
        case expr_kind::Let: assert(false); break;
        }
    }



public:
    virtual name get_name() const { return get_quoted_expr_name(); }
    virtual pair<expr, constraint_seq> check_type(expr const & m, extension_context & ctx, bool infer_only) const {
        constraint_seq cseq;
        check_macro(m);
        return mk_pair(mk_constant(get_expr_name()), cseq);
    }
    virtual optional<expr> expand(expr const & m, extension_context &) const {
        check_macro(m);
        return quote_expr(get_quoted_expr_expr(m));
    }
    virtual void write(serializer & s) const {
        s.write_string(get_quoted_expr_opcode());
    }
};

bool is_quoted_expr(expr const & e) {
    return is_macro(e) && macro_def(e) == *g_quoted_expr;
}

expr mk_quoted_expr(expr const & v) {
    expr args[1] = {v};
    return mk_macro(*g_quoted_expr, 1, args);
}

expr get_quoted_expr_expr(expr const & e) { lean_assert(is_quoted_expr(e)); return macro_arg(e, 0); }


void initialize_quoted_expr() {
    g_quoted_expr_name = new name("quoted_expr");
    g_quoted_expr_opcode = new std::string("QuoteE");
    g_quoted_expr = new macro_definition(new quoted_expr_macro_definition_cell());
    register_macro_deserializer(*g_quoted_expr_opcode,
                                [](deserializer &, unsigned num, expr const * args) {
                                    if (num != 1)
                                        throw corrupted_stream_exception();
                                    return mk_quoted_expr(args[0]);
                                });
}

void finalize_quoted_expr() {
    delete g_quoted_expr;
    delete g_quoted_expr_opcode;
    delete g_quoted_expr_name;
}
}
