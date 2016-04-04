/*
Copyright (c) 2016 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Gallagher, Daniel Selsam
*/
#include <string>
#include "assert.h"
#include "kernel/kernel_exception.h"
#include "library/util.h"
#include "library/constants.h"
#include "library/quoted_expr.h"
#include "library/string.h"
#include "library/kernel_serializer.h"

namespace lean {
static name * g_quoted_expr_name = nullptr;
static std::string * g_quoted_expr_opcode = nullptr;
static macro_definition * g_quoted_expr = nullptr;

name const & get_quoted_expr_name() { return *g_quoted_expr_name; }
std::string const & get_quoted_expr_opcode() { return *g_quoted_expr_opcode; }

class quoted_expr_macro_definition_cell : public macro_definition_cell {
    void check_macro(expr const & m) const {
        if (!is_macro(m) || macro_num_args(m) != 1)
            throw exception("invalid quoted-expr, incorrect number of arguments");
    }

    expr quote_name(name const & n) const {
        if (n.is_anonymous()) {
            return mk_constant(get_name_nil_name());
        } else if (n.is_string()) {
            return mk_app(mk_constant(get_name_cons_name()), {from_string(n.get_string()), quote_name(n.get_prefix())});
        }
        lean_unreachable();
    }

    expr quote_level(level const & l) const {
        assert(false);
        return mk_var(0);
    }

    expr quote_expr(expr const & e)  const {
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
        lean_unreachable();
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
        return some_expr(quote_expr(get_quoted_expr_expr(m)));
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
