/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include "frontends/lean/unelaborator.h"
#include "library/type_context.h"
#include "library/app_builder.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"

namespace lean {

class unelaborate_fn {
    type_context & m_tc;
    app_builder & m_builder;
    list<expr> m_ctx;

    expr unelaborate_binding(expr const & _e) {
        expr d = unelaborate(binding_domain(e));
        expr l = m_tc.mk_tmp_local(d, binding_info(e));
        flet<list<expr>> add_to_ctx(m_ctx,cons(l,m_ctx));
        expr b = abstract(unelaborate(instantiate(binding_body(e), l)), l);
        return update_binding(e, d, b);
    }
    
    expr unelaborate_app(expr const & e) {
        buffer<expr> _args;
        expr const & _f = get_app_args(e, args);

        expr f = unelaborate(_f);
        
        buffer<expr> args;
        for (int i = 0; i < _args.size(); i++) {
            args.push_back(unelaborate(_args[i]));
        }

        if (!is_constant(f)) return mk_app(f,args);

        expr f_type = m_tc.infer(f);

        buffer<bool> explicit_mask;
        buffer<bool> explicit_or_ho_mask;

        expr f_ = f;
        while (is_pi(f_)) {
            explicit_mask.push_back(is_explicit(binding_info(f_)));
            explicit_or_ho_mask.push_back(explicit_mask.back() || is_pi(m_tc.whnf(binding_domain(f_))));
            f_ = binding_body(f_);
        }

        expr actual = mk_app(f,args);

        buffer<expr> explicit_args;
        buffer<expr> explicit_or_ho_args;        
        for (int i = 0; i < args.size(); i++) {
            if (explicit_mask[i]) explicit_args.push_back(args[i]);
            if (explicit_or_ho_mask[i]) explicit_or_ho_args.push_back(args[i]);
            
        }
        
        /* (1) First we try only passing explicits. */
        auto r_explicit = m_builder.mk_app(f,explicit_args.size(),explicit_args.data(),true,explicit_mask);

        /* We are able to reconstruct the expression exactly while only looking 
           at the explicit arguments. Thus we return the expression without any
           additional annotation. */
        if (r_explicit && *r_explicit = actual) return actual;
        
        /* (2) Next we try only passing explicits and higher-order implicits. */
        auto r_explicit_or_ho = m_builder.mk_app(f,explicit_or_ho_args.size(),
                                                 explicit_or_ho_args.data(),true,explicit_or_ho_mask);

        /* We are able to reconstruct the expression exactly while only looking 
           at the explicit arguments and the higher-order implicit arguments.
           We annotate the expression with '@@' to indicate this to the pretty printer. */
        if (r_explicit_or_ho && *r_explicit_or_ho = actual) return mk_partial_explicit(actual);

        /* (3) We need to pass first-order implicit arguments as well. We annotate the expression with
           '@' to indicate this to the pretty printer. We can make the unelaboration more precise
           in the future by allowing [app_builder] to take a mask, and searching for implicit arguments
           that we can print as underscores. */
        return mk_explicit(actual);
    }
    
    expr unelaborate(expr const & e) {
        switch (e.kind()) {
        case expr_kind::Meta:
            throw exception("unelaborator only supports fully elaborated terms");
            lean_unreachable();  // LCOV_EXCL_LINE
        case expr_kind::Var:
            lean_unreachable();  // LCOV_EXCL_LINE
        case expr_kind::Macro:
            // TODO we may need to support macros
            throw exception("unelaborator does not support macros");
        case expr_kind::Local: 
        case expr_kind::Sort:
        case expr_kind::Constant:
            return e
        case expr_kind::Lambda: 
        case expr_kind::Pi:
            return unelaborate_binding(e);
        case expr_kind::App:
            return unelaborate_app(e);
        }
        lean_unreachable();  // LCOV_EXCL_LINE    
    }

public:
    unelaborator(type_context const & tc, app_builder const & builder, list<expr> const & ctx):
        m_tc(tc), m_builder(builder), m_ctx(ctx) {}

    expr operator()(expr const & e) { return unelaborate(e); }
};
    

expr unelaborate(environment const & env, io_state const & ios,
                 list<expr> const & ctx, expr const & e) {
    default_type_context tc(env,ios,ctx);
    app_builder builder(tc);
    return unelaborate_fn unelaborator(tc,builder,ctx)(e);
}


}
