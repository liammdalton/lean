/*
  Copyright (c) 2015 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Leonardo de Moura
*/
#include <unordered_map>
#include "kernel/expr_maps.h"
#include "kernel/for_each_fn.h"
#include "kernel/instantiate.h"
#include "kernel/inductive/inductive.h"
#include "kernel/quotient/quotient.h"
#include "kernel/replace_fn.h"
#include "library/max_sharing.h"
#include "library/module.h"
#include "library/unfold_macros.h"
#include "library/reducible.h"


namespace lean {
template<typename T>
using level_map = typename std::unordered_map<level, T, level_hash, level_eq>;

template<typename T>
using name_hmap = typename std::unordered_map<name, T, name_hash, name_eq>;



class exporter {
    std::ostream &        m_out;
    environment           m_env;
    bool                  m_all;
    name_set              m_exported;
    max_sharing_fn        m_max_sharing;
    name_hmap<unsigned>   m_name2idx;
    level_map<unsigned>   m_level2idx;
    expr_map<unsigned>    m_expr2idx;

    class dependency_exporter {
        std::ostream & m_out;
        environment           m_env;
        std::unordered_set<unsigned> m_saw;
        exporter & m_ex;

        void acc_dependencies(const expr & e) {
            declaration d;
            switch (e.kind()) {
            case expr_kind::Var: break;
            case expr_kind::Sort: return;
            case expr_kind::Constant:
                d    = m_env.get(const_name(e));
                if (d.is_theorem()) {
                    m_saw.insert(m_ex.export_name(const_name(e)));
                }
                break;
            case expr_kind::App:
                acc_dependencies(app_fn(e));
                acc_dependencies(app_arg(e));
                break;
            case expr_kind::Lambda:
            case expr_kind::Pi:            
                acc_dependencies(binding_domain(e));
                acc_dependencies(binding_body(e));
                break;
            case expr_kind::Meta:
                throw exception("invalid 'export', proof contains Meta");
                break;
            case expr_kind::Local:
                throw exception("invalid 'export', proof contains Local expression type");
                break;
            case expr_kind::Macro:
                throw exception("invalid 'export', proof contains illegal expression type");
                break;

            }
        }

        void output_dependencies() {
            for (auto & i : m_saw) {
                m_out << " " << i;
            }
        }


    public:
        dependency_exporter(std::ostream & out, environment env, exporter & ex):
            m_out(out), m_env(env), m_saw(), m_ex(ex) {}

        void export_lemma_dependencies(const expr & e) {
            declaration d;
            switch (e.kind()) {
            case expr_kind::Var:
                break;
            case expr_kind::Sort: break;
            case expr_kind::Constant:
                d    = m_env.get(const_name(e));
                if (d.is_theorem()) {
                    m_ex.export_definition(d);
                }
                break;
            case expr_kind::App:
                export_lemma_dependencies(app_fn(e));
                export_lemma_dependencies(app_arg(e));
                break;
            case expr_kind::Lambda:
            case expr_kind::Pi:            
                export_lemma_dependencies(binding_domain(e));
                export_lemma_dependencies(binding_body(e));
                break;
            case expr_kind::Meta:
            case expr_kind::Local:
            case expr_kind::Macro:
                throw exception("invalid 'export', proof contains illegal expression type");
                break;
            }
        }

        void export_proof_dependencies(const expr & e) {
            acc_dependencies(e);
            output_dependencies();
        }

    };
    

    void mark(name const & n) {
        m_exported.insert(n);
    }

    bool already_exported(name const & n) {
        return m_exported.contains(n);
    }



    unsigned export_name(name const & n) {
        auto it = m_name2idx.find(n);
        if (it != m_name2idx.end())
            return it->second;
        unsigned i;
        if (n.is_anonymous()) {
            lean_unreachable();
        } else if (n.is_string()) {
            unsigned p = export_name(n.get_prefix());
            i = m_name2idx.size();
            m_out << i << " #NS " << p << " " << n.get_string() << "\n";
        } else {
            unsigned p = export_name(n.get_prefix());
            i = m_name2idx.size();
            m_out << i << " #NI " << p << " " << n.get_numeral() << "\n";
        }
        m_name2idx.insert(mk_pair(n, i));
        return i;
    }

    unsigned export_level(level const & l) {
        auto it = m_level2idx.find(l);
        if (it != m_level2idx.end())
            return it->second;
        unsigned i = 0;
        unsigned l1, l2, n;
        switch (l.kind()) {
        case level_kind::Zero:
            lean_unreachable();
            break;
        case level_kind::Succ:
            l1 = export_level(succ_of(l));
            i  = m_level2idx.size();
            m_out << i << " #US " << l1 << "\n";
            break;
        case level_kind::Max:
            l1 = export_level(max_lhs(l));
            l2 = export_level(max_rhs(l));
            i  = m_level2idx.size();
            m_out << i << " #UM " << l1 << " " << l2 << "\n";
            break;
        case level_kind::IMax:
            l1 = export_level(imax_lhs(l));
            l2 = export_level(imax_rhs(l));
            i  = m_level2idx.size();
            m_out << i << " #UIM " << l1 << " " << l2 << "\n";
            break;
        case level_kind::Param:
            n = export_name(param_id(l));
            i = m_level2idx.size();
            m_out << i << " #UP " << n << "\n";
            break;
        case level_kind::Global:
            n = export_name(global_id(l));
            i = m_level2idx.size();
            m_out << i << " #UG " << n << "\n";
            break;
        case level_kind::Meta:
            throw exception("invalid 'export', universe meta-variables cannot be exported");
        }
        m_level2idx.insert(mk_pair(l, i));
        return i;
    }

    unsigned export_binding(expr const & e, char const * k) {
        unsigned e1 = export_expr(binding_domain(e));
        unsigned n = export_name(binding_name(e));

        expr l = mk_local(name(), binding_name(e), binding_domain(e), binding_info(e));        
        unsigned e2 = export_expr(instantiate(binding_body(e), l));
        unsigned i  = m_expr2idx.size();
        m_out << i << " " << k << " ";
        m_out << n << " ";
        m_out << e1 << " " << e2 << "\n";
        return i;
    }

    unsigned export_const(expr const & e) {
        buffer<unsigned> ls;
        unsigned n = export_name(const_name(e));
        unsigned i  = m_expr2idx.size();
        m_out << i << " #EC " << n;
        m_out << "\n";
        return i;
    }

    unsigned export_expr(expr const & e) {
        auto it = m_expr2idx.find(e);
        if (it != m_expr2idx.end())
            return it->second;
        unsigned i = 0;
        unsigned l, e1, e2;
        switch (e.kind()) {
        case expr_kind::Local:
            i = m_expr2idx.size();
            m_out << i << " #ET ";
            i = export_name(mlocal_name(e));
            e1 = export_expr(mlocal_type(e));
            m_out << i << " " << e1 << "\n";
            break;
        case expr_kind::Sort:
            l = export_level(normalize(sort_level(e)));
            i = m_expr2idx.size();
            m_out << i << " #ES " << l << "\n";
            break;
        case expr_kind::Constant:
            i = export_const(e);
            break;
        case expr_kind::App:
            e1 = export_expr(app_fn(e));
            e2 = export_expr(app_arg(e));
            i  = m_expr2idx.size();
            m_out << i << " #EA " << e1 << " " << e2 << "\n";
            break;
        case expr_kind::Lambda:
            i  = export_binding(e, "#EL");
            break;
        case expr_kind::Pi:
            i  = export_binding(e, "#EP");
            break;
        case expr_kind::Meta:
            throw exception("invalid 'export', meta-variables cannot be exported");
        case expr_kind::Var:
            throw exception("invalid 'export', variables cannot be exported");
        case expr_kind::Macro:
            throw exception("invalid 'export', macros cannot be exported");
        }
        m_expr2idx.insert(mk_pair(e, i));
        return i;
    }

    unsigned export_root_expr(expr const & e) {
        return export_expr(m_max_sharing(unfold_all_macros(m_env, e)));
    }

    void export_dependencies(expr const & e) {
        for_each(e, [&](expr const & e, unsigned) {
                if (is_constant(e)) {
                    name const & n = const_name(e);
                    export_declaration(n);
                }
                return true;
            });
    }

    void export_definition(declaration const & d) {
        if (already_exported(d.get_name()))
            return;
        
        mark(d.get_name());
        unsigned n = export_name(d.get_name());
        buffer<unsigned> ps;

        if (d.is_theorem()) {
            if (m_all) {
                export_dependencies(d.get_type());
            }
            const expr & proof = unfold_all_macros(m_env,d.get_value());
            dependency_exporter(m_out,m_env,*this).export_lemma_dependencies(proof);
            unsigned t = export_root_expr(d.get_type());
            m_out << "#LEM " << n << " " << t << " ";
            dependency_exporter(m_out,m_env,*this).export_proof_dependencies(proof);
            m_out << "\n";
        }
        // TODO handle these cases together, and just print out the reducibility status as well
        else {
            std::string status;
            switch (get_reducible_status(m_env,d.get_name())) {
            case reducible_status::Reducible: status = "R"; break;
            case reducible_status::Quasireducible: status = "Q"; break;
            case reducible_status::Semireducible: status = "S"; break;
            case reducible_status::Irreducible: status = "I"; break;
            }

            if (m_all) {
                export_dependencies(d.get_value());
            }
            unsigned v = export_root_expr(d.get_value());
            m_out << "#DEF " << status << " " << n << " " << v << "\n";
        }
    }

    void export_axiom(declaration const & d) {
        if (already_exported(d.get_name())) return;
        mark(d.get_name());
        unsigned n = export_name(d.get_name());

        if (m_all) export_dependencies(d.get_type());

        if (inductive::is_intro_rule(m_env, d.get_name())) {
            unsigned t = export_root_expr(d.get_type());
            m_out << "#CON " << n << " " << t << "\n";
        }
        else if (inductive::is_elim_rule(m_env, d.get_name())) {
            unsigned t = export_root_expr(d.get_type());
            m_out << "#REC " << n << " " << t << "\n";
        }
        else if (is_quotient_decl(m_env,d.get_name())) {
            int quot_id = -1;
            if (d.get_name() == name{"quot"}) quot_id = 1;
            else if (d.get_name() == name{"quot", "lift"}) quot_id = 2;
            else if (d.get_name() == name{"quot", "ind"}) quot_id = 3;
            else if (d.get_name() == name{"quot", "mk"}) quot_id = 4;
            else if (d.get_name() == name{"quot", "sound"}) quot_id = 5;
            else {
                lean_assert(false);
            }
            unsigned t = export_root_expr(d.get_type());
            m_out << "#QUOT " << n << " " << quot_id << " " << t << "\n";
        }
        else {
            unsigned t = export_root_expr(d.get_type());
            m_out << "#AX " << n << " " << t << "\n";
        }
    }

    void export_inductive(name const & n) {
        if (already_exported(n))
            return;
        mark(n);
        std::tuple<level_param_names, unsigned, list<inductive::inductive_decl>> decls =
            *inductive::is_inductive_decl(m_env, n);
        if (m_all) {
            for (inductive::inductive_decl const & d : std::get<2>(decls)) {
                export_dependencies(inductive::inductive_decl_type(d));
                for (inductive::intro_rule const & c : inductive::inductive_decl_intros(d)) {
                    export_dependencies(inductive::intro_rule_type(c));
                }
            }
        }
        for (inductive::inductive_decl const & d : std::get<2>(decls)) {
            export_name(inductive::inductive_decl_name(d));
            export_root_expr(inductive::inductive_decl_type(d));
            for (inductive::intro_rule const & c : inductive::inductive_decl_intros(d)) {
                expr cty_start = inductive::intro_rule_type(c);
                expr cty = replace(cty_start,
                                   [=](expr const & e, unsigned offset) -> optional<expr> {
                                       switch (e.kind()) {
                                       case expr_kind::Constant:
                                           if (const_name(e) == inductive::inductive_decl_name(d)) {
                                               return some_expr(mk_constant(string_to_name("#INDNAME"),const_levels(e)));
                                           }
                                       default:
                                           return none_expr();
                                       }
                                   });
                export_root_expr(cty);
            }
        }
        for (inductive::inductive_decl const & d : std::get<2>(decls)) {
            m_out << "#INDTYPE " << export_name(inductive::inductive_decl_name(d)) << " "
                  << export_root_expr(inductive::inductive_decl_type(d)) << " ";

            // TODO pointlessly repeated
            for (inductive::intro_rule const & c : inductive::inductive_decl_intros(d)) {
                expr cty_start = inductive::intro_rule_type(c);
                expr cty = replace(cty_start,
                                   [=](expr const & e, unsigned offset) -> optional<expr> {
                                       switch (e.kind()) {
                                       case expr_kind::Constant:
                                           if (const_name(e) == inductive::inductive_decl_name(d)) {
                                               return some_expr(mk_constant("#INDNAME",const_levels(e)));
                                           }
                                       default:
                                           return none_expr();
                                       }
                                   });
                    m_out << export_root_expr(cty) << " ";
            }
        }
        m_out << "\n";
    }

    void export_declaration(name const & n) {
        if (inductive::is_inductive_decl(m_env, n)) {
            export_inductive(n);
        } else {
            declaration const & d = m_env.get(n);
            if (d.is_definition())
                export_definition(d);
            else
                export_axiom(d);
        }
    }

    void export_declarations() {
        if (m_all) {
            m_env.for_each_declaration([&](declaration const & d) {
                    if (d.is_theorem() || !d.is_definition()) {
                        export_declaration(d.get_name());
                    }
                });
        } else {
            buffer<name> ns;
            to_buffer(get_curr_module_decl_names(m_env), ns);
            std::reverse(ns.begin(), ns.end());
            for (name const & n : ns) {
                export_declaration(n);
            }
        }
    }

    void export_direct_imports() {
        if (!m_all) {
            buffer<module_name> imports;
            to_buffer(get_curr_module_imports(m_env), imports);
            std::reverse(imports.begin(), imports.end());
            for (module_name const & m : imports) {
                unsigned n = export_name(m.get_name());
                if (m.is_relative()) {
                    m_out << "#RI " << *m.get_k() << " " << n << "\n";
                } else {
                    m_out << "#DI " << n << "\n";
                }
            }
        }
    }

    void export_global_universes() {
        if (m_all) {
            m_env.for_each_universe([&](name const & u) {
                    unsigned n = export_name(u);
                    m_out << "#UNI " << n << "\n";
                });
        } else {
            buffer<name> ns;
            to_buffer(get_curr_module_univ_names(m_env), ns);
            std::reverse(ns.begin(), ns.end());
            for (name const & u : ns) {
                unsigned n = export_name(u);
                m_out << "#UNI " << n << "\n";
            }
        }
    }

public:
    exporter(std::ostream & out, environment const & env, bool all):m_out(out), m_env(env), m_all(all) {}

    void operator()() {
        m_name2idx.insert(mk_pair(name(), 0));
        m_level2idx.insert(mk_pair(level(), 0));
        export_direct_imports();
        export_global_universes();
        export_declarations();
    }
};



void export_module_as_lowtext(std::ostream & out, environment const & env) {
    exporter(out, env, false)();
}

void export_all_as_lowtext(std::ostream & out, environment const & env) {
    exporter(out, env, true)();
}
}
