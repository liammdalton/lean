#include "library/blast/blast_serializer.h"
#include "library/kernel_serializer.h"
#include "kernel/expr.h"
#include "kernel/environment.h"
#include "kernel/declaration.h"

#include "kernel/inductive/inductive.h"
#include "util/debug.h"
#include <utility>
#include <assert.h>

namespace lean {

using inductive::is_inductive_decl;
using inductive::inductive_decl;
using inductive::inductive_decls;
using inductive::inductive_decl_intros;

using inductive::is_intro_rule;
using inductive::intro_rule;
using inductive::intro_rule_type;

using inductive::is_elim_rule;

bool is_quot_assumption(declaration const & d) { 
    return d.get_name() == name{"quot"} 
    || d.get_name () == name{"quot", "lift"}
    || d.get_name () == name{"quot", "ind"}
    || d.get_name () == name{"quot", "mk"}
    || d.get_name () == name{"quot", "sound"};
}

int reducible_status_to_int(reducible_status status) {
    switch (status) {
    case reducible_status::Reducible: return 1;
    case reducible_status::Quasireducible: return 2;
    case reducible_status::Semireducible: return 3;
    case reducible_status::Irreducible: return 4;
    }
    lean_unreachable();
}

bool in_prop(declaration const & d) { return d.is_axiom() || d.is_theorem(); }

void write_export_declaration(serializer & s, environment const & env, declaration const & d) {
    optional<inductive_decls> idecls = is_inductive_decl(env,d.get_name());
    optional<name> ir_name = is_intro_rule(env,d.get_name());
    optional<name> er_name = is_elim_rule(env,d.get_name());

    s << bool(idecls) 
      << bool(ir_name) 
      << bool(er_name)
      << is_quot_assumption(d)
      << in_prop(d)
      << reducible_status_to_int(get_reducible_status(env,d.get_name()))
      << d.get_name() 
      << d.get_type() 
      << d.is_definition();

    if (d.is_definition()) { s << d.get_value(); }
    if (idecls) { 
        /* Not currently handling mutually inductive types */
        assert(length(std::get<2>(*idecls)) == 1); 
        inductive_decl idecl = head(std::get<2>(*idecls));
        list<intro_rule> irs = inductive_decl_intros(idecl);
      
        while (!is_nil(irs)) {
            intro_rule ir = head(irs);
            s << true << intro_rule_type(ir);
            irs = tail(irs);
        }
        s << false;
    }      

}

export_declaration read_export_declaration(deserializer & d) {
    struct export_declaration edecl;
    edecl.is_inductive_type = d.read_bool();
    edecl.is_constructor = d.read_bool();
    edecl.is_recursor = d.read_bool();
    edecl.is_quot_assumption = d.read_bool();
    edecl.in_prop = d.read_bool();
    edecl.reducible_status = d.read_char();
    edecl.n = read_name(d);
    edecl.type = read_expr(d);
    if (d.read_bool()) {
        /* is definition */
        edecl.val = read_expr(d);
    }
    if (edecl.is_inductive_type) {
        while (d.read_bool()) {
            edecl.constructor_types.push_back(read_expr(d));
        }
    }
    return edecl;
}

#include <iostream>
void export_all_for_blast(std::ostream & out, environment const & env) {
    serializer s(out);
    env.for_each_declaration([&](declaration const & d) {
            s << true;
            write_export_declaration(s,env,d);
        });
    s << false;
}

std::vector<export_declaration> import_blast(std::istream & in) {
    deserializer d(in);
    std::vector<export_declaration> edecls;
    while (d.read_bool()) {
        edecls.push_back(read_export_declaration(d));
    }
    return edecls;
}

}
