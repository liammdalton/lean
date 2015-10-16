/*
  Copyright (c) 2015 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
*/
#pragma once
#include <string>
#include "util/serializer.h"
#include "library/reducible.h"
#include "kernel/expr.h"
#include "kernel/environment.h"
#include "kernel/declaration.h"
#include <vector>

namespace lean {

struct export_declaration { 
    bool is_inductive_type;
    bool is_constructor;
    bool is_recursor;
    bool is_quot_assumption;
    bool in_prop;
    char reducible_status;
    name n;
    expr type;
    optional<expr> val;

    std::vector<expr> constructor_types;
};

void write_export_declaration(serializer & s, environment const & env, declaration const & d);
export_declaration read_export_declaration(deserializer & d);

}
