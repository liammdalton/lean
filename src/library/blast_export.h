/*
  Copyright (c) 2015 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

*/
#pragma once
#include "kernel/environment.h"
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

void export_all_for_blast(std::ostream & out, environment const & env);
std::vector<export_declaration> import_blast(std::istream & in);
}
