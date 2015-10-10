/*
  Copyright (c) 2015 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
*/

#pragma once
#include "kernel/environment.h"
#include <vector>

namespace lean {

void export_all_for_blast(std::ostream & out, environment const & env);
void export_dependency_dataset_for_blast(std::ostream & out, environment const & env);

}
