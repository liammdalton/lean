/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include "library/blast/state.h"
#include "library/blast/blast.h"
#include "library/blast/imp_extension.h"
#include <vector>

namespace lean {
namespace blast {

action_result dummy_action();
void initialize_dummy_action();
void finalize_dummy_action();

}}
