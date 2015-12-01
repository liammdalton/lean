/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "library/blast/dummy_branch_extension.h"
#include "library/blast/trace.h"
#include <vector>

namespace lean {
namespace blast {

struct dummy_state : imp_extension_state {
    std::vector<std::vector<hypothesis> > m_state;
    void push() override {
        m_state.emplace_back();
    }
    void pop() override {
        m_state.pop_back();
    }

    void assert(hypothesis const & h) override {
        m_state.back().push_back(h);
    }

    void show() {
        ios().get_diagnostic_channel() << "DUMMY_STATE: ";
        for (auto v : m_state) {
            for (auto h : v) {
                ios().get_diagnostic_channel() << h.get_name() << " ";
            }
        }
        ios().get_diagnostic_channel() << "\n";
    }
};

static ext_state_maker g_ext_state_maker = []() { return new dummy_state(); };
static unsigned g_ext_id = 0;

static dummy_state & get_dummy_state() {
    return static_cast<dummy_state&>(get_imp_extension_state(g_ext_id));
}

action_result dummy_action() {
    trace_action("dummy_state");
    ios().get_diagnostic_channel() << "TRUE_STATE: ";
    curr_state().for_each_hypothesis([&](hypothesis_idx, hypothesis const & h) {
            ios().get_diagnostic_channel() << h.get_name() << " ";
        });
    ios().get_diagnostic_channel() << "\n";
    get_dummy_state().show();
    return action_result::failed();
}

void initialize_dummy_action() {
    g_ext_id = register_imp_extension(g_ext_state_maker);
}

void finalize_dummy_action() { }

}}
