#include "eager_search.h"

#include "../evaluation_context.h"
#include "../evaluator.h"
#include "../open_list_factory.h"
#include "../option_parser.h"
#include "../pruning_method.h"

#include "../algorithms/ordered_set.h"
#include "../task_utils/successor_generator.h"
#include "../task_utils/task_properties.h"
#include "../tasks/root_task.h"

#include <cassert>
#include <cstdlib>
#include <memory>
#include <set>
#include <map>

#include <unordered_set>
#include <unordered_map>

using namespace std;

namespace fwdbwd{

    unordered_map<OperatorID, vector<OperatorID> > dependency_map;
    unordered_map<OperatorID, vector<OperatorID> > inverse_map;
    unordered_map<StateID, unordered_set<OperatorID> > forward_nodes;
    unordered_map<OperatorID, bool> goal_ops;
    // the first int in the unordered map below tracks to the variable id
    unordered_map<OperatorID, unordered_map<int, pair<int, bool> > > op_data;

    OpStackNode* stack_root = new OpStackNode(OperatorID::no_operator, NULL);

    bool is_applicable(const GlobalState &state, const OperatorProxy op)
    {
        for(FactProxy precondition: op.get_preconditions())
        {
            if(state[precondition.get_variable().get_id()] != precondition.get_value())
            return false;
        }
        return true;
    }

    // CHANGE: New function added, do check functionality
    // RECHECK: Vulnerable function, created in one go.
    void generate_op_data(const TaskProxy task_proxy)
    {
        for(OperatorProxy op: task_proxy.get_operators())
        {
            for (FactProxy precondition: op.get_preconditions())
            {
                op_data[OperatorID(op.get_id())][precondition.get_variable().get_id()].first = precondition.get_value();
                op_data[OperatorID(op.get_id())][precondition.get_variable().get_id()].second = false;
            }
            for (EffectProxy eff: op.get_effects())
            {
                FactProxy f = eff.get_fact();
                if(op_data[OperatorID(op.get_id())][f.get_variable().get_id()].first != f.get_value())
                    op_data[OperatorID(op.get_id())][f.get_variable().get_id()].second = true; 
            }
        }
    }

    bool check_goal_op(const OperatorProxy op, const TaskProxy task_proxy)
    {
        for(FactProxy precondition: op.get_preconditions())
        {
            for(FactProxy goal_fact: task_proxy.get_goals()) 
            {
                bool flag1 = (precondition.get_variable() == goal_fact.get_variable());
                bool flag2 = (precondition.get_value() != goal_fact.get_value());
                bool flag3 = op_data[OperatorID(op.get_id())][precondition.get_variable().get_id()].second;
                if(flag1 && flag2 && flag3)
                    return true;
            }
        }
        return false;
    }

    // CHANGE: A bug was resolved in this function, do check again.
    void generate_goal_ops(const TaskProxy task_proxy)
    {
        for(OperatorProxy op: task_proxy.get_operators())
          goal_ops[OperatorID(op.get_id())] = check_goal_op(op, task_proxy);
    }

    bool is_dependent(OperatorProxy op1, OperatorProxy op2)
    { 
        // return true op1 supplies some facts to op2

        PreconditionsProxy pre1 = op1.get_preconditions();
        PreconditionsProxy pre2 = op2.get_preconditions();

        for(FactProxy p2: pre2)
        {
            for(FactProxy p1: pre1)
            {
                if(p1.get_variable() == p2.get_variable())
                {
                    if(p1.get_value() != p2.get_value())
                    {
                        if(op_data[OperatorID(op1.get_id())][p1.get_variable().get_id()].second)
                            return true;
                    }
                    else
                    {
                        if(!op_data[OperatorID(op1.get_id())][p1.get_variable().get_id()].second)
                            return true;
                    }
                }
            }
        }
        return false;
    }

    void generate_dependency_graph(const TaskProxy task_proxy)
    {
        OperatorsProxy operators = task_proxy.get_operators();
      
        for (OperatorProxy op1 : operators)
        {
            for(OperatorProxy op2 : operators)
            {
                if(op1 != op2)
                {
                    if(is_dependent(op1, op2))
                    {
                        dependency_map[OperatorID(op1.get_id())].push_back(OperatorID(op2.get_id()));
                        inverse_map[OperatorID(op2.get_id())].push_back(OperatorID(op1.get_id()));
                    }
                }
            }
        }
    }

    // Call all the functions here
    void calculate(const TaskProxy task_proxy)
    {
        generate_op_data(task_proxy);
        generate_goal_ops(task_proxy);
        generate_dependency_graph(task_proxy);
    }

    FwdbwdNode::FwdbwdNode(StateID state_id, OperatorID operator_id, OpStackNode* op_stack_node, int g_value):
    id(state_id), op_id(operator_id)
    {
        op_stack = op_stack_node;
        state_g_value = g_value;
    }

    bool FwdbwdNode::operator<(const FwdbwdNode& rhs) const{
    
        if(op_stack == NULL && rhs.get_stack_pointer() == NULL)
            return state_g_value < rhs.get_g();

        else if(op_stack != NULL && rhs.get_stack_pointer() != NULL)
            return op_stack->get_depth() < rhs.get_stack_pointer()->get_depth();
    
        else
            return (op_stack == NULL)? true: false;
    }

}

namespace eager_search {
EagerSearch::EagerSearch(const Options &opts)
    : SearchEngine(opts),
      reopen_closed_nodes(opts.get<bool>("reopen_closed")),
      open_list(opts.get<shared_ptr<OpenListFactory>>("open")->
                create_fwdbwd_open_list()),
      f_evaluator(opts.get<shared_ptr<Evaluator>>("f_eval", nullptr)),
      preferred_operator_evaluators(opts.get_list<shared_ptr<Evaluator>>("preferred")),
      lazy_evaluator(opts.get<shared_ptr<Evaluator>>("lazy_evaluator", nullptr)),
      pruning_method(opts.get<shared_ptr<PruningMethod>>("pruning")) {
    if (lazy_evaluator && !lazy_evaluator->does_cache_estimates()) {
        cerr << "lazy_evaluator must cache its estimates" << endl;
        utils::exit_with(utils::ExitCode::SEARCH_INPUT_ERROR);
    }
}

void EagerSearch::initialize() {
    cout << "Conducting best first search"
         << (reopen_closed_nodes ? " with" : " without")
         << " reopening closed nodes, (real) bound = " << bound
         << endl;
    assert(open_list);

    // fwdbwd code
    fwdbwd::calculate(task_proxy);
    // fwdbwd code


    set<Evaluator *> evals;
    open_list->get_path_dependent_evaluators(evals);

    if (f_evaluator) {
        f_evaluator->get_path_dependent_evaluators(evals);
    }

    path_dependent_evaluators.assign(evals.begin(), evals.end());

    const GlobalState &initial_state = state_registry.get_initial_state();
    for (Evaluator *evaluator : path_dependent_evaluators) {
        evaluator->notify_initial_state(initial_state);
    }

    /*
      Note: we consider the initial state as reached by a preferred
      operator.
    */
    EvaluationContext eval_context(initial_state, 0, true, &statistics);

    statistics.inc_evaluated_states();

    if (open_list->is_dead_end(eval_context)) {
        cout << "Initial state is a dead end." << endl;
    } else {
        if (search_progress.check_progress(eval_context))
            print_checkpoint_line(0);
        start_f_value_statistics(eval_context);
        SearchNode node = search_space.get_node(initial_state);
        node.open_initial();

        fwdbwd::FwdbwdNode fwdbwd_node(initial_state.get_id(), OperatorID::no_operator, NULL, node.get_real_g());
        open_list->insert(eval_context, fwdbwd_node);
    }

    print_initial_evaluator_values(eval_context);

}

void EagerSearch::print_checkpoint_line(int g) const {
    cout << "[g=" << g << ", ";
    statistics.print_basic_statistics();
    cout << "]" << endl;
}

void EagerSearch::print_statistics() const {
    statistics.print_detailed_statistics();
    search_space.print_statistics();
    pruning_method->print_statistics();
}

SearchStatus EagerSearch::step()
{
    pair<fwdbwd::FwdbwdNode, bool> n = fetch_next_node();
    if(!n.second)
        return FAILED;
    fwdbwd::FwdbwdNode fwdbwd_node = n.first;
    if(!fwdbwd_node.get_stack_pointer())
      return forward_step(fwdbwd_node);
    else
      return backward_step(fwdbwd_node);
}

SearchStatus EagerSearch::forward_step(fwdbwd::FwdbwdNode fwdbwd_node)
{
    // Get the search node from id
    StateID id = fwdbwd_node.get_state();
    GlobalState s = state_registry.lookup_state(id);
    SearchNode node = search_space.get_node(s);

    if (check_goal_and_set_plan(s))
        return SOLVED;

    vector<fwdbwd::FwdbwdOps> fwdbwd_ops = generate_fwdbwd_ops(s, fwdbwd_node.get_operator());
    EvaluationContext eval_context(s, node.get_g(), false, &statistics, true);


    for (fwdbwd::FwdbwdOps fwdbwd_op: fwdbwd_ops) {

        OperatorID op_id = fwdbwd_op.first;
        OperatorProxy op = task_proxy.get_operators()[op_id];
        if(fwdbwd_op.second)
        {
            if ((node.get_real_g() + op.get_cost()) >= bound)
                continue;
            GlobalState succ_state = state_registry.get_successor_state(s, op);
            //FWDBWD: What do they consider when counting generated nodes? What if an old node is generated?
            statistics.inc_generated();


            SearchNode succ_node = search_space.get_node(succ_state);

            // Previously encountered dead end. Don't re-evaluate.
            if (succ_node.is_dead_end())
                continue;

            // Urgent: Check if repeated notifications cause error.
            for (Evaluator *evaluator : path_dependent_evaluators) {
                evaluator->notify_state_transition(s, op_id, succ_state);
            }

            if (succ_node.is_new()) {

                int succ_g = node.get_g() + get_adjusted_cost(op);

                EvaluationContext succ_eval_context(
                    succ_state, succ_g, NULL, &statistics);
                statistics.inc_evaluated_states();

                if (open_list->is_dead_end(succ_eval_context)) {
                    succ_node.mark_as_dead_end();
                    statistics.inc_dead_ends(); 
                    continue;
                }
                succ_node.open(node, op, get_adjusted_cost(op));

                // succ_node.store_foward_operator(op_id);
                fwdbwd::forward_nodes[succ_state.get_id()].insert(op_id);

                fwdbwd::FwdbwdNode succ_fwdbwd_node(succ_state.get_id(), op_id, NULL, succ_node.get_real_g());
                open_list->insert(eval_context, succ_fwdbwd_node);
                if (search_progress.check_progress(eval_context)) {
                    print_checkpoint_line(succ_node.get_g());
                    reward_progress();
                }
            }
            else{
                if(succ_node.get_g() > node.get_g() + get_adjusted_cost(op))
                    succ_node.update_parent(succ_node, op, get_adjusted_cost(op));
                
                // FWDBWD: Check if the same operator and state pair has not been seen before
                // check if the state is reached via a new operator.
                if(fwdbwd::forward_nodes[succ_state.get_id()].find(op_id) == fwdbwd::forward_nodes[succ_state.get_id()].end())
                {
                    fwdbwd::forward_nodes[succ_state.get_id()].insert(op_id);
                    EvaluationContext eval_context(
                        succ_state, succ_node.get_g(), NULL, &statistics);
                    fwdbwd::FwdbwdNode succ_fwdbwd_node(succ_state.get_id(), op_id, NULL, succ_node.get_real_g());
                    open_list->insert(eval_context, succ_fwdbwd_node);
                }
            }   
        }
        else
        {
            // push the current and all it's dependent ones on the stack
            // also check if you've observed the same pair before

            pair<OpStackNode*, bool> first_child = fwdbwd::stack_root->gen_child(op_id, id, op.get_cost());
            if(first_child.second)
            {
                // careful op_id already in use
                for (OperatorID oid: fwdbwd::dependency_map[op_id])
                {
                    OperatorProxy op2 = task_proxy.get_operators()[oid];
                    pair<OpStackNode*, bool> second_child = (first_child.first)->gen_child(oid, id, op2.get_cost());
                    if(second_child.second)
                    {
                        // Now push this backward into the open list
                        fwdbwd::FwdbwdNode succ_fwdbwd_node(id, OperatorID::no_operator, second_child.first, node.get_real_g());
                        open_list->insert(eval_context, succ_fwdbwd_node);
                    }
                }
            }
        }
    }

    return IN_PROGRESS;


}

SearchStatus EagerSearch::backward_step(fwdbwd::FwdbwdNode fwdbwd_node)
{
    OpStackNode* op_stack_node = fwdbwd_node.get_stack_pointer();
    assert(op_stack_node != NULL);

    StateID id = fwdbwd_node.get_state();
    GlobalState s = state_registry.lookup_state(id);
    SearchNode node = search_space.get_node(s);

    OperatorID op_id = op_stack_node->get_operator();
    OperatorProxy op = task_proxy.get_operators()[op_id];

    EvaluationContext eval_context(s, node.get_g(), false, &statistics, true);
    
    if(task_properties::is_applicable(op, convert_global_state(s)))
    {
        /* Apply the top stack operator to the current state
        and push the data entry into the new stack
        if the current operator_stack_pointer is equal to stack_root
        then stop the search */

        if ((node.get_real_g() + op.get_cost()) >= bound)
            return IN_PROGRESS;
        GlobalState succ_state = state_registry.get_successor_state(s, op);
        //FWDBWD: What do they consider when counting generated nodes? What if an old node is generated?
        statistics.inc_generated();

        SearchNode succ_node = search_space.get_node(succ_state);

        if (succ_node.is_dead_end())
            return IN_PROGRESS;

        // update new path
        for (Evaluator *evaluator : path_dependent_evaluators) {
            evaluator->notify_state_transition(s, op_id, succ_state);
        }

        if (succ_node.is_new()) {

            // OPTIMIZE: Can we do something about the goal states found here?

            int succ_g = node.get_g() + get_adjusted_cost(op);
            EvaluationContext eval_context(
                succ_state, succ_g, NULL, &statistics);
            statistics.inc_evaluated_states();

            if (open_list->is_dead_end(eval_context)) {
                succ_node.mark_as_dead_end();
                statistics.inc_dead_ends();
                return IN_PROGRESS;
            }
            succ_node.open(node, op, get_adjusted_cost(op));

            OpStackNode* parent_op_stack_node = op_stack_node->get_parent();
            parent_op_stack_node->store_state(succ_state.get_id());

            if(parent_op_stack_node == fwdbwd::stack_root)
            {
                // cout << "VERY GOOD WARNING -- 1" << endl;
                fwdbwd::forward_nodes[succ_state.get_id()].insert(op_id);
                fwdbwd::FwdbwdNode succ_fwdbwd_node(succ_state.get_id(), op_id, NULL, succ_node.get_real_g());
                open_list->insert(eval_context, succ_fwdbwd_node);
            }
            else
            {
                // cout << "GOOD WARNING -- 1" << endl;
                fwdbwd::FwdbwdNode succ_fwdbwd_node(succ_state.get_id(), OperatorID::no_operator, parent_op_stack_node, succ_node.get_real_g());
                open_list->insert(eval_context, succ_fwdbwd_node);
            }
            if (search_progress.check_progress(eval_context)) {
                print_checkpoint_line(succ_node.get_g());
                reward_progress();
            }
        }
        else{
            if(succ_node.get_g() > node.get_g() + get_adjusted_cost(op))
                succ_node.update_parent(succ_node, op, get_adjusted_cost(op));
            OpStackNode* parent_op_stack_node = op_stack_node->get_parent();
            bool flag = parent_op_stack_node->store_state(succ_state.get_id());
            if(flag)
            {
                EvaluationContext eval_context(
                    succ_state, succ_node.get_g(), NULL, &statistics);
                if(parent_op_stack_node == fwdbwd::stack_root)
                {
                    if(fwdbwd::forward_nodes[succ_state.get_id()].find(op_id) == fwdbwd::forward_nodes[succ_state.get_id()].end())
                    {
                        fwdbwd::forward_nodes[succ_state.get_id()].insert(op_id);
                        fwdbwd::FwdbwdNode succ_fwdbwd_node(succ_state.get_id(), op_id, NULL, succ_node.get_real_g());
                        open_list->insert(eval_context, succ_fwdbwd_node);
                    }
                }
                else
                {
                    fwdbwd::FwdbwdNode succ_fwdbwd_node(succ_state.get_id(), OperatorID::no_operator, parent_op_stack_node, succ_node.get_real_g());
                    open_list->insert(eval_context, succ_fwdbwd_node);
                }
            }
        }
    }
    else
    {
        for (OperatorID oid : (fwdbwd::dependency_map[op_stack_node->get_operator()]))
        {
            OperatorProxy op = task_proxy.get_operators()[oid];
            pair<OpStackNode*, bool> child = op_stack_node->gen_child(oid, id, op.get_cost());

            if(child.second)
            {
                fwdbwd::FwdbwdNode succ_fwdbwd_node(id, OperatorID::no_operator, child.first, fwdbwd_node.get_g());
                open_list->insert(eval_context, succ_fwdbwd_node);
            }
        }
    }
    return IN_PROGRESS;
}

pair<fwdbwd::FwdbwdNode, bool> EagerSearch::fetch_next_node() {
    while (true) {
        if (open_list->empty()) {
            cout << "Completely explored state space -- no solution!" << endl;
            fwdbwd::FwdbwdNode dummy_node(StateID::no_state, OperatorID::no_operator, NULL, 0);
            return make_pair(dummy_node, false);
        }
        fwdbwd::FwdbwdNode fwdbwdNode = open_list->remove_min();

        StateID id = fwdbwdNode.get_state();
        GlobalState s = state_registry.lookup_state(id);
        SearchNode node = search_space.get_node(s);

        if (node.is_closed())
            continue;
        // MUST:: Check the value of lazy_evaluator. Should be false.
        assert(!node.is_dead_end());
        /* FWDBWD: Should it be updated for backwards node? 
        We might be in a loop error or something
        if EvaluationContext is considering f_value_statistics in
        that sense.
        */
        update_f_value_statistics(node);
        /*
        FWDBWD: Should this be counted as expanded? 
        When reopen_closed_node was there, we did count it as expanded.
        Look for how it effects search and stuff.
        */
        statistics.inc_expanded();
        return make_pair(fwdbwdNode, true);
    }
}

void EagerSearch::reward_progress() {
    // Boost the "preferred operator" open lists somewhat whenever
    // one of the heuristics finds a state with a new best h value.
    open_list->boost_preferred();
}

void EagerSearch::dump_search_space() const {
    search_space.dump(task_proxy);
}

void EagerSearch::start_f_value_statistics(EvaluationContext &eval_context) {
    if (f_evaluator) {
        int f_value = eval_context.get_evaluator_value(f_evaluator.get());
        statistics.report_f_value_progress(f_value);
    }
}

/* TODO: HACK! This is very inefficient for simply looking up an h value.
   Also, if h values are not saved it would recompute h for each and every state. */
void EagerSearch::update_f_value_statistics(const SearchNode &node) {
    if (f_evaluator) {
        /*
          TODO: This code doesn't fit the idea of supporting
          an arbitrary f evaluator.
        */
        EvaluationContext eval_context(node.get_state(), node.get_g(), false, &statistics);
        int f_value = eval_context.get_evaluator_value(f_evaluator.get());
        statistics.report_f_value_progress(f_value);
    }
}

State EagerSearch::convert_global_state(const GlobalState &global_state) const {
    return task_proxy.convert_ancestor_state(global_state.unpack());
}

vector<fwdbwd::FwdbwdOps> EagerSearch::generate_fwdbwd_ops(GlobalState s, OperatorID op_id)
{
        vector<OperatorID> base_ops;
        vector<fwdbwd::FwdbwdOps> fwdbwd_ops;

        
        if((op_id == OperatorID::no_operator) || fwdbwd::goal_ops[op_id])
        {
            successor_generator.generate_applicable_ops(s, base_ops);
            for(OperatorID id: base_ops)
                fwdbwd_ops.push_back(make_pair(id, true));
        }
        else
        {
            base_ops = fwdbwd::inverse_map[op_id];
            State state = convert_global_state(s);

            for(OperatorID id: base_ops)
            {
                OperatorProxy op = task_proxy.get_operators()[id];
                if(task_properties::is_applicable(op, state))
                    fwdbwd_ops.push_back(make_pair(id, true));
                else
                    fwdbwd_ops.push_back(make_pair(id, false));
            }
        }

        return fwdbwd_ops;
}

}
