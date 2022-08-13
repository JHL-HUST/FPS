#ifndef _HEURISTIC_H_
#define _HEURISTIC_H_

#include "basis_pms.h"
#include "deci.h"

void MaxFPS::init(vector<int> &init_solution)
{
    soft_large_weight_clauses_count = 0;
    //Initialize clause information
    for (int c = 0; c < num_clauses; c++)
    {
        already_in_soft_large_weight_stack[c] = 0;
        clause_selected_count[c] = 0;

        if (org_clause_weight[c] == top_clause_weight)
            clause_weight[c] = 1;
        else
        {
            if (best_soln_feasible == 0)
            {
                clause_weight[c] = 0;
            }
            else
            {
                clause_weight[c] = org_clause_weight[c];
                if (clause_weight[c] > 1 && already_in_soft_large_weight_stack[c] == 0)
                {
                    already_in_soft_large_weight_stack[c] = 1;
                    soft_large_weight_clauses[soft_large_weight_clauses_count++] = c;
                }
            }
        }
    }

    //init solution
    if (best_soln_feasible == 1)
    {
        best_soln_feasible = 2;
        for (int v = 1; v <= num_vars; v++)
        {
            //cur_soln[v] = rand() % 2;
            time_stamp[v] = 0;
            unsat_app_count[v] = 0;
        }
    }
    else if (init_solution.size() == 0)
    {
        for (int v = 1; v <= num_vars; v++)
        {
            cur_soln[v] = rand() % 2;
            time_stamp[v] = 0;
            unsat_app_count[v] = 0;
        }
    }
    else
    {
        for (int v = 1; v <= num_vars; v++)
        {
            cur_soln[v] = init_solution[v];
            if (cur_soln[v] != 0 && cur_soln[v] != 1)
                cur_soln[v] = rand() % 2;
            time_stamp[v] = 0;
            unsat_app_count[v] = 0;
        }
    }

    //init stacks
    hard_unsat_nb = 0;
    soft_unsat_weight = 0;
    hardunsat_stack_fill_pointer = 0;
    softunsat_stack_fill_pointer = 0;
    unsatvar_stack_fill_pointer = 0;
    large_weight_clauses_count = 0;

    /* figure out sat_count, sat_var and init unsat_stack */
    for (int c = 0; c < num_clauses; ++c)
    {
        sat_count[c] = 0;
        for (int j = 0; j < clause_lit_count[c]; ++j)
        {
            if (cur_soln[clause_lit[c][j].var_num] == clause_lit[c][j].sense)
            {
                sat_count[c]++;
                sat_var[c] = clause_lit[c][j].var_num;
            }
        }
        if (sat_count[c] == 0)
        {
            unsat(c);
        }
    }

    /*figure out score*/
    for (int v = 1; v <= num_vars; v++)
    {
        score[v] = 0;
        for (int i = 0; i < var_lit_count[v]; ++i)
        {
            int c = var_lit[v][i].clause_num;
            if (sat_count[c] == 0)
                score[v] += clause_weight[c];
            else if (sat_count[c] == 1 && var_lit[v][i].sense == cur_soln[v])
                score[v] -= clause_weight[c];
        }
    }

    //init goodvars stack
    goodvar_stack_fill_pointer = 0;
    for (int v = 1; v <= num_vars; v++)
    {
        if (score[v] > 0)
        {
            already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
            mypush(v, goodvar_stack);
        }
        else
            already_in_goodvar_stack[v] = -1;
    }

    //cout << goodvar_stack_fill_pointer << endl;
    //cout << hard_unsat_nb << endl;
    //cout << soft_unsat_weight << endl;
}

int MaxFPS::pick_var()
{
    int i, v;
    int best_var;

    if ((rand() % MY_RAND_MAX_INT) * BASIC_SCALE < rdprob)
        return goodvar_stack[rand() % goodvar_stack_fill_pointer];

    if (goodvar_stack_fill_pointer < hd_count_threshold)
    {
        best_var = goodvar_stack[0];
        for (i = 1; i < goodvar_stack_fill_pointer; ++i)
        {
            v = goodvar_stack[i];
            if (score[v] > score[best_var])
                best_var = v;
            else if (score[v] == score[best_var])
            {
                if (time_stamp[v] < time_stamp[best_var])
                    best_var = v;
            }
        }
        return best_var;
    }
    else
    {
        best_var = goodvar_stack[rand() % goodvar_stack_fill_pointer];
        for (i = 1; i < hd_count_threshold; ++i)
        {
            v = goodvar_stack[rand() % goodvar_stack_fill_pointer];
            if (score[v] > score[best_var])
                best_var = v;
            else if (score[v] == score[best_var])
            {
                if (time_stamp[v] < time_stamp[best_var])
                    best_var = v;
            }
        }
        return best_var;
    }
}

void MaxFPS::pick_vars() 
{
    int i, v;

    if ((rand() % MY_RAND_MAX_INT) * BASIC_SCALE < rwprob){
        update_clause_weights();
        int sel_c;
        
        if (hardunsat_stack_fill_pointer > 0)
        {
            sel_c = hardunsat_stack[rand() % hardunsat_stack_fill_pointer];
        }
        else
        {
            while(1){
                sel_c = softunsat_stack[rand() % softunsat_stack_fill_pointer];
                if (clause_lit_count[sel_c]>0)
                    break;
            }
        }
    
        best_vars[0] = clause_lit[sel_c][rand() % clause_lit_count[sel_c]].var_num;
        selected_nums = 1;
        flip(best_vars[0]);
        time_stamp[best_vars[0]]=step;
        return;
    }

    selected_nums = sc_num;
    
    if (hardunsat_stack_fill_pointer > 0){
        for (i = 0; i < sc_num; i++){
            sel_cs[i] = hardunsat_stack[rand() % hardunsat_stack_fill_pointer];
        }
    }
    else{
        for (i = 0; i < sc_num; i++){
            sel_cs[i] = softunsat_stack[rand() % softunsat_stack_fill_pointer];
        }
    }

    int best_vars_num = 0;
    
    for (i = 0; i < sc_num; i++){
        if (clause_lit_count[sel_cs[i]] == 0){
            selected_nums--;
            continue;
        }
        best_vars[best_vars_num] = clause_lit[sel_cs[i]][rand() % clause_lit_count[sel_cs[i]]].var_num;
        
        if (selected[best_vars[best_vars_num]]){
            selected_nums--;
        }
        else {
            selected[best_vars[best_vars_num]] = 1;
            best_vars_num++;
        }
    }
    
    
    for (i = 0; i < selected_nums; i++)
        selected[best_vars[i]] = 0;
    
    if (selected_nums == 1){
        flip(best_vars[0]);
        time_stamp[best_vars[0]]=step;
        return;
    }
    
    long long max_score1 = LONG_LONG_MIN, max_score2 = LONG_LONG_MIN;
    int num1, num2;
    
    for (i = 0; i < selected_nums; i++)
    {
        scores[i] = score[best_vars[i]];
        if (score[best_vars[i]] > max_score1){
            max_score1 = score[best_vars[i]]; num1 = i;
        }
        else if (score[best_vars[i]] == max_score1){
            if (time_stamp[best_vars[i]] < time_stamp[best_vars[num1]])
                num1 = i;
        }
    }
    
    int j;

    for (i = 0; i < selected_nums; i++)
    {
        flip2(best_vars[i]);
        if (goodvar_stack2_num > 0){
            if (goodvar_stack2_num < sv_num)
            {
                vars2[i] = goodvar_stack2[0];
                for (j = 1; j < goodvar_stack2_num; ++j)
                {
                    v = goodvar_stack2[j];
                    if (score2[v] > score2[vars2[i]])
                        vars2[i] = v;
                    else if (score2[v] == score2[vars2[i]])
                    {
                        if (time_stamp[v] < time_stamp[vars2[i]])
                            vars2[i] = v;
                    }
                }
            }
            else
            {
                vars2[i] = goodvar_stack2[rand() % goodvar_stack2_num];
                for (j = 1; j < sv_num; ++j)
                {
                    v = goodvar_stack2[rand() % goodvar_stack2_num];
                    if (score2[v] > score2[vars2[i]])
                        vars2[i] = v;
                    else if (score2[v] == score2[vars2[i]])
                    {
                        if (time_stamp[v] < time_stamp[vars2[i]])
                            vars2[i] = v;
                    }
                }
            }
            scores[i] += score2[vars2[i]];
            if (scores[i] > 0){
                flip(best_vars[i]);
                flip(vars2[i]);
                time_stamp[best_vars[i]] = step;
                time_stamp[vars2[i]] = step;
                return;
            }
        }
        else{
            scores[i] -= 1000;
        }

        if (scores[i] > max_score1){
            if (scores[i] > max_score2){
                max_score2 = scores[i]; num2 = i;
            }
            else if (scores[i] == max_score2){
                if (time_stamp[best_vars[i]] + time_stamp[vars2[i]] < time_stamp[best_vars[num2]] + time_stamp[vars2[num2]])
                    num2 = i;
            }
        }

    }
    update_clause_weights();
    if (max_score1 >= max_score2){
        flip(best_vars[num1]);
        time_stamp[best_vars[num1]] = step;
    }
    else{
        flip(best_vars[num2]); flip(vars2[num2]);
        time_stamp[best_vars[num2]] = step;
        time_stamp[vars2[num2]] = step;
    }

    return;
}

void MaxFPS::local_search(char *inputfile)
{
    vector<int> init_solution;
    settings();
    for (tries = 1; tries < max_tries; ++tries)
    {
        init(init_solution);
        for (step = 1; step < max_flips; ++step)
        {
            if (hard_unsat_nb == 0 && (soft_unsat_weight < opt_unsat_weight || best_soln_feasible == 0))
            {
                if (soft_unsat_weight < opt_unsat_weight)
                {
                    best_soln_feasible = 1;
                    opt_unsat_weight = soft_unsat_weight;
                    opt_time = get_runtime();
                    for (int v = 1; v <= num_vars; ++v)
                        best_soln[v] = cur_soln[v];
                }
                if (opt_unsat_weight == 0)
                    return;
            }

            if (step % 1000 == 0)
            {
                double elapse_time = get_runtime();
                if (elapse_time >= cutoff_time)
                    return;
                else if (opt_unsat_weight == 0)
                    return;
            }
            
            int flipvar = pick_var();
            flip(flipvar);
            time_stamp[flipvar] = step;
        }
    }
}

void MaxFPS::local_search_with_decimation(char *inputfile)
{
    settings();
    Decimation deci(var_lit, var_lit_count, clause_lit, org_clause_weight, top_clause_weight);
    deci.make_space(num_clauses, num_vars);
    
    for(int i = 1; i <= num_vars; i++)
        selected[i] = 0;
    
    opt_unsat_weight = __LONG_LONG_MAX__;
    for (tries = 1; tries < max_tries; ++tries)
    {
        if (get_runtime()>=cutoff)
            break;
    
        if (best_soln_feasible != 1)
        {
            deci.init(local_opt_soln, best_soln, unit_clause, unit_clause_count, clause_lit_count);
            deci.unit_prosess();
            init(deci.fix);
        }
        else
            init(deci.fix);

        long long local_opt = __LONG_LONG_MAX__;
        max_flips = max_non_improve_flip;
        for (step = 1; step < max_flips; ++step)
        {
            if (get_runtime()>=cutoff)
                break;
                
            if (hard_unsat_nb == 0)
            {
                if (local_opt > soft_unsat_weight)
                {
                    local_opt = soft_unsat_weight;
                    max_flips = step + max_non_improve_flip;
                }
                if (soft_unsat_weight < opt_unsat_weight)
                {
                    cout << "o " << soft_unsat_weight << endl;
                    opt_unsat_weight = soft_unsat_weight;
                    opt_time = get_runtime();
                    for (int v = 1; v <= num_vars; ++v)
                        best_soln[v] = cur_soln[v];
                }
                if (best_soln_feasible == 0)
                {
                    best_soln_feasible = 1;
                    break;
                }
            }
            //if(goodvar_stack_fill_pointer==0) cout<<step<<": 0"<<endl;
            
            if(goodvar_stack_fill_pointer > 0){
                int flipvar = pick_var();
                flip(flipvar);
                time_stamp[flipvar] = step;
            }
            else{
                pick_vars();
            }
            
        }
        if (get_runtime()>=cutoff)
            break;
    }
    
    
}

void MaxFPS::increase_weights()
{
    int i, c, v;
    for (i = 0; i < hardunsat_stack_fill_pointer; ++i)
    {
        c = hardunsat_stack[i];
        clause_weight[c] += h_inc;

        if (clause_weight[c] == (h_inc + 1))
            large_weight_clauses[large_weight_clauses_count++] = c;

        for (lit *p = clause_lit[c]; (v = p->var_num) != 0; p++)
        {
            score[v] += h_inc;
            if (score[v] > 0 && already_in_goodvar_stack[v] == -1)
            {
                already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                mypush(v, goodvar_stack);
            }
        }
    }
    if (best_soln_feasible > 0){
        for (i = 0; i < softunsat_stack_fill_pointer; ++i)
        {
            c = softunsat_stack[i];
            if (clause_weight[c] > softclause_weight_threshold)
                continue;
            else
                clause_weight[c]++;
    
            if (clause_weight[c] > 1 && already_in_soft_large_weight_stack[c] == 0)
            {
                already_in_soft_large_weight_stack[c] = 1;
                soft_large_weight_clauses[soft_large_weight_clauses_count++] = c;
            }
            if(clause_lit_count[c] > 0){
                for (lit *p = clause_lit[c]; (v = p->var_num) != 0; p++)
                {
                    score[v]++;
                    if (score[v] > 0 && already_in_goodvar_stack[v] == -1)
                    {
                        already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                        mypush(v, goodvar_stack);
                    }
                }
            }
        }
    }
}

void MaxFPS::smooth_weights()
{
    int i, clause, v;

    for (i = 0; i < large_weight_clauses_count; i++)
    {
        clause = large_weight_clauses[i];
        if (sat_count[clause] > 0)
        {
            clause_weight[clause] -= h_inc;

            if (clause_weight[clause] == 1)
            {
                large_weight_clauses[i] = large_weight_clauses[--large_weight_clauses_count];
                i--;
            }
            if (sat_count[clause] == 1)
            {
                v = sat_var[clause];
                score[v] += h_inc;
                if (score[v] > 0 && already_in_goodvar_stack[v] == -1)
                {
                    already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                    mypush(v, goodvar_stack);
                }
            }
        }
    }
    if (best_soln_feasible > 0){
        for (i = 0; i < soft_large_weight_clauses_count; i++)
        {
            clause = soft_large_weight_clauses[i];
            if (sat_count[clause] > 0)
            {
                clause_weight[clause]--;
                if (clause_weight[clause] == 1 && already_in_soft_large_weight_stack[clause] == 1)
                {
                    already_in_soft_large_weight_stack[clause] = 0;
                    soft_large_weight_clauses[i] = soft_large_weight_clauses[--soft_large_weight_clauses_count];
                    i--;
                }
                if (sat_count[clause] == 1)
                {
                    v = sat_var[clause];
                    score[v]++;
                    if (score[v] > 0 && already_in_goodvar_stack[v] == -1)
                    {
                        already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                        mypush(v, goodvar_stack);
                    }
                }
            }
        }
    }
}

void MaxFPS::update_clause_weights()
{
    if (((rand() % MY_RAND_MAX_INT) * BASIC_SCALE) < smooth_probability && large_weight_clauses_count > large_clause_count_threshold)
    {
        smooth_weights();
    }
    else
    {
        increase_weights();
    }
}

#endif
