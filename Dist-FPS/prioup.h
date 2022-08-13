#include "basis_pms.h"

//priority_queue
struct cmp{

	bool operator () (lit &a, lit & b) const
	{
		return clause_weight[a.clause_num] < clause_weight[b.clause_num];
	}
};
priority_queue<lit, vector<lit>, cmp> unit_clause_priority_queue;

int		cp_clause_lit_count[MAX_CLAUSES];
bool     clause_delete[MAX_CLAUSES];
int		sense_in_queue[MAX_VARS];	


/*
int unassigned_var[MAX_VARS];
int index_in_unassigned_var[MAX_VARS];
int unassigned_count;

inline
void remove_unassigned_var(int var)
{
	int index, last_unassigned_var;
	
	last_unassigned_var = unassigned_var[--unassigned_count];
	index = index_in_unassigned_var[var];
	unassigned_var[index] = last_unassigned_var;
	index_in_unassigned_var[last_unassigned_var]=index;
}*/

void assign(int var, bool sense)
{
	int c,v;
    int i,j;
    lit cur, cur_c;
    
	fix[var] = sense;//assign the variable in unit clause
	
	//remove_unassigned_var(var);
	//fix[var]=1;
        
    for(i = 0; i<var_lit_count[var]; ++i)
    {
            cur = var_lit[var][i];
            c = cur.clause_num;
            
            if(clause_delete[c]==1) continue;
            
            if(cur.sense == sense)//then remove the clause from the formula (by marking it as deleted).
            {
                clause_delete[c]=1;
            }
            else
            {
            	for(j=0; j<clause_lit_count[c]; ++j)
                {
					if(clause_lit[c][j].var_num == var)
					{
						struct lit tmplit;
						tmplit = clause_lit[c][j];
						clause_lit[c][j] = clause_lit[c][--cp_clause_lit_count[c]];
						clause_lit[c][cp_clause_lit_count[c]] = tmplit;
						break;
					}
                }
                
                if (cp_clause_lit_count[c]==1)//newly generated unit clause
                {
                	lit tmplit=clause_lit[c][0];
                	int tmpvar=clause_lit[c][0].var_num;
                	
                	if (sense_in_queue[tmpvar] == -1)
                	{
		            	unit_clause_priority_queue.push(tmplit);
		            	sense_in_queue[tmpvar] = tmplit.sense;
		            }
		            else
		            {
		            	if (sense_in_queue[tmpvar]!=tmplit.sense)
		            		fix[tmpvar]=-2;//mark this var to be forbidden to assign
		            }
                }
                    
            
        	}
	}

}


void unit_propagation()
{
    lit uc_lit;
    int uc_var;
    bool uc_sense;

    while (unit_clause_priority_queue.empty()!=true)
    {
        uc_lit = unit_clause_priority_queue.top();
        unit_clause_priority_queue.pop();
        
        uc_var = uc_lit.var_num;
        uc_sense = uc_lit.sense;
        
        if (fix[uc_var]==-2) {
        	//remove_unassigned_var(uc_var);
        	continue;
        }
         
        assign(uc_var, uc_sense);
   
    }//begpointer to endpointer for
    
}

int uc_count=0;

void pre_assign()
{
	lit uc_lit;
    int  as_var;
    bool as_sense;
    
    int c,v,i;
    uc_count=0;

    
    for (i=0; i<num_vars; ++i)
    {
    	v=i+1;
    	//unassigned_var[i]=v;
    	//index_in_unassigned_var[v]=i;
    	
    	fix[v] = -1;
		//cur_soln[v]=-1;//unassigned
		sense_in_queue[v]=-1;//not in uc queue
    }
    
    for (c = 0; c < num_clauses; c++) 
	{
		clause_delete[c] = 0;
		cp_clause_lit_count[c] = clause_lit_count[c];
		
		//unit clause
        if(clause_lit_count[c]==1)
        {
        	lit tmplit=clause_lit[c][0];
        	int tmpvar=tmplit.var_num;
		    if (sense_in_queue[tmpvar] == -1)
            {
            	/*if (uc_count==tries)
            	{
            		tmplit.sense = 1-tmplit.sense;
            	}*/
            	
		        unit_clause_priority_queue.push(tmplit);
		        sense_in_queue[tmpvar] = tmplit.sense;
		        
		        //uc_count++;
		    }
		    else
		    {
		        if (sense_in_queue[tmpvar]!=tmplit.sense)
		            fix[tmpvar]=-2;//mark this var to be forbidden to assign
		    }
         }
	}	
    
    //unassigned_count = num_vars;
    
    unit_propagation();
    
    /*while (unassigned_count>0)
    {
    	if (unit_clause_priority_queue.empty()!=true)
    	{
    		unit_propagation();
    	}
    	else {
    		as_var = unassigned_var[rand()%unassigned_count];
    		as_sense = rand()%2;
    		assign(as_var, as_sense);
    	}
    }*/

}


/*
int process_time;

void output_init_solution(char *filename)
{
	ofstream initFile(filename);
	
	process_time=get_runtime();
	initFile<<process_time<<' ';
	
    for (int i=1; i<=num_vars; i++) {
    	if (cur_soln[i]==0 || cur_soln[i]==1)
    	{
    		initFile<<cur_soln[i]<<' ';
    	}
    	else initFile<<"2"<<' ';
    }
    initFile.close();
}
*/


