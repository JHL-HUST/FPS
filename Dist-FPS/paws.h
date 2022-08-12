#include "basis_pms.h"
#include "pms.h"



/*
void set_weighting_parameters()
{
	rwprob=0.1;
	large_clause_count_threshold=0;
	
	if(num_vars<=2000) {
		smooth_probability=0.01;
	}
	
	else {
    	smooth_probability=0.001;
    }
	
    /*if(num_vars<=1000) {
    	large_clause_count_threshold=1; smooth_probability=0.01;
    	rwprob=0.01;
    }
    else if(num_vars<=2000) {
    	large_clause_count_threshold=5; smooth_probability=0.002;
    }
    else if(num_vars<=2500) {
    	large_clause_count_threshold=10; smooth_probability=0.0001;
    }
    else{
    	large_clause_count_threshold=10; smooth_probability=0.00001;
    	rwprob=0.2;
    }*/
    
//}


void inc_hclause_weights()
{
	int i,c,v;
    
    for(i=0; i < hardunsat_stack_fill_pointer; ++i)
    {
        c=hardunsat_stack[i];
		clause_weight[c]++;
        
        if(clause_weight[c] == 2)
			large_weight_clauses[large_weight_clauses_count++] = c;
		
        
        for(lit* p=clause_lit[c]; (v=p->var_num)!=0; p++)
		{
			hscore[v]++;
            if (hscore[v]==1 || (hscore[v]==0 && sscore[v]>0 ))           
            {
                if (already_in_goodvar_stack[v]==0)
                {
                    mypush(v,goodvar_stack);
                    already_in_goodvar_stack[v] = 1;
                }
            }
		}
    }

}


void smooth_hclause_weights()
{
	int i, clause, v;
    int dec_count=0;
	for(i=0; i<large_weight_clauses_count; i++)
	{
		clause = large_weight_clauses[i];
		if(sat_count[clause]>0)
		{
			clause_weight[clause]--;
            dec_count++;
            
			if(clause_weight[clause]==1)
			{
				large_weight_clauses[i] = large_weight_clauses[--large_weight_clauses_count];
				i--;
			}
			if(sat_count[clause] == 1)
			{
				v = sat_var[clause];
				hscore[v]++;
                if (hscore[v]>0 || (hscore[v]==0 && sscore[v]>0) )           
                {
                    if (already_in_goodvar_stack[v]==0)
                    {
                        mypush(v,goodvar_stack);
                        already_in_goodvar_stack[v] = 1;
                    }
                }
			}
		}
	}
}


void update_hclause_weights()
{
	
	if( ((rand()%MY_RAND_MAX_INT)*BASIC_SCALE)<smooth_probability 
       && large_weight_clauses_count>large_clause_count_threshold  )
	{
		smooth_hclause_weights();
	}
	else 
	{
		inc_hclause_weights();
	}
}
