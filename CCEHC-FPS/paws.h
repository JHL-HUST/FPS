#include "basis_wpms.h"
#include "wpms.h"

float pacprob;

void set_weighting_parameters()
{
	if(probtype==UNWEIGHTED)
	{
		smooth_probability = 0.0001;
		large_clause_count_threshold = 10;
		pacprob = 0.01;
	}
	else if(probtype==WEIGHTED)
	{
		smooth_probability = 0.0001;
		large_clause_count_threshold = 10;
		pacprob = 0.01;
	}
	else if(probtype==UNWEIGHTED_PARTIAL)
	{
		if(num_vars<=500)
		{
			large_clause_count_threshold=5; smooth_probability=0.01;
			rwprob=0.01;
			pacprob = 0.01;
		}
		else if(num_vars<=1000) {
			large_clause_count_threshold=5; smooth_probability=0.01;
			rwprob=0.01;
			pacprob = 0.005;
		}
		else if(num_vars<=5000) {
			large_clause_count_threshold=10; smooth_probability=0.0001;
			pacprob = 0.01;
		}
		else if(num_vars<=10000) {
			large_clause_count_threshold=10; smooth_probability=0.001;
			pacprob = 0.01;
		}
		else if(num_vars<=30000) {
			large_clause_count_threshold=10; smooth_probability=0.001;
			pacprob = 0.01;
		}
		else {
			large_clause_count_threshold=10; smooth_probability=0.00001;
			pacprob = 0.01;
		}
	}
	else if(probtype==WEIGHTED_PARTIAL)
	{
		smooth_probability = 0.0001;
		large_clause_count_threshold = 10;
		pacprob = 0.01;
	}
	else
	{
		smooth_probability = 0.0001;
		large_clause_count_threshold = 10;
		pacprob = 0.01;
	}
}
 
/*
void set_weighting_parameters()
{
	if(num_vars<=1000) {
    	large_clause_count_threshold=5; smooth_probability=0.01;
    	rwprob=0.01;
    }
    else if(num_vars<=5000) {
    	large_clause_count_threshold=10; smooth_probability=0.0001;
    }
    else if(num_vars<=10000) {
    	large_clause_count_threshold=10; smooth_probability=0.001;
    }
    else{
    	large_clause_count_threshold=10; smooth_probability=0.00001;
    }
}
*/

/*
//for wpms_crafted
void set_weighting_parameters()
{
	smooth_probability = 0.0001;
	large_clause_count_threshold = 10;
}
*/

/*
//for wpms_industrial and wpms_application
void set_weighting_parameters()
{
	smooth_probability = 0.001;
	large_clause_count_threshold = 10;
}
*/

/*
//for pms_crafted
void set_weighting_parameters()
{
	if(num_vars<=500)
	{
		large_clause_count_threshold=5; smooth_probability=0.01;
    	rwprob=0.01;
    	pacprob = 0.01;
	}
	else if(num_vars<=1000) {
    	large_clause_count_threshold=5; smooth_probability=0.01;
    	rwprob=0.01;
    	pacprob = 0.005;
    }
    else if(num_vars<=5000) {
    	large_clause_count_threshold=10; smooth_probability=0.0001;
    	pacprob = 0.01;
    }
    else if(num_vars<=10000) {
    	large_clause_count_threshold=10; smooth_probability=0.001;
    	pacprob = 0.01;
    }
    else if(num_vars<=30000) {
    	large_clause_count_threshold=10; smooth_probability=0.001;
    	pacprob = 0.01;
    }
    else {
    	large_clause_count_threshold=10; smooth_probability=0.00001;
    	pacprob = 0.01;
    }
}
*/

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
                    push(v,goodvar_stack);
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
                        push(v,goodvar_stack);
                        already_in_goodvar_stack[v] = 1;
                    }
                }
			}
		}
	}
}


void update_hclause_weights()
{
	
	//if( ((rand()%MY_RAND_MAX_INT)*BASIC_SCALE)<smooth_probability 
    //   && large_weight_clauses_count>large_clause_count_threshold  )
	if(((rand()%MY_RAND_MAX_INT)*BASIC_SCALE)<smooth_probability && large_weight_clauses_count>large_clause_count_threshold)
	{
		smooth_hclause_weights();
	}
	else 
	{
		inc_hclause_weights();
	}
}
