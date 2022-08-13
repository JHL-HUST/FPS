#ifndef _BASIS_PMS_H_
#define _BASIS_PMS_H_

#include <iostream>
#include <fstream>
#include <cstdlib>
#include <cmath>
#include <cstring>
#include <string>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/times.h> //these two h files are for timing in linux
#include <unistd.h>

using namespace std;

/* limits on the size of the problem. */
//#define MAX_VARS    1000000
//#define MAX_CLAUSES 10000000

#define pop(stack) stack[--stack ## _fill_pointer]
#define push(item, stack) stack[stack ## _fill_pointer++] = item
#define LONG_LONG_MIN -9223372036854775807

int sc_num = 10; //number of sampled clauses
int sv_num = 50; //BMS parameter for selecting the second-level variable
int selected_nums;

const float       MY_RAND_MAX_FLOAT = 10000000.0;
const int   	  MY_RAND_MAX_INT =   10000000;
const float 	BASIC_SCALE = 0.0000001; //1.0f/MY_RAND_MAX_FLOAT;

// Define a data structure for a literal in the SAT problem.
struct lit {
    int             clause_num;		//clause num, begin with 0
    int             var_num;		//variable num, begin with 1
    int             sense;			//is 1 for true literals, 0 for false literals.
};

enum PROBLEMTYPE {NONE, WEIGHTED, UNWEIGHTED, UNWEIGHTED_PARTIAL, WEIGHTED_PARTIAL};
enum PROBLEMTYPE probtype;

/*parameters of the instance*/
int     num_vars;		//var index from 1 to num_vars
int     num_clauses;		//clause index from 0 to num_clauses-1

int     num_hclauses;
int     num_sclauses;

/* literal arrays */				
lit**	var_lit;				//var_lit[i][j] means the j'th literal of var i.
int*	var_lit_count;			//amount of literals of each var
lit**	clause_lit;			//clause_lit[i][j] means the j'th literal of clause i.
int*	clause_lit_count; 			// amount of literals in each clause				

/* Information about the variables. */
long long*    hscore;
long long*    sscore;

int*	conf_change;
int**	var_neighbor;
int*	var_neighbor_count;
long long*	time_stamp;
int*	neighbor_flag;
int* temp_neighbor;
int temp_neighbor_count;

/* Hard clause states based on configuration checking */
int*	hard_cscc;
int*	is_hard_clause;


/* Information about the clauses */		
long long     top_clause_weight;
long long*    org_clause_weight;	
long long     total_soft_weight;
long long*    clause_weight;		
int*    sat_count;			
int*	sat_var;		

//unsat clauses stack
int*	hardunsat_stack;		//store the unsat clause number
int		hardunsat_stack_fill_pointer;
int*	index_in_hardunsat_stack;//which position is a clause in the unsat_stack

int*	softunsat_stack;		//store the unsat clause number
int		softunsat_stack_fill_pointer;
int*	index_in_softunsat_stack;//which position is a clause in the unsat_stack


int*   selected; 
int*   best_vars; 
int*   sel_cs; 
int*   vars2; 
long long*   hscores; 
long long*   sscores; 
//int*   conf_change2;
//int*   hard_cscc2;

long long*   hscore2; 
long long*   sscore2; 
int*	goodvar_stack2;		
int	goodvar_stack2_num;	

//variables in unsat clauses
//int*	unsatvar_stack;		
//int		unsatvar_stack_fill_pointer;
//int*	index_in_unsatvar_stack;
//int*	unsat_app_count;		//a varible appears in how many unsat clauses

//configuratio changed decreasing variables (dscore>0 and confchange=1)
int*	goodvar_stack;		
int		goodvar_stack_fill_pointer;
int*	already_in_goodvar_stack;

/* Information about solution */
int*    cur_soln;	//the current solution, with 1's for True variables, and 0's for False variables
int*    best_soln;
int     best_soln_feasible; //when find a feasible solution, this is marked as 1.

int     hard_unsat_nb;
long long     soft_unsat_weight;
long long     opt_unsat_weight;
double  opt_time;
//int     instance_optimal;

//steps and time
int max_tries = 1000;
unsigned int max_flips = 4000000000u;
unsigned int step;

struct tms start, stop;

float rwprob;

int* best_array;
int best_count;
unsigned int* already_in_ccmpvars;
int* ccmpvars;
int ccmpvars_count;

int* temp_lit;

int*   large_weight_clauses;
int    large_weight_clauses_count=0;	
int    large_clause_count_threshold;

float  smooth_probability;


void build_neighbor_relation();

int problem_weighted=1;


void allocate_memory()
{
	int malloc_var_length = num_vars+10;
	int malloc_clause_length = num_clauses+10;
	
	var_lit = new lit* [malloc_var_length];
	var_lit_count = new int [malloc_var_length];
	hard_cscc = new int [malloc_var_length];
	hscore = new long long [malloc_var_length];
	sscore = new long long [malloc_var_length];
	conf_change = new int [malloc_var_length];
	var_neighbor = new int* [malloc_var_length];
	var_neighbor_count = new int [malloc_var_length];
	time_stamp = new long long [malloc_var_length];
	neighbor_flag = new int [malloc_var_length];
	temp_neighbor = new int [malloc_var_length];
	//unsatvar_stack = new int [malloc_var_length];
	//index_in_unsatvar_stack = new int [malloc_var_length];
	//unsat_app_count = new int [malloc_var_length];
	goodvar_stack = new int [malloc_var_length];
	already_in_goodvar_stack = new int [malloc_var_length];
	cur_soln = new int [malloc_var_length];
	best_soln = new int [malloc_var_length];
	best_array = new int [malloc_var_length];
	already_in_ccmpvars = new unsigned int [malloc_var_length];
	ccmpvars = new int [malloc_var_length];
	temp_lit = new int [malloc_var_length];
	
	clause_lit = new lit* [malloc_clause_length];
	clause_lit_count = new int [malloc_clause_length];
	is_hard_clause = new int [malloc_clause_length];
	org_clause_weight = new long long [malloc_clause_length];
	clause_weight = new long long [malloc_clause_length];
	sat_count = new int [malloc_clause_length];
	sat_var = new int [malloc_clause_length];
	hardunsat_stack = new int [malloc_clause_length];
	index_in_hardunsat_stack = new int [malloc_clause_length];
	softunsat_stack = new int [malloc_clause_length];
	index_in_softunsat_stack = new int [malloc_clause_length];
	large_weight_clauses = new int [malloc_clause_length];
 
  //conf_change2 = new int [malloc_var_length];
  //hard_cscc2 = new int [malloc_var_length];
  selected = new int [malloc_var_length];
  best_vars = new int [sc_num + 10];
  sel_cs = new int [sc_num + 10];
  vars2 = new int [sc_num + 10]; 
  hscores = new long long [sc_num + 10]; 
  sscores = new long long [sc_num + 10]; 
  
  hscore2 = new long long [malloc_var_length];
  sscore2 = new long long [malloc_var_length]; 
  goodvar_stack2 = new int [malloc_var_length];
}

void free_memory()
{
	int i;
	
	for(i=1; i<=num_vars; ++i)
	{
		delete[] var_lit[i];
		delete[] var_neighbor[i];
	}
	
	delete [] var_lit;
	delete [] var_lit_count;
	delete [] hscore;
	delete [] sscore;
	delete [] conf_change;
	delete [] var_neighbor;
	delete [] var_neighbor_count;
	delete [] time_stamp;
	delete [] neighbor_flag;
	delete [] temp_neighbor;
	//delete [] unsatvar_stack;
	//delete [] index_in_unsatvar_stack;
	//delete [] unsat_app_count;
	delete [] goodvar_stack;
	delete [] already_in_goodvar_stack;
	delete [] cur_soln;
	delete [] best_soln;
	delete [] best_array;
	delete [] already_in_ccmpvars;
	delete [] ccmpvars;
	delete [] temp_lit;
	
	for (i = 0; i < num_clauses; i++) 
	{
		delete[] clause_lit[i];
	}
	
	delete [] clause_lit;
	delete [] clause_lit_count;
	delete [] hard_cscc;
	delete [] is_hard_clause;
	delete [] org_clause_weight;
	delete [] clause_weight;
	delete [] sat_count;
	delete [] sat_var;
	delete [] hardunsat_stack;
	delete [] index_in_hardunsat_stack;
	delete [] softunsat_stack;
	delete [] index_in_softunsat_stack;
	delete [] large_weight_clauses;
 
 
  //delete [] conf_change2;
  //delete [] hard_cscc2;
  delete [] selected; 
  delete [] best_vars; 
  delete [] sel_cs; 
  delete [] vars2; 
  delete [] hscores; 
  delete [] sscores; 
  
  delete [] hscore2;
  delete [] sscore2;
  delete [] goodvar_stack2;
}

void build_instance(char *filename)
{
	char    line[102411];
	char    tempstr1[102411];
	char    tempstr2[102411];
	int     cur_lit;
	int     i,v,c;
    
    times(&start);
	
	ifstream infile(filename);
	if(!infile.is_open()) 
    {
		//cout<<"c the input filename "<<filename<<" is invalid, please input the correct filename."<<endl;
		printf("c the input filename %s is invalid, please input the correct filename.\n", filename);
		fflush(stdout);
		exit(-1);
	}
    
	/*** build problem data structures of the instance ***/
	infile.getline(line,102410);
	while (line[0] != 'p')
		infile.getline(line,102410);
    
    int read_items;
    
	read_items=sscanf(line, "%s %s %d %d %lld", tempstr1, tempstr2, &num_vars, &num_clauses, &top_clause_weight);
    
    probtype = NONE;
    
    if(read_items<5)
    {
    	if(strcmp(tempstr2,"cnf")==0) 
		{
			//cout<<"c this is an unweighted MaxSAT instance."<<endl;
			//printf("c Unweighted MAX-SAT instance\n");
			//fflush(stdout);
			probtype = UNWEIGHTED;
			problem_weighted=0;
		}
		else 
		{
			//printf("c Non-partial Weighted MAX-SAT instance\n");
			//fflush(stdout);
			probtype = WEIGHTED;
		}
		
		top_clause_weight=-1;
	}
	/*
	else if (read_items==5) 
	{
		printf("c Partial (weighted) MAX-SAT instance\n");
		fflush(stdout);
	}
	*/
	
	allocate_memory();
	
	/*
	if(num_vars>=MAX_VARS)
	{
		cout<<"c the number of variables exceeds MAX_VARS, please enlarge MAX_VARS."<<endl;
		exit(-1);
	}
	if( num_clauses>=MAX_CLAUSES)
	{
		cout<<"c the number of clauses exceeds MAX_CLAUSES, please enlarge MAX_CLAUSES."<<endl;
		exit(-1);
	}
	*/
	
	for (v=1; v<=num_vars; ++v)
		var_lit_count[v] = 0;
    
    num_hclauses=num_sclauses=0;
	//Now, read the clauses, one at a time.
	int lit_redundent,clause_redundent;
	for (c = 0; c < num_clauses; ) 
	{
		clause_redundent=0;
        clause_lit_count[c] = 0;
        
        if (problem_weighted!=0) 
        	infile>>org_clause_weight[c];
        else org_clause_weight[c]=1;
        
        if (org_clause_weight[c]!=top_clause_weight) 
        {
            total_soft_weight += org_clause_weight[c];
            num_sclauses++;
        }
        else num_hclauses++;
		
		infile>>cur_lit;
		while (cur_lit != 0) { 
            
			lit_redundent=0;
			for(int p=0; p<clause_lit_count[c]; p++)
			{
				if(cur_lit==temp_lit[p]){
					lit_redundent=1;
					break;
				}
				else if(cur_lit==-temp_lit[p]){
					clause_redundent=1;
					break;
				}
			}
			
			if(lit_redundent==0)
			{
				temp_lit[clause_lit_count[c]] = cur_lit;
				clause_lit_count[c]++;
			}
            
			infile>>cur_lit;
		}
		
		if(clause_redundent==0) //the clause is not tautology
		{
			clause_lit[c] = new lit[clause_lit_count[c]+1];
            
			for(i=0; i<clause_lit_count[c]; ++i)
			{
				clause_lit[c][i].clause_num = c;
				clause_lit[c][i].var_num = abs(temp_lit[i]);
				if (temp_lit[i] > 0) clause_lit[c][i].sense = 1;
                else clause_lit[c][i].sense = 0;
                
				var_lit_count[clause_lit[c][i].var_num]++;
			}
            clause_lit[c][i].var_num=0; 
            clause_lit[c][i].clause_num = -1;
            
            //hcscc
            if(org_clause_weight[c]!=top_clause_weight)
            	is_hard_clause[c] = 0;
            else is_hard_clause[c] = 1;
			//
			
			c++;
		}
		else 
		{
			num_clauses--;
			clause_lit_count[c] = 0;
		}
        
	}
	infile.close();
	
	//creat var literal arrays
	for (v=1; v<=num_vars; ++v)
	{
    selected[v] = 0;
		var_lit[v] = new lit[var_lit_count[v]+1];
		var_lit_count[v] = 0;	//reset to 0, for build up the array
	}
	//scan all clauses to build up var literal arrays
	for (c = 0; c < num_clauses; ++c) 
	{
		for(i=0; i<clause_lit_count[c]; ++i)
		{
			v = clause_lit[c][i].var_num;
			var_lit[v][var_lit_count[v]] = clause_lit[c][i];
			++var_lit_count[v];
		}
	}
    for (v=1; v<=num_vars; ++v)
		var_lit[v][var_lit_count[v]].clause_num=-1;
        

	build_neighbor_relation();
    
    best_soln_feasible=0;
    opt_unsat_weight=total_soft_weight+1;
    
    
    //judge this is unweighted partial instance or weighted partial instance
    if(probtype==NONE)
    {
    	int flag_tmp=0;
    	long long org_soft_clause_weight_tmp;
    	for(c=0; c<num_clauses; c++)
    	{
    		if(is_hard_clause[c]==0)
    		{
    			org_soft_clause_weight_tmp = org_clause_weight[c];
    			break;
    		}
    	}
    	
    	for(c++; c<num_clauses; c++)
    	{
    		if(is_hard_clause[c]==0)
    		{
    			if(org_clause_weight[c]!=org_soft_clause_weight_tmp)
    			{
    				flag_tmp = 1;
    				break;
    			}
    		}
    	}
    	
    	if(flag_tmp==0) probtype = UNWEIGHTED_PARTIAL;
    	else probtype = WEIGHTED_PARTIAL;
    }
}

void build_neighbor_relation()
{
	int		i,j,count;
	int 	v,c;

	for(v=1; v<=num_vars; ++v)
	{
		neighbor_flag[v] = 0;
	}
	neighbor_flag[0] = 0;

	for(v=1; v<=num_vars; ++v)
	{
		var_neighbor_count[v] = 0;
		//for(i=1; i<=num_vars; ++i)
		//	neighbor_flag[i] = 0;
		neighbor_flag[v] = 1;
		temp_neighbor_count = 0;
		for(i=0; i<var_lit_count[v]; ++i)
		{
			c = var_lit[v][i].clause_num;
			for(j=0; j<clause_lit_count[c]; ++j)
			{
				if(neighbor_flag[clause_lit[c][j].var_num]==0)
				{
					var_neighbor_count[v]++;
					neighbor_flag[clause_lit[c][j].var_num] = 1;
					temp_neighbor[temp_neighbor_count++] = clause_lit[c][j].var_num;
				}
			}
			
		}

		neighbor_flag[v] = 0;
 
		var_neighbor[v] = new int[var_neighbor_count[v]+1];

		count = 0;
		for(i=0; i<temp_neighbor_count; i++)
		{
			var_neighbor[v][count++] = temp_neighbor[i];
			neighbor_flag[temp_neighbor[i]] = 0;
		}
		/*
		for(i=1; i<=num_vars; ++i)
		{
			if(neighbor_flag[i]==1)
			{
				var_neighbor[v][count] = i;
				count++;
			}
		}
		*/
		var_neighbor[v][count]=0;
		var_neighbor_count[v] = count;
	}
}



/*the following functions are non-algorithmic*/

double get_runtime()
{
    times(&stop);
    return (double)(stop.tms_utime - start.tms_utime +stop.tms_stime - start.tms_stime) / sysconf(_SC_CLK_TCK);
}

/*
void print_best_solution()
{
	if (best_soln_feasible==0) return;
	
    cout<<"v";
    for (int i=1; i<=num_vars; i++) {
    	cout<<' ';
		if(best_soln[i]==0) cout<<"-";
		cout<<i;
    }
    cout<<endl;
}
*/

void print_best_solution()
{
	if (best_soln_feasible==0) return;
	/*
    printf("v");
    for (int i=1; i<=num_vars; i++) {
    	printf(" ");
		if(best_soln[i]==0) printf("-");
		printf("%d", i);
    }
    printf("\n");
    fflush(stdout);
  */
}


int verify_sol()
{        
	int c,j,flag;
    long long verify_unsat_weight=0;
    
	for (c = 0; c<num_clauses; ++c) 
	{
        flag = 0;
        for(j=0; j<clause_lit_count[c]; ++j)
            if (best_soln[clause_lit[c][j].var_num] == clause_lit[c][j].sense) {flag = 1; break;}
        
        if(flag ==0)
        {
            if(org_clause_weight[c]==top_clause_weight)//verify hard clauses
            {
                //output the clause unsatisfied by the solution
                //cout<<"c Error: hard clause "<<c<<" is not satisfied"<<endl;
                printf("c Error: hard clause %d is not satisfied\n", c);
                
                //cout<<"c ";
                printf("c ");
                for(j=0; j<clause_lit_count[c]; ++j)
                {
                    if(clause_lit[c][j].sense==0) printf("-");
                    printf("%d ", clause_lit[c][j].var_num);
                }
                printf("\n");
                
                printf("c ");
                for(j=0; j<clause_lit_count[c]; ++j)
                	printf("%d ", best_soln[clause_lit[c][j].var_num]);
                printf("\n");
                fflush(stdout);
                return 0;
            }
            else
            {
                verify_unsat_weight+=org_clause_weight[c];
            }
        }
    }
    
    if(verify_unsat_weight==opt_unsat_weight)  return 1;
    else{
    	//cout<<"c Error: find opt="<<opt_unsat_weight<<", but verified opt="<<verify_unsat_weight<<endl;
    	printf("c Error: find opt=%lld, but verified opt=%lld", opt_unsat_weight, verify_unsat_weight);
    	fflush(stdout);
    }
    
    return 0;
}


#endif

