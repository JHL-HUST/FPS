#ifndef _BASIS_PMS_H_
#define _BASIS_PMS_H_

#include <iostream>
#include <fstream>
#include <cstdlib>
#include <cmath>
#include <cstring>
#include <queue>

#include <stdlib.h>
#include <sys/times.h> //these two h files are for timing in linux
#include <unistd.h>

using namespace std;

/* limits on the size of the problem. */
#define MAX_VARS    1000000
#define MAX_CLAUSES 20000000
#define LONG_LONG_MIN -9223372036854775807

#define mypop(stack) stack[--stack ## _fill_pointer]
#define mypush(item, stack) stack[stack ## _fill_pointer++] = item


const float       MY_RAND_MAX_FLOAT = 10000000.0;
const int   	  MY_RAND_MAX_INT =   10000000;
const float 	  BASIC_SCALE = 0.0000001; //1.0f/MY_RAND_MAX_FLOAT;

int sc_num = 10; //number of sampled clauses
int sv_num = 50; //BMS parameter for selecting the second-level variable
int selected_nums;

// Define a data structure for a literal.
struct lit {
    int             clause_num;		//clause num, begin with 0
    int             var_num;		//variable num, begin with 1
    bool             sense;			//is 1 for true literals, 0 for false literals.
};

/***********non-algorithmic information ****************/
int problem_weighted=1;
int partial=1; //1 if the instance has hard clauses, and 0 otherwise.

int max_clause_length=0;
int min_clause_length=100000000;

//size of the instance
int     num_vars;		//var index from 1 to num_vars
int     num_clauses;		//clause index from 0 to num_clauses-1
int     num_hclauses;
int     num_sclauses;

//steps and time
int tries=0;
int max_tries = 100000000;
unsigned int max_flips = 200000000;
unsigned int step;


int print_time=240;
int cutoff_time=300;
int prioup_time;
double  opt_time;

struct tms start, stop;

/**********end non-algorithmic information*****************/



/* literal arrays */				
lit*	var_lit[MAX_VARS];				//var_lit[i][j] means the j'th literal of var i.
int		var_lit_count[MAX_VARS];			//amount of literals of each var
lit*	clause_lit[MAX_CLAUSES];			//clause_lit[i][j] means the j'th literal of clause i.
int		clause_lit_count[MAX_CLAUSES]; 			// amount of literals in each clause


/* Information about the variables. */
int     hscore[MAX_VARS];
int     sscore[MAX_VARS];

//int		conf_change[MAX_VARS];
int*	var_neighbor[MAX_VARS];
int		var_neighbor_count[MAX_VARS];
long	time_stamp[MAX_VARS];


/* Information about the clauses */		
long long     top_clause_weight;
long long     org_clause_weight[MAX_CLAUSES];	
long long     total_soft_weight;
int     clause_weight[MAX_CLAUSES];		
int     sat_count[MAX_CLAUSES];			
int		sat_var[MAX_CLAUSES];		

//unsat clauses stack
int		hardunsat_stack[MAX_CLAUSES];		//store the unsat clause number
int		hardunsat_stack_fill_pointer;
int		index_in_hardunsat_stack[MAX_CLAUSES];//which position is a clause in the unsat_stack

int		softunsat_stack[MAX_CLAUSES];		//store the unsat clause number
int		softunsat_stack_fill_pointer;
int		index_in_softunsat_stack[MAX_CLAUSES];//which position is a clause in the unsat_stack


//variables in unsat clauses
int		unsatvar_stack[MAX_VARS];		
int		unsatvar_stack_fill_pointer;
int		index_in_unsatvar_stack[MAX_VARS];
int		unsat_app_count[MAX_VARS];		//a varible appears in how many unsat clauses

//configuratio changed decreasing variables (dscore>0 and confchange=1)
int		goodvar_stack[MAX_VARS];		
int		goodvar_stack_fill_pointer;
bool	already_in_goodvar_stack[MAX_VARS];

int   goodvar_stack2[MAX_VARS];		
int   goodvar_stack2_num;
int     hscore2[MAX_VARS];
int     sscore2[MAX_VARS];

int   selected[MAX_VARS]; 
int   best_vars[11]; 
int   sel_cs[11]; 
int   vars2[11]; 
long long   hscores[11]; 
long long   sscores[11]; 

/* Information about solution */
int		fix[MAX_VARS]; //partial assignment fixed by PrioUP procedure
int     cur_soln[MAX_VARS];	//the current solution, with 1's for True variables, and 0's for False variables
int     best_soln[MAX_VARS];
int     best_soln_feasible; //when find a feasible solution, this is marked as 1.


int     hard_unsat_nb;
long long    soft_unsat_weight;
long long    opt_unsat_weight;


//clause weighting 
int    large_weight_clauses[MAX_CLAUSES];
int    large_weight_clauses_count;	
int    large_clause_count_threshold=0;
float  smooth_probability;


bool call_pre_assign = false;


void build_neighbor_relation();

void build_instance(char *filename)
{
	char    line[10241];
	char    tempstr1[10];
	char    tempstr2[10];
	int     cur_lit;
	int     i,v,c;
    int     temp_lit[MAX_VARS];
	
	ifstream infile(filename);
	//if(infile==NULL) 
  //  {
	//	cout<<"c the input filename "<<filename<<" is invalid, please input the correct filename."<<endl;
	//	exit(-1);
	//}
    
	/*** build problem data structures of the instance ***/
	infile.getline(line,10240);
	while (line[0] != 'p')
		infile.getline(line,10240);
    
    int read_items;
    
	read_items=sscanf(line, "%s %s %d %d %lld", tempstr1, tempstr2, &num_vars, &num_clauses, &top_clause_weight);
    
    if(read_items<5)
    {
    	if(strcmp(tempstr2,"cnf")==0) 
		{
			cout<<"c this is an unweighted MaxSAT instance."<<endl;
			problem_weighted=0;
		}
		else cout<<"c this is a non-partial weighted MaxSAT instance."<<endl;
		
		partial = 0;
		top_clause_weight=-1;
	}
	else if (read_items==5) cout<<"c this is a partial (weighted) MaxSAT instance."<<endl;
	
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
	

	for (c = 0; c < num_clauses; c++) 
	{
		clause_lit_count[c] = 0;
		clause_lit[i]=NULL;
	}
	for (v=1; v<=num_vars; ++v)
	{
		var_lit_count[v] = 0;
		var_lit[v]=NULL;
		var_neighbor[v]=NULL;
	}
    
    num_hclauses=num_sclauses=0;
	//Now, read the clauses, one at a time.
	//int lit_redundent,clause_redundent;
	for (c = 0; c < num_clauses; ) 
	{
		//clause_redundent=0;
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
            
			/*lit_redundent=0;
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
			}*/
			
			//if(lit_redundent==0)
			//{
				temp_lit[clause_lit_count[c]] = cur_lit;
				clause_lit_count[c]++;
			//}
            
			infile>>cur_lit;
		}
		
		//if(clause_redundent==0) //the clause is not tautology
		//{
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
            
            if(clause_lit_count[c]>max_clause_length) max_clause_length=clause_lit_count[c];
			if(clause_lit_count[c]<min_clause_length) min_clause_length=clause_lit_count[c];
            
			c++;
		//}
		/*else 
		{
			num_clauses--;
			clause_lit_count[c] = 0;
		}*/
		
		
        
	}
	infile.close();
	
	//cout<<"maxlen="<<max_clause_length<<", minlen="<<min_clause_length<<endl;
	
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
    
}




int	neighbor_flag[MAX_VARS];
int temp_neighbor[MAX_VARS];
int temp_neighbor_count;
void build_neighbor_relation()
{
	int	i,j,count;
	int v,c,n;
    
	for(v=1; v<=num_vars; ++v)
	{
		neighbor_flag[v] = 1;
		temp_neighbor_count = 0;
		
		for(i=0; i<var_lit_count[v]; ++i)
		{
			c = var_lit[v][i].clause_num;
			for(j=0; j<clause_lit_count[c]; ++j)
			{
                n=clause_lit[c][j].var_num;
				if(neighbor_flag[n]!=1)
				{
					neighbor_flag[n] = 1;
					temp_neighbor[temp_neighbor_count++] = n;
				}
			}
		}
        
		neighbor_flag[v] = 0;
        
		var_neighbor[v] = new int[temp_neighbor_count];
		var_neighbor_count[v]=temp_neighbor_count;
        
		count = 0;
		for(i=0; i<temp_neighbor_count; i++)
		{
			var_neighbor[v][count++] = temp_neighbor[i];
			neighbor_flag[temp_neighbor[i]] = 0;
		}
		
	}
	
}


void free_memory()
{
	int i;
	for (i = 0; i < num_clauses; i++) 
		delete[] clause_lit[i];
	
	for(i=1; i<=num_vars; ++i)
	{
		delete[] var_lit[i];
		delete[] var_neighbor[i];
	}
	
}


/*the following functions are non-algorithmic*/

double get_runtime()
{
    times(&stop);
    return (double)(stop.tms_utime - start.tms_utime +stop.tms_stime - start.tms_stime) / sysconf(_SC_CLK_TCK);
}

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
                cout<<"c Error: hard clause "<<c<<" is not satisfied"<<endl;
                
                cout<<"c ";
                for(j=0; j<clause_lit_count[c]; ++j)
                {
                    if(clause_lit[c][j].sense==0)cout<<"-";
                    cout<<clause_lit[c][j].var_num<<" ";
                }
                cout<<endl;
                
                cout<<"c ";
                for(j=0; j<clause_lit_count[c]; ++j)
                    cout<<best_soln[clause_lit[c][j].var_num]<<" ";
                cout<<endl;
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
    	cout<<"c Error: find opt="<<opt_unsat_weight<<", but verified opt="<<verify_unsat_weight<<endl;
    }
    
    return 0;
}


#endif

