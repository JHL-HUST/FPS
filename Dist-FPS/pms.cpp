#include "basis_pms.h"
#include "pms.h"
#include "paws.h"
#include "prioup.h"

int best_array[MAX_VARS];
int best_count;


float rwprob;
float rdprob;
int hd_count_threshold;

int pick_var()
{
	int     i,v;
	int     best_var;
    
	//if(goodvar_stack_fill_pointer>0 )
	//{
		if( (rand()%MY_RAND_MAX_INT)*BASIC_SCALE< rdprob ) 
            return goodvar_stack[rand()%goodvar_stack_fill_pointer]; 
            
        best_count=0;
        
        for(i=0; i<goodvar_stack_fill_pointer; ++i)
		{
			v = goodvar_stack[i];
            
            if(hscore[v]>0)
            {
                best_array[best_count]=v;
                best_count++;
            }
        }
        
        if (best_count>0)
        {
            	if (best_count < hd_count_threshold)
            	{
		            best_var = best_array[0];
		            for (i=1; i<best_count; ++i) 
		            {
		                v = best_array[i];
		                if (hscore[v]>hscore[best_var]) best_var=v;
		                else if (hscore[v]==hscore[best_var])
		                {   
		                    if (sscore[v]>sscore[best_var]) best_var=v;
		                    else if (sscore[v]==sscore[best_var] && time_stamp[v]<time_stamp[best_var]) best_var=v;
		                } 
		            }
		            return best_var;
                }
                else{
		            best_var = best_array[rand()%best_count];
		            for (i=1; i<hd_count_threshold; ++i) 
		            {
		                v = best_array[rand()%best_count];
		                if (hscore[v]>hscore[best_var]) best_var=v;
		                else if (hscore[v]==hscore[best_var])
		                {   
		                    if (sscore[v]>sscore[best_var]) best_var=v;
		                    else if (sscore[v]==sscore[best_var] && time_stamp[v]<time_stamp[best_var]) best_var=v;
		                } 
		            }
		            return best_var;
                }
        }
        
        best_array[0] = goodvar_stack[0];
        int best_sscore = sscore[goodvar_stack[0]];
        best_count=1;

        for(i=1; i<goodvar_stack_fill_pointer; ++i)
		{
			v = goodvar_stack[i];
            if (sscore[v]>best_sscore)
            {
                best_sscore = sscore[v];
                best_array[0] = v;
                best_count = 1;
            }
            else if (sscore[v]==best_sscore)
            {
                best_array[best_count] = v;
                best_count++;
            }
        }
        if (best_count==1) return best_array[0];
        else return best_array[rand()%best_count];

	//}

    update_hclause_weights();
    
    int sel_c;    
    lit* p;
    
    if (hardunsat_stack_fill_pointer>0) sel_c = hardunsat_stack[rand()%hardunsat_stack_fill_pointer]; 
    else sel_c= softunsat_stack[rand()%softunsat_stack_fill_pointer];
    
    if( (rand()%MY_RAND_MAX_INT)*BASIC_SCALE< rwprob )  
        return clause_lit[sel_c][rand()%clause_lit_count[sel_c]].var_num;

    best_var = clause_lit[sel_c][0].var_num;
    
    p=clause_lit[sel_c];
	for(p++; (v=p->var_num)!=0; p++)  
    {           
        if (sscore[v]>sscore[best_var]) 
            best_var=v;
        else if (sscore[v]==sscore[best_var])
        {
            if (hscore[v]>hscore[best_var]) best_var=v;
            else if (hscore[v]==hscore[best_var] && time_stamp[v]<time_stamp[best_var]) best_var=v;
        }
    }
    
    return best_var;

}


void pick_vars(){
    
    int i,v;
    
    if ((rand() % MY_RAND_MAX_INT) * BASIC_SCALE < rwprob){
        update_hclause_weights();
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
        step++;
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
        update_hclause_weights();
        flip(best_vars[0]);
        time_stamp[best_vars[0]]=step;
        step++;
        return;
    }

    long long max_score1 = LONG_LONG_MIN, max_score2 = LONG_LONG_MIN;
    int num1, num2;
    
    for (i = 0; i < selected_nums; i++)
    {
        hscores[i] = hscore[best_vars[i]];
        sscores[i] = sscore[best_vars[i]];
        if (sscore[best_vars[i]] > max_score1){
            max_score1 = sscore[best_vars[i]]; num1 = i;
        }
        else if (sscore[best_vars[i]] == max_score1){
            if (hscore[best_vars[i]] > hscore[best_vars[num1]])
                num1 = i;
            else if (hscore[best_vars[i]] == hscore[best_vars[num1]]){
                if (time_stamp[best_vars[i]] < time_stamp[best_vars[num1]])
                    num1 = i;
            }
        }
    }
    
    int j;
    
    
    
    for (i = 0; i < selected_nums; i++)
    {
        //cout << i << " " << selected_nums << " " << get_runtime() << endl;
        //cout << " 11 " << get_runtime() << endl;
    
        flip2(best_vars[i]);
        if (goodvar_stack2_num > 0){
            best_count = 0;
            for(j=0; j<goodvar_stack2_num; ++j)
        		{
        			  v = goodvar_stack2[i];  
                if(hscore2[v]>0)
                {
                    best_array[best_count]=v;
                    best_count++;
                }
            }
            if (best_count > 0){
                if (best_count < sv_num){
                    vars2[i] = best_array[0];
                    for (j = 1; j < best_count; j++){
                        v = best_array[i];
                        if (hscore2[v] > hscore2[vars2[i]])
                            vars2[i] = v;
                        else if (hscore2[v] == hscore2[vars2[i]]){
                            if (sscore2[v] > sscore2[vars2[i]])
                                vars2[i] = v;
                            else if (sscore2[v] == sscore2[vars2[i]] && time_stamp[v] < time_stamp[vars2[i]])
                                vars2[i] = v;
                        }
                    }
                }
                else{
                    vars2[i] = best_array[rand()%best_count];
                    for (j = 1; j < sv_num; j++){
                        v = best_array[rand()%best_count];
                        if (hscore2[v] > hscore2[vars2[i]])
                            vars2[i] = v;
                        else if (hscore2[v] == hscore2[vars2[i]]){
                            if (sscore2[v] > sscore2[vars2[i]])
                                vars2[i] = v;
                            else if (sscore2[v] == sscore2[vars2[i]] && time_stamp[v] < time_stamp[vars2[i]])
                                vars2[i] = v;
                        }
                    }
                }
            }
            else{
                if (goodvar_stack2_num < sv_num){
                    vars2[i] = goodvar_stack2[0];
                    for (j = 1; j < goodvar_stack2_num; j++){
                        v = goodvar_stack2[i];
                        if (sscore2[v] > sscore2[vars2[i]])
                            vars2[i] = v;
                        else if (sscore2[v] == sscore2[vars2[i]] && rand()%2 == 1)
                            vars2[i] = v;
                    }
                }
                else{
                    vars2[i] = goodvar_stack2[rand()%goodvar_stack2_num];
                    for (j = 1; j < sv_num; j++){
                        v = goodvar_stack2[rand()%goodvar_stack2_num];
                        if (sscore2[v] > sscore2[vars2[i]])
                            vars2[i] = v;
                        else if (sscore2[v] == sscore2[vars2[i]] && rand()%2 == 1)
                            vars2[i] = v;
                    }
                }
            }
            
            hscores[i] += hscore2[vars2[i]];
            sscores[i] += sscore2[vars2[i]];
            if (hscores[i] > 0 || (hscores[i] == 0 && sscores[i] > 0)){
                flip(best_vars[i]);
                flip(vars2[i]);
                time_stamp[best_vars[i]] = step;
                step++;
                time_stamp[vars2[i]] = step;
                step++;
                return;
            }
        }
        else{
            hscores[i] -= 1000;
            sscores[i] -= 1000;
        }
        
        //cout << " 22 " << get_runtime() << endl;
        
        if (sscores[i] > max_score1){
            if (sscores[i] > max_score2){
                max_score2 = sscores[i]; num2 = i;
            }
            else if (sscores[i] == max_score2){
                if (time_stamp[best_vars[i]] + time_stamp[vars2[i]] < time_stamp[best_vars[num2]] + time_stamp[vars2[num2]])
                    num2 = i;
            }
        }
        //flip(best_vars[i]);
        
        //cout << " 33 " << get_runtime() << endl;
    }
    
    //cout << " 33 " << get_runtime() << endl;
    
    update_hclause_weights();
    if (max_score1 >= max_score2){
        flip(best_vars[num1]);
        time_stamp[best_vars[num1]] = step;
        step++;
    }
    else{
        flip(best_vars[num2]); flip(vars2[num2]);
        time_stamp[best_vars[num2]] = step;
        step++;
        time_stamp[vars2[num2]] = step;
        step++;
    }

    return;
}

/*
int pick_var()
{
	int     i,v;
	int     best_var;

	if(goodvar_stack_fill_pointer>0)
	{
        if( (rand()%MY_RAND_MAX_INT)*BASIC_SCALE< rdprob ) 
            return goodvar_stack[rand()%goodvar_stack_fill_pointer]; 
        
		best_var = goodvar_stack[0];
                
		for(i=1; i<goodvar_stack_fill_pointer; ++i)
		{
			v = goodvar_stack[i];
            
            if(hscore[v]<hscore[best_var]) continue;
            else if (hscore[v]>hscore[best_var]) best_var=v;
            else 
            {   
                if (sscore[v]>sscore[best_var]) best_var=v;
                else if (sscore[v]==sscore[best_var] && time_stamp[v]<time_stamp[best_var]) best_var=v;
            } 
		}
		
		return best_var;
	}

    update_hclause_weights();
    

    int sel_c;    
    
    if (hardunsat_stack_fill_pointer>0) sel_c = hardunsat_stack[rand()%hardunsat_stack_fill_pointer];
    else sel_c= softunsat_stack[rand()%softunsat_stack_fill_pointer];
        
    if( (rand()%MY_RAND_MAX_INT)*BASIC_SCALE< rwprob )  
        return clause_lit[sel_c][rand()%clause_lit_count[sel_c]].var_num;

    best_var = clause_lit[sel_c][0].var_num;
    lit* p=clause_lit[sel_c];
	for(p++; (v=p->var_num)!=0; p++)  
    {           
        if (sscore[v]>sscore[best_var]) 
            best_var=v;
        else if (sscore[v]==sscore[best_var])
        {
            if (hscore[v]>hscore[best_var]) best_var=v;
            else if (hscore[v]==hscore[best_var] && time_stamp[v]<time_stamp[best_var]) best_var=v;
        }
    }
    
    return best_var;

}
*/


int print=0;
void local_search_nonpartial(unsigned int max_flips, char* filename)
{
	int flipvar;
    
	for (step = 1; step<max_flips; ++step)
	{
		if (soft_unsat_weight<opt_unsat_weight)
        {
		        best_soln_feasible = 1;
		        opt_unsat_weight = soft_unsat_weight;
		        
				cout<<"o "<<opt_unsat_weight<<endl;
				opt_time = get_runtime(); 
				//cout<<"c run time: "<<get_runtime()<<endl;
		        
		        for(int v=1; v<=num_vars; v++) best_soln[v] = cur_soln[v];

		        if(opt_unsat_weight==0) 
		        {
		            print_best_solution();
		            opt_time = get_runtime();
		            return;
		        }
		        
		        if(print==1) print_best_solution();
        }
		if(goodvar_stack_fill_pointer>0){
  		flipvar = pick_var();
  		flip(flipvar);
  		time_stamp[flipvar] = step;
    }
    else{
      pick_vars();
    }
        if (step%1000==0)
        {
        	double elapse_time=get_runtime();
            if(print==0 && elapse_time>=print_time) 
            {
            	print=1;
            	
            	if(best_soln_feasible == 1)
    				print_best_solution();
            }
            if(elapse_time>=cutoff_time) return;    
        }
	}
    
}


void local_search_partial(unsigned int max_flips, char* filename)
{
	int flipvar;
    step = 1;
    
	//for (step = 1; step<max_flips; ++step)
	//{
 while(1)
 {
 if (step >= max_flips)
     break;
    //cout << "11 " << get_runtime() << endl;
		if (hard_unsat_nb==0 && (soft_unsat_weight<opt_unsat_weight || best_soln_feasible==0) )
        {
        
		    if (soft_unsat_weight<top_clause_weight) 
		    {
		        best_soln_feasible = 1;
		        opt_unsat_weight = soft_unsat_weight;
		        
				cout<<"o "<<opt_unsat_weight<<endl;
				opt_time = get_runtime(); 
				//cout<<"c run time: "<<get_runtime()<<endl;
		        
		        for(int v=1; v<=num_vars; v++) best_soln[v] = cur_soln[v];

		        if(opt_unsat_weight==0) 
		        {
		            print_best_solution();
		            opt_time = get_runtime();
		            return;
		        }
		        
		        if(print==1) print_best_solution();
		       }
        }
		
   //cout << "22 " << get_runtime() << endl;
   
		if(goodvar_stack_fill_pointer>0){
      //cout << "33 " << get_runtime() << endl;
  		flipvar = pick_var();
  		flip(flipvar);
  		time_stamp[flipvar] = step;
     step++;
    }
    else{
      //cout << "44 " << get_runtime() << endl;
      pick_vars();
    }
        //cout << "55 " << get_runtime() << endl;
        if (step%1000==0)
        {
        	double elapse_time=get_runtime();
            if(print==0 && elapse_time>=print_time) 
            {
            	print=1;
            	
            	if(best_soln_feasible == 1)
    				print_best_solution();
            }
            if(elapse_time>=cutoff_time) return;    
        }
    
    //cout << get_runtime() << endl;
    
    //if(get_runtime() > 300) return;
	}
    
}

void (*local_search)(unsigned int max_flips, char* filename);

int seed;

void settings()
{

	if (partial==1) local_search=local_search_partial;
	else local_search = local_search_nonpartial;
	
	rdprob=0.01;
	hd_count_threshold=15;
	rwprob=0.1; 
	smooth_probability=0.01;
	
	call_pre_assign = false;
	

	//settings for random categories
	if (max_clause_length==min_clause_length) 
	{	
		if(max_clause_length==2 || max_clause_length==3)
		{
			rdprob=0.1;
			rwprob=0.1; 
			smooth_probability=0.01;
			return;
		}
	}
	if(min_clause_length==1 && (max_clause_length==3||max_clause_length==4))
	{
		if (top_clause_weight<num_vars && top_clause_weight>num_vars/4 )
		{
			rdprob=0.1;
			rwprob=0.1; 
			smooth_probability=0.01;

			return;
		}
	}
	//end settings for random categories
	
	if(min_clause_length==1 && max_clause_length==2 
		&& top_clause_weight==num_vars) //for maxclique
	{
		rdprob=0.3;
		hd_count_threshold=30;
		rwprob=0.1; 
		smooth_probability=0.01;
		return;
	}
		
	if(num_vars>2000&& num_vars<25000 && top_clause_weight<100) //for reversi
	{
		rdprob=0.01;
		rwprob=0.01; 
		smooth_probability=0.001;
		return;
	}
	
	if (num_vars>2000)// for industrial
	{
		rdprob=0.01;
		hd_count_threshold=15;
		rwprob=0.1; 
		
		//rdprob=0.01;
		//hd_count_threshold=40;
		//rwprob=0.1; 
		smooth_probability=0.0001;
		call_pre_assign = true;
	}

}



int main(int argc, char* argv[])
{
	times(&start);

	//cout<<argv[1]<<'\t';
  cout<<"c This is Dist-FPS, which combines Dist with FPS."<<endl;
  cout<<"c Author of FPS: Jiongzhi Zheng, Kun He."<<endl;
  cout<<"c Author of Dist: Shaowei Cai."<<endl;	

	build_instance(argv[1]);
	
	seed=1;

	settings();
	
	
	//int i=2;
	//sscanf(argv[i++],"%d",&cutoff_time);
	//sscanf(argv[i++],"%d",&seed);
	//sscanf(argv[i++],"%f",&rdprob);
	//sscanf(argv[i++],"%d",&hd_count_threshold);
	//sscanf(argv[i++],"%f",&rwprob);
	//sscanf(argv[i++],"%f",&smooth_probability);

	
	
	srand(seed);

	//call_pre_assign = true;
	if (call_pre_assign)
	{
		max_flips = 100000000;
		pre_assign();
	}

	for (tries=0; tries<max_tries; tries++) 
	{	 
		 init();
		 
		 local_search(max_flips,argv[1]);
     
		 if(opt_unsat_weight==0) break;
		 if(get_runtime()>=cutoff_time) break;
      
     //if(get_runtime()>=300) break;
	}

	cout<<"s UNKNOWN"<<endl;

    if(best_soln_feasible==1)
    {
        if(verify_sol()==1)
        {   
            //print_best_solution();
            cout<<"c instance: "<<argv[1]<<endl;
            cout<<"c best found feasible solution: "<<opt_unsat_weight<<endl;
            cout<<"c search time for best found solution: "<<opt_time<<endl;
            cout<<"c verfied successfully."<<endl;
            //cout<<opt_unsat_weight<<'\t'<<opt_time;
        }
    }
    else {
    
        cout<<"c cannot find a feasible solution."<<endl;
    }
    //cout<<endl;
   
   
	free_memory();

    return 0;
}
