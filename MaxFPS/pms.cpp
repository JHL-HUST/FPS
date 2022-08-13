/*
 * This is MaxFPS, which combines SATLike3.0 with FPS, a general strategy for boosting MaxSAT local search solvers
 * Author of FPS: Jiongzhi Zheng, Kun He
 * Author of SATLike3.0: Shaowei Cai, Zhendong Lei
 * Contact: jzzheng@hust.edu.cn
*/


#include "basis_pms.h"
#include "build.h"
#include "pms.h"
#include "heuristic.h"
#include <signal.h>


MaxFPS s;
void interrupt(int sig)
{
	s.print_best_solution();
	s.free_memory();
	exit(10);
}

int main(int argc, char *argv[])
{
	start_timing();

	signal(SIGTERM, interrupt);

	s.build_instance(argv[1]);

	s.settings();

	s.local_search_with_decimation(argv[1]);

	s.simple_print();

	s.free_memory();

	return 0;
}
