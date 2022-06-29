/*
 * Farsighted Probabilistic Sampling: A General Strategy for Boosting MaxSAT Local Search Solvers
 * Farsighted Probabilistic Sampling (FPS) is implemented on top of SATLike3.0
 * Author of FPS: Jiongzhi Zheng, Kun He, Jianrong Zhou
 * Author of SATLike3.0: Shaowei Cai, Zhendong Lei
 * Contact: jzzheng@hust.edu.cn
*/

#include "basis_pms.h"
#include "build.h"
#include "pms.h"
#include "heuristic.h"
#include <signal.h>


FPS s;
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
