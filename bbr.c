#include "bbr.h"

/*
   The overall algorithm consists of three phases.
   Phase I.   A heuristic is used to find an initial upper bound.
   Phase II.  BB&R is executed with a best first search or distributed best first search strategy.
   Phase III. If Phase II is unable to verify optimality, then BB&R is executed with a breadth first search strategy.
*/

namespace salb
{

searchinfo search_info;
int      first_state;            // index (in states) where first unexplored is stored
int      last_state;             // index (in states) last  state is stored
state*   states;				 // Stores states
heap_record **dbfs_heaps;
heap_record *bfs_heap;
int      cycle = 0;              // Cycle time for the stations
int      n_tasks;                // number of tasks
int      UB;                     // upper bound on the number of stations needed
char     **predecessor_matrix;   // predecessor_matrix(i,j) = 1 indicates that i immediately precedes j.
char     **closed_predecessor_matrix;   // closed_predecessor_matrix(i,j) = 1 indicates that i precedes j.
char     **potentially_dominates;// potentially_dominates[i][j] = 1 if task i potentially dominates task j.
short    **predecessors;         // predecessors[j] = vector of immediates predecessors of task j.
short    **successors;           // successors[j] = vector of immediates successors of task j.
int      *t;                     // t[i] = processing time of task i
int      *n_successors;          // n_successors[i] = number of successors of i in closed graph.
int      *n_predecessors;        // n_predecessors[i] = number of predecessors of i in closed graph.
int      *positional_weight;     // positional_weight[i] = t[i] + sum(t[j]: j is a successor of i).
long 	 *hash_values;           // hash_values(j) = hash value assigned to task j.
double   *LB2_values;            // LB2_values[j] = the value assigned to task j to use in computing LB2.
double   *LB3_values;            // LB3_values[j] = the value assigned to task j to use in computing LB3.
int      *descending_order;      // descending_order[k] = the task with the kth largest processing time.
int      *sorted_task_times;     // sorted_task_times[k] = the kth largest processing time.
int      verified_optimality;    // verified_optimality = 1 (0) if best_first_bbr proved optimality
int      state_space_exceeded=0; // state_spaced_exceeded = 1 (0) if we attempt to store more than STATE_SPACE states
problem  problems[31];           // Cycle times and upper bounds for benchmark problems

float    alpha = 0.01;
float    beta = 0.01;
float    gimmel = 0.02;
char     *prob_file;        // problem file
int      bin_pack_flag = -1;
int      bin_pack_lb = 0;   // -b option: 1 = use bin packing LB, 0 = do not use
int      search_strategy = 1; /* -m option: search_strategy during Phase II                       
                                 1 = distributed best first search
                                 2 = best first search */
int      prn_info = 0;      // -p option: controls level of printed info
double   seed=3.1567;       // -s option: seed for random number generation

}; // end namespace salb


int main(int ac, char **av)
{
   double   cpu;
   time_t   current_time; 
   clock_t  start_time;

   start_time = clock();
   salb::search_info.start_time = clock();
   salb::search_info.hoffman_cpu = 0.0;
   salb::search_info.best_first_cpu = 0.0;
   salb::search_info.bfs_bbr_cpu = 0.0;
   salb::search_info.find_insert_cpu = 0.0;

   current_time = time(NULL);
   
   salb::parseargs (ac, av);
   if (salb::prn_info > 0) printf("%s start at %s\n", av[ac-1], ctime(&current_time));

   salb::bin_testprob();
   salb::testprob();
   //salb::define_problems();
   //salb::benchmarks(salb::prob_file);

   cpu = (double) (clock() - start_time) / CLOCKS_PER_SEC;
   printf("Hoffman cpu = %6.2f  best_first_bbr cpu = %6.2f  bfs_bbr cpu = %6.2f find_insert_cpu = %6.2f  bin_cpu = %6.2f  cpu = %6.2f\n", 
           salb::search_info.hoffman_cpu, salb::search_info.best_first_cpu, 
		   salb::search_info.bfs_bbr_cpu, salb::search_info.find_insert_cpu, 
		   salb::search_info.bin_cpu, cpu);

   current_time = time(NULL);
   if (salb::prn_info > 0) printf("\n%s end at %s\n", av[ac-1], ctime(&current_time));

   return 0;
}

namespace salb
{

//_________________________________________________________________________________________________

void parseargs(int ac, char **av)
{
   int c, cnt;

   cnt = 0; 
   while (++cnt < ac && av[cnt][0] == '-') {
      c = av[cnt][1];
      switch (c) {
         case 'b':
            bin_pack_lb = atoi(av[++cnt]);
            break;
         case 'c':
            cycle = atoi(av[++cnt]);
            break;
         case 'm':
            search_strategy = atoi(av[++cnt]);
            break;
         case 'p':
            prn_info = atoi(av[++cnt]);
            break;
         case 's':
            seed = atof(av[++cnt]);
            break;
         default:
            usage(*av);
            break;
      }
   }

   if (cnt >= ac) usage (*av);
   prob_file = av[cnt++];
   if (cnt < ac) usage (*av);
}

//_________________________________________________________________________________________________

void usage (char *prog)
{
   fprintf (stderr, "Usage: %s probfile\n", prog);
   fprintf (stderr, "    -b: 1 = use bin packing LB, 0 = do not use (def=0)\n");
   fprintf (stderr, "    -m: method (search_strategy) to use during Phase II 1 = DBFS, 2 = BFS (def=1)\n");
   fprintf (stderr, "    -p: controls level of printed information (def=0)\n");
   fprintf (stderr, "    -s: seed for random number generation\n");
   exit (1);
}


/*****************************************************************************/

void benchmarks(const char* filename)
{
   char     *degrees;
   int      count, graph, i, iter, j, min_n_stations, n_stations, *stations, sum, t_sum, upper_bound;
   int      n_explored, n_generated, n_states;
   double   best_first_cpu, bfs_bbr_cpu, best_hoffman_cpu, hoffman_cpu, total_cpu;
   clock_t  start_time;

   sum = 0;
//   for(graph = 24; graph <= 24; graph++) {
      read_problem(filename);
      //prn_problem();

      if ((graph == 2) || (graph == 3) || (graph == 8) || (graph == 11) || (graph == 13) || (graph == 16) || (graph == 19) || (graph == 21) || (graph == 23) || (graph == 25) || (graph == 26) || (graph == 27) || (graph == 28) || (graph == 30)) {
         reverse_pred();
      }
      find_successors();
      //prn_successors();
      close_pred();
      //prn_pred(closed_predecessor_matrix);
      compute_potentially_dominates();
      //prn_pred(potentially_dominates);
      compute_positional_weights();
      //prn_vec(n_predecessors, n_tasks); prn_vec(n_successors, n_tasks); prn_vec(positional_weight, n_tasks);
      compute_descending_order();

      MALLOC(degrees, n_tasks+1, char);
      t_sum = 0;
      for(i = 1; i <= n_tasks; i++) {
         t_sum += t[i];
         count = 0;
         for(j = 1; j <= n_tasks; j++) {
            if(predecessor_matrix[j][i] == 1) count++;
         }
         degrees[i] = count;
      }

/*
      initialize_hoffman();

      for(iter = 1; iter <= problems[graph].cycle_times[0]; iter++) {
         printf("%2d %3d %5d %2d ", graph, n_tasks, problems[graph].cycle_times[iter], problems[graph].upper_bounds[iter]);
         cycle = problems[graph].cycle_times[iter];
         min_n_stations = BIG_INT;
         for(alpha = 0.000; alpha <= 0.02; alpha += 0.005) {
            for(beta = 0.000; beta <= 0.02; beta += 0.005) {
               for(gimmel = 0; gimmel <= 0.03; gimmel += 0.01) {
                  n_stations = hoffman(degrees, 1000, 1, 5000);
                  if(n_stations < min_n_stations) min_n_stations = n_stations;
               }
            }
         }
         sum += min_n_stations - problems[graph].upper_bounds[iter];
         printf("%2d %2d\n", min_n_stations, min_n_stations - problems[graph].upper_bounds[iter]);
      }

      free_hoffman();
*/

      //initialize_anneal();
      MALLOC(stations, n_tasks+1, int);


      for(iter = 1; iter <= problems[graph].cycle_times[0]; iter++) {
         //if((graph == 24) && ((iter == 17) || (iter == 18) || (iter == 19) || (iter == 20) || (iter == 21) || (iter == 22) || (iter == 23))) continue;
         if((graph == 24) && ((iter == 17) || (iter == 18) || (iter == 19) || (iter == 20) || (iter == 21) || (iter == 22))) continue;
         //if((graph == 29) && ((iter == 2) || (iter == 3) || (iter == 7))) continue;
         //if((graph == 30) && ((iter == 1) || (iter == 3) || (iter == 4) || (iter == 5) || (iter == 7) || (iter == 9) || (iter == 11) || (iter == 12) || (iter == 13) || (iter == 14) || (iter == 15) || (iter == 16))) continue;
         search_info.start_time = clock();
         printf("%2d %3d %5d %2d \n", graph, n_tasks, problems[graph].cycle_times[iter], problems[graph].upper_bounds[iter]);
         cycle = problems[graph].cycle_times[iter];
         //upper_bound = problems[graph].upper_bounds[iter] + 1;
         //if(upper_bound > n_tasks) upper_bound = n_tasks;
         upper_bound = n_tasks;

         //LB3b();

         // Use Hoffman type heuristic to find a reasonably good upper bound.

         start_time = clock();
         best_hoffman_cpu = 0.0;
         initialize_hoffman();

         min_n_stations = BIG_INT;
         for(alpha = 0.000; alpha <= 0.02; alpha += 0.005) {
            for(beta = 0.000; beta <= 0.02; beta += 0.005) {
               for(gimmel = 0; gimmel <= 0.03; gimmel += 0.01) {
                  n_stations = hoffman(degrees, 1000, 1, 5000);
                  if(n_stations < min_n_stations) {
                     min_n_stations = n_stations;
                     best_hoffman_cpu = (double) (clock() - start_time) / CLOCKS_PER_SEC;
                  }
               }
            }
         }
         
         upper_bound = min_n_stations;
         UB = min_n_stations;
         free_hoffman();
         hoffman_cpu = (double) (clock() - start_time) / CLOCKS_PER_SEC;


         compute_LB2_values();
         compute_LB3_values();
         best_first_cpu = 0.0;
         bfs_bbr_cpu = 0.0;
         n_explored = 0;
         n_generated = 0;
         n_states = 0;
         if(ceil((double) t_sum / (double) cycle) < upper_bound) {

            //gen_initial_assignment(cycle, stations, upper_bound);
            //best_cycle = sim_anneal(cycle, stations, upper_bound, 2000000, 0.99999, 10*cycle);
            //printf("%5d ", best_cycle); if(best_cycle <= cycle) printf("0\n"); else printf("1\n");

            //initialize_bfs_bbr();
            //bfs_bbr(upper_bound);

            start_time = clock();
            initialize_best_first_bbr();
            if(bin_pack_lb == 1) initialize_bin_packing();
            best_first_bbr(upper_bound);
            n_explored = search_info.n_explored;
            n_generated = search_info.n_generated;
            n_states = search_info.n_states;
            search_info.n_explored = 0;
            search_info.n_generated = 0;
            search_info.n_states = 0;
            free_heaps();
		      free_best_first_bbr();
            reinitialize_states();
            if((verified_optimality != 0) && (bin_pack_lb == 1)) free_bin_packing();
            best_first_cpu = (double) (clock() - start_time) / CLOCKS_PER_SEC;

            if(verified_optimality == 0) {
               start_time = clock();
               initialize_bfs_bbr();
               bfs_bbr(upper_bound);
               free_bfs_bbr();
               if(bin_pack_lb == 1) free_bin_packing();
               bfs_bbr_cpu = (double) (clock() - start_time) / CLOCKS_PER_SEC;
            }
            //if(bin_pack_lb == 1) printf("n_in_bin_hash_table = %8d\n", get_n_in_bin_hash_table());
         }

         total_cpu = (double) (clock() - search_info.start_time) / CLOCKS_PER_SEC;
         printf("%2d %3d %5d %2d ", graph, n_tasks, problems[graph].cycle_times[iter], problems[graph].upper_bounds[iter]);
         printf("%2d %2d %7d %9d %7d ", min_n_stations, UB, n_explored, n_generated, n_states);
         printf("%7d %9d %7d ", search_info.n_explored, search_info.n_generated, search_info.n_states);
         printf("%6.2f %6.2f %6.2f %6.2f %6.2f\n", best_hoffman_cpu, hoffman_cpu, best_first_cpu, bfs_bbr_cpu, total_cpu);
      }

      //free_anneal();
      free(stations);

      for(j = 1; j <= n_tasks; j++) {
         free(predecessor_matrix[j]);
         free(closed_predecessor_matrix[j]);
         free(potentially_dominates[j]);
         free(successors[j]);
      }
      free(predecessor_matrix);
      free(closed_predecessor_matrix);
      free(potentially_dominates);
      free(predecessors);
      free(successors);
      free(t);
      free(n_successors);
      free(n_predecessors);
      free(positional_weight);
      free(hash_values);
      free(LB2_values);
      free(LB3_values);
      free(sorted_task_times);
      free(descending_order);
   //}

   free(degrees);
   printf("%2d\n", sum);
}

//_________________________________________________________________________________________________

void testprob()
{
   char     *degrees;
   int      count, i, j, upper_bound;
   
   read_problem(prob_file);
   //prn_problem();
   if(prn_info > 1) prn_problem();

   //reverse_pred();
   find_successors();
   //prn_successors();
   close_pred();
   //prn_pred(closed_predecessor_matrix);
   compute_potentially_dominates();
   //prn_pred(potentially_dominates);
   compute_positional_weights();
   //prn_vec(n_predecessors, n_tasks); prn_vec(n_successors, n_tasks); prn_vec(positional_weight, n_tasks);

   cycle = 1000;
   //upper_bound = 33;
   MALLOC(degrees, n_tasks+1, char);
   for(i = 1; i <= n_tasks; i++) {
      count = 0;
      for(j = 1; j <= n_tasks; j++) {
         if(predecessor_matrix[j][i] == 1) count++;
      }
      degrees[i] = count;
   }

   MALLOC(states, STATE_SPACE+1, state);
   compute_descending_order();
   compute_LB2_values();
   compute_LB3_values();

         double start_time = clock();
         double best_hoffman_cpu = 0.0;
         initialize_hoffman();

         int min_n_stations = BIG_INT;
         for(alpha = 0.000; alpha <= 0.02; alpha += 0.005) {
            for(beta = 0.000; beta <= 0.02; beta += 0.005) {
               for(gimmel = 0; gimmel <= 0.03; gimmel += 0.01) {
                  int n_stations = hoffman(degrees, 1000, 1, 5000);
                  if(n_stations < min_n_stations) {
                     min_n_stations = n_stations;
                     best_hoffman_cpu = (double) (clock() - start_time) / CLOCKS_PER_SEC;
                  }
               }
            }
         }
         
         upper_bound = min_n_stations;
         UB = min_n_stations;
         free_hoffman();
         double hoffman_cpu = (double) (clock() - start_time) / CLOCKS_PER_SEC;
/*
   initialize_hoffman();
   for(alpha = 0.001; alpha < 0.02; alpha += 0.001) {
      for(beta = 0.001; beta < 0.02; beta += 0.001) {
         hoffman(degrees, 1000, 1, 10000);
      }
   }
*/

   //initialize_anneal();
   //MALLOC(stations, n_tasks+1, int);
   //for(i = 1; i <= n_tasks; i++) stations[i] = 1;
   //gen_initial_assignment(cycle, stations, upper_bound);
   //sim_anneal(cycle, stations, upper_bound, 10000000, 0.99999, 10*cycle);

   //initialize_bfs_bbr();
   initialize_bin_packing();
   //bfs_bbr(upper_bound);

   initialize_best_first_bbr();
   best_first_bbr(upper_bound);

   free(degrees);
   free_bin_packing();
}

//_________________________________________________________________________________________________

void bin_testprob()
{
   char     *degrees;
   int      count, i, j; //, upper_bound;
   short    *items;
   
   read_problem(prob_file);
   //prn_problem();
   if(prn_info > 1) prn_problem();

   //reverse_pred();
   find_successors();
   //prn_successors();
   close_pred();
   //prn_pred(closed_predecessor_matrix);
   compute_potentially_dominates();
   //prn_pred(potentially_dominates);
   compute_positional_weights();
   //prn_vec(n_predecessors, n_tasks); prn_vec(n_successors, n_tasks); prn_vec(positional_weight, n_tasks);

   cycle = 1000;
   //upper_bound = 33;
   MALLOC(degrees, n_tasks+1, char);
   for(i = 1; i <= n_tasks; i++) {
      count = 0;
      for(j = 1; j <= n_tasks; j++) {
         if(predecessor_matrix[j][i] == 1) count++;
      }
      degrees[i] = count;
   }
   compute_descending_order();
   compute_LB2_values();
   compute_LB3_values();

   initialize_bfs_bbr();
   initialize_bin_packing();

   MALLOC(items, n_tasks+1, short);
   for(i = 1; i <= n_tasks; i++) items[i] = descending_order[i];
   items[0] = n_tasks;
   bin_dfs_bbr(items);
   //bfs_bbr(upper_bound);
   //prn_bin_hash_table();

   free(degrees);
   free_bin_packing();
}

/*****************************************************************************/

void close_pred()
/*
   1. This function creates the closed predecessor matrix from a predecessor matrix.
   2. The predecessor matrix must be acyclic.
   3. This function assumes that the tasks have been sorted such that (i,j) is an
      edge implies that i < j.
   4. predecessor_matrix[i][j] = 1 if task i precedes task j, 0 o.w.
   5. closed_predecessor_matrix[i][j] = 1 if there is a directed path from i to j in the graph.
   6. Written 2/28/06.
*/
{
   int      i, j, k;

   // Copy predecessor_matrix into closed_predecessor_matrix, check that the entries
   // are either 0 or 1, and check that the tasks are topologically sorted.

   MALLOC(closed_predecessor_matrix, n_tasks+1, char *);
   for(i = 1; i <= n_tasks; i++) {
      MALLOC(closed_predecessor_matrix[i], n_tasks+1, char);
      for(j = 1; j <= n_tasks; j++) {
         assert((predecessor_matrix[i][j] == 0) || (predecessor_matrix[i][j] == 1));
         assert((predecessor_matrix[i][j] == 0) || (i < j));
         closed_predecessor_matrix[i][j] = predecessor_matrix[i][j];
      }
   }

   // Compute the closure.

   for(k = 2; k <= n_tasks; k++) {
      for(j = 1; j < k; j++) {
         if(closed_predecessor_matrix[j][k] == 1) {
            for(i = 1; i < k; i++) {
               if(closed_predecessor_matrix[i][j] == 1) {
                  closed_predecessor_matrix[i][k] = 1;
               }
            }
         }
      }
   }
}

//_________________________________________________________________________________________________

void reverse_pred()
/*
   1. This function reverses the predecessor matrix and the t values.
   2. Written 3/2/06.
*/
{
   int      i, j, temp;

   for(i = 1; i <= n_tasks; i++) {
      for(j = 1; j <= n_tasks - i + 1; j++) {
         temp = predecessor_matrix[i][j];
         predecessor_matrix[i][j] = predecessor_matrix[n_tasks-j+1][n_tasks-i+1];
         predecessor_matrix[n_tasks-j+1][n_tasks-i+1] = temp;
      }
   }

   i = 1;
   j = n_tasks;
   while(i < j) {
      temp = t[i];
      t[i] = t[j];
      t[j] = temp;
      i++;
      j--;
   }
}

//_________________________________________________________________________________________________

void find_successors()
{
   int      i, j, k1, k2, *n_predecessors, *n_successors;

   MALLOC(n_successors, n_tasks+1, int);
   MALLOC(n_predecessors, n_tasks+1, int);
   for(i = 1; i <= n_tasks; i++) {
      n_predecessors[i] = 0;
      n_successors[i] = 0;
   }

   for(i = 1; i <= n_tasks; i++) {
      for(j = 1; j <= n_tasks; j++) {
         if(predecessor_matrix[j][i] == 1) {
            n_predecessors[i]++;
         }
         if(predecessor_matrix[i][j] == 1) {
            n_successors[i]++;
         }
      }
   }


   MALLOC(predecessors, n_tasks+1, short *);
   MALLOC(successors, n_tasks+1, short *);
   for(i = 1; i <= n_tasks; i++) {
      MALLOC(predecessors[i], n_predecessors[i]+1, short);
      MALLOC(successors[i], n_successors[i]+1, short);
      k1 = 0;
      k2 = 0;
      for(j = 1; j <= n_tasks; j++) {
         if(predecessor_matrix[j][i] == 1) {
            predecessors[i][++k1] = j;
         }
         if(predecessor_matrix[i][j] == 1) {
            successors[i][++k2] = j;
         }
      }
      predecessors[i][0] = k1;
      successors[i][0] = k2;
   }

   free(n_predecessors);
   free(n_successors);
}

//_________________________________________________________________________________________________

void compute_potentially_dominates()
/*
   1. This function determines which tasks potentially dominate one another.
   2. It uses the strengthened Jackson dominance rule (Scholl and Klein, 1997).
   3. Task i potentially dominates task j if the following conditions are satisfied:
      a. i and j are not related by a precedence relationship.
      b. t(i) >= t(j).
      c. The successors of i include the successors of j.
      d. If t(i) = t(j) and i and j have the same set of successors, then the task with the smaller task number
         dominates the other one.
   4. potentially_dominates[i][j] = 1 if task i potentially dominates task j.
   5. This function uses closed_predecessor_matrix, so it must be computed before this function is called.
   6. Written 3/21/06.
*/
{
   int      i, j, k, kk, stop, superset;

   // Copy predecessor_matrix into closed_predecessor_matrix, check that the entries
   // are either 0 or 1, and check that the tasks are topologically sorted.

   MALLOC(potentially_dominates, n_tasks+1, char *);
   for(i = 1; i <= n_tasks; i++) {
      MALLOC(potentially_dominates[i], n_tasks+1, char);
      for(j = 1; j <= n_tasks; j++) {
         assert((closed_predecessor_matrix[i][j] == 0) || (closed_predecessor_matrix[i][j] == 1));
         assert((closed_predecessor_matrix[i][j] == 0) || (i < j));
         
         potentially_dominates[i][j] = 0;
         if ((i != j) && (t[i] >= t[j]) && (closed_predecessor_matrix[i][j] == 0) && (closed_predecessor_matrix[j][i] == 0)) {

            // Determine if the successors of i contain all the successors of j.

            superset = 1;
            stop = successors[j][0];
            for(kk = 1; kk <= stop; kk++) {
               k = successors[j][kk];
               if(closed_predecessor_matrix[i][k] != 1) superset = 0;
            }

            // If superset = 1, determine if the two sets of successors are the same.

            if(superset == 1) {
               if(successors[i][0] == successors[j][0]) superset = 2;
            }

            if(superset >= 1) {
               if ((t[i] > t[j]) || ((t[i] == t[j]) && ((i < j) || (superset == 1)))) {
                  potentially_dominates[i][j] = 1;
               }
            }
         }

      }
   }
}

//_________________________________________________________________________________________________

void compute_LB2_values()
/*
   1. This function computes the values needed to compute LB2.
   2. Written 3/30/06.
*/
{
   int      i;

   MALLOC(LB2_values, n_tasks+1, double);
   LB2_values[0] = n_tasks;

   for(i = 1; i <= n_tasks; i++) {
      if(t[i] > cycle / 2.0) { LB2_values[i] = 1; continue; }
      if(t[i] == cycle / 2.0) { LB2_values[i] = 0.5; continue; }
      LB2_values[i] = 0;
   }
   //for(i = 1; i <= n_tasks; i++) printf("%3d %4d %8.2f\n", i, t[i], LB2_values[i]);
}

//_________________________________________________________________________________________________

void compute_LB3_values()
/*
   1. This function computes the values needed to compute LB3.
   2. Written 3/17/06.
*/
{
   int      i;

   MALLOC(LB3_values, n_tasks+1, double);
   LB3_values[0] = n_tasks;

   for(i = 1; i <= n_tasks; i++) {
      if(t[i] > 2 * cycle / 3.0) { LB3_values[i] = 1; continue; }
      if((cycle / 3.0 < t[i]) && (t[i] < 2 * cycle / 3.0)) { LB3_values[i] = 0.5; continue; }
      if(t[i] == 2 * cycle / 3.0) { LB3_values[i] = 2 / 3.0; continue; }
      if(t[i] == cycle / 3.0) { LB3_values[i] = 1 / 3.0; continue; }
      LB3_values[i] = 0;
   }
   //for(i = 1; i <= n_tasks; i++) printf("%3d %4d %8.2f\n", i, t[i], LB3_values[i]);
}

//_________________________________________________________________________________________________

void compute_positional_weights()
/*
   1. This function computes the number of predecessors, number of successors, and the 
      positional weights from the closed predecessor matrix.
   2. positional_weight[i] = t[i] + sum(t[j]: j is a successor of i).
   3. Written 2/28/06.
*/
{
   int      i, j, count, sum;

   MALLOC(n_predecessors, n_tasks+1, int);
   MALLOC(n_successors, n_tasks+1, int);
   MALLOC(positional_weight, n_tasks+1, int);

   for(i = 1; i <= n_tasks; i++) {
      n_predecessors[i] = 0;
      n_successors[i] = 0;
      positional_weight[i] = t[i];
   }

   for(i = 1; i <= n_tasks; i++) {
      count = 0;
      sum = 0;
      for(j = i+1; j <= n_tasks; j++) {
         if(closed_predecessor_matrix[i][j] == 1) {
            count++;
            sum += t[j];
         }
      }
      n_successors[i] = count;
      positional_weight[i] += sum;
   }

   for(j = n_tasks; j >= 1; j--) {
      count = 0;
      for(i = 1; i < j; i++) {
         if(closed_predecessor_matrix[i][j] == 1) {
            count++;
         }
      }
      n_predecessors[j] = count;
   }
}

//_________________________________________________________________________________________________

void compute_descending_order()
/*
   1. This function computes descending_order.
   2. descending_order[k] = the task with the kth largest processing time.
   3. Written 5/18/06.
*/
{
   int      i, index, j, max_value, temp;

   MALLOC(descending_order, n_tasks+1, int);
   MALLOC(sorted_task_times, n_tasks+1, int);
   
   // Sort the tasks in order of decreasing processing time.

   for(i = 1; i <= n_tasks; i++) {
      descending_order[i] = i;
      sorted_task_times[i] = t[i];
   }

   for(i = 1; i <= n_tasks - 1; i++) {
      max_value = sorted_task_times[i];
      index = i;
      for(j = i + 1; j <= n_tasks; j++) {
         if(sorted_task_times[j] > max_value) {
            max_value = sorted_task_times[j];
            index = j;
         }
      }
      temp = descending_order[i];
      descending_order[i] = descending_order[index];
      descending_order[index] = temp;
      temp = sorted_task_times[i];
      sorted_task_times[i] = sorted_task_times[index];
      sorted_task_times[index] = temp;
   }

   for(i = 1; i <= n_tasks - 1; i++) assert(t[descending_order[i]] >= t[descending_order[i+1]]);

   //for(i = 1; i <= n_tasks; i++) printf("%3d %4d %4d %4d\n", i, t[i], sorted_task_times[i], descending_order[i]);

   //free(sorted_task_times);
}

//_________________________________________________________________________________________________

int LB3b()
/*
   1. This function computes a lower bound for the simple assembly line balancing problem.
   2. The lower bound can be viewed as an extension of either LB3 or LB7 from Scholl and Becker (2006).
   3. Warning: This code is only designed to be called at the root node of the search tree.
      It needs to be modified to handle subproblems.
   4. Written 11/5/06.
*/
{
   int      flag, h, i, j, k, lb, *sorted_t, start;
   int      /*first_one,*/ first_half, last_one, last_half;
   double   best_sum, *best_w, sum_weights, *w;


   sorted_t = sorted_task_times;
   lb = 0;
   MALLOC(best_w, n_tasks+1, double);
   MALLOC(w, n_tasks+1, double);
   for(i = 1; i <= n_tasks; i++) {
      w[i] = 0;
      best_w[i] = 0;
   }
   if(n_tasks <= 1) return(0);

   // Phase I:  Find the largest i such that sorted_t(i-1) + sorted_t(i) > c.
   //           Tasks 1, 2, ..., i are temporarily assigned weight 1.


   w[1] = 1;
   sum_weights = 1;
   i = 1;
   while((i <= n_tasks - 1) && (sorted_t[i] + sorted_t[i+1] > cycle)) {
      i = i + 1;
      w[i] = 1;
      sum_weights = sum_weights + 1;
   }

   best_sum = sum_weights;
   for(h = 1; h <= n_tasks; h++) best_w[h] = w[h];

   // Phase II: Find tasks which can have a weight of 0.5 assigned to them.
   //           Assigning 0.5 to a task may necessitate changing the weight of some of the items that have weight 1 to 0.5.
   //           Keep track of the best set of weights found during the process.

   for(j = i+1; j <= n_tasks; j++) {
      if((j == i + 1) || (sorted_t[j-2] + sorted_t[j-1] + sorted_t[j] > cycle)) {
         while((i >= 1) & (sorted_t[i] + sorted_t[j] <= cycle)) {
            w[i] = 0.5;
            sum_weights = sum_weights - 0.5;
            i = i - 1;
         }
         w[j] = 0.5;
         sum_weights = sum_weights + 0.5;
      
         if(sum_weights > best_sum) {
            best_sum = sum_weights;
            for(h = 1; h <= n_tasks; h++) best_w[h] = w[h];
         }
      } else {
         break;
      }
   }

   // Phase III: Find tasks which can have a weight of 0.25 assigned to them.

   for(h = 1; h <= n_tasks; h++) w[h] = best_w[h];
   sum_weights = best_sum;
   for(i = 1; i <= n_tasks; i++) {
      if(sorted_t[i] < (cycle / 3)) {
         sum_weights = sum_weights - w[i];
         w[i] = 0;
      }
   }

   last_one = -1;
   last_half = -1;
   for(i = 1; i <= n_tasks; i++) {
      if(w[i] == 1) last_one = i;
      if(w[i] == 0.5) last_half = i;
   }

   //first_one = -1;
   first_half = -1;
   for(i = n_tasks; i >= 1; i--) {
      //if(w[i] == 1) first_one = i;
      if(w[i] == 0.5) first_half = i;
   }

   start = last_one;
   if(last_half > last_one) start = last_half;
   for(k = start+1; k <= n_tasks; k++) {
      flag = 1;
   
      if((last_one > 0) && (sorted_t[last_one] + sorted_t[k] <= cycle)) flag = 0;
   
      if((last_half - first_half > 0) && (sorted_t[last_half-1] + sorted_t[last_half] + sorted_t[k] <= cycle)) flag = 0;
   
      if((last_half > 0) && (k - last_half > 2) & (sorted_t[last_half] + sorted_t[k-2] + sorted_t[k-1] + sorted_t[k] <= cycle)) flag = 0;
   
      if((k - last_half > 4) && (sorted_t[k-4] + sorted_t[k-3] +sorted_t[k-2] + sorted_t[k-1] + sorted_t[k] <= cycle)) flag = 0;
   
      if(flag == 1) {
         w[k] = 0.25;
         sum_weights = sum_weights + 0.25;
      } else {
         break;
      }
   }

   if(sum_weights > best_sum) {
      best_sum = sum_weights;
      for(h = 1; h <= n_tasks; h++) best_w[h] = w[h];
   }

   lb = ceil(best_sum);
   for(h = 1; h <= n_tasks; h++) w[h] = best_w[h];

   //printf("%6.2f %3d\n", best_sum, lb);

   free(w);
   free(best_w);

   return(lb);
}

/*****************************************************************************/

void define_problems()
{
   int      i;
   problem  probs[31] = 
   {
	   {"", {0}, {0}},
	   {"c:\\sewell\\research\\assembly\\data\\bowman8.in2", {1, 20}, {1, 5}},
       {"c:\\sewell\\research\\assembly\\data\\mansoor.in2", {3, 48, 62, 94}, {3, 4, 3, 2}},
      {"c:\\sewell\\research\\assembly\\data\\mertens.in2", {6, 6, 7, 8, 10, 15, 18}, {6, 6, 5, 5,  3,  2,  2}},
      {"c:\\sewell\\research\\assembly\\data\\jaeschke.in2", {5, 6, 7, 8, 10, 18}, {5, 8, 7, 6,  4,  3}},
      {"c:\\sewell\\research\\assembly\\data\\jackson.in2", {6, 7, 9, 10, 13, 14, 21}, {6, 8, 6,  5,  4,  4,  3}},
      {"c:\\sewell\\research\\assembly\\data\\mitchell.in2", {6, 14, 15, 21, 26, 35, 39}, {6, 8,  8,  5,  5,  3,  3}},
      {"c:\\sewell\\research\\assembly\\data\\heskia.in2", {6, 138, 205, 216, 256, 324, 342}, {6,  8,   5,   5,   4,   4,   3}},
      {"c:\\sewell\\research\\assembly\\data\\sawyer30.in2", {7, 25, 27, 30, 36, 41, 54, 75}, {7, 14, 13, 12, 10,  8,  7,  5}},
      {"c:\\sewell\\research\\assembly\\data\\kilbrid.in2", {6, 57, 79, 92, 110, 138, 184}, {6, 10,  7,  6,   6,   4,   3}},
      {"c:\\sewell\\research\\assembly\\data\\tonge70.in2", {5, 176, 364, 410, 468, 527}, {5, 21,   10,   9,   8,   7}},
      {"c:\\sewell\\research\\assembly\\data\\arc83.in2", {7, 5048, 5853, 6842, 7571, 8412, 8898, 10816}, {7, 16, 14, 12, 11, 10, 9, 8}},
      {"c:\\sewell\\research\\assembly\\data\\arc111.in2", {6, 5755, 8847, 10027, 10743, 11378, 17067}, {6, 27, 18, 16, 15, 14, 9}},
      {"c:\\sewell\\research\\assembly\\data\\sawyer30.in2", {7, 27, 30, 33, 36, 41, 47, 54}, {7, 13, 12, 11, 10,  8,  7,  7}},
      {"c:\\sewell\\research\\assembly\\data\\kilbrid.in2", {6, 56, 62, 69, 79, 92, 111}, {6, 10,  9,  8,  7,  6,   5}},
      {"c:\\sewell\\research\\assembly\\data\\tonge70.in2", {12, 160, 168, 176, 185, 195, 207, 220, 234, 251, 270, 293, 320}, {12, 23, 22, 21, 20, 19, 18, 17, 16, 14, 14, 13, 11}},
      {"c:\\sewell\\research\\assembly\\data\\arc83.in2", {11, 3786, 3985, 4206, 4454, 4732, 5048, 5408, 5824, 6309, 6883, 7571}, {11, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11}},
      {"c:\\sewell\\research\\assembly\\data\\arc111.in2", {14, 5785, 6016, 6267, 6540, 6837, 7162, 7520, 7916, 8356, 8847, 9400, 10027, 10743, 11570}, {14, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 13}},
      {"c:\\sewell\\research\\assembly\\data\\roszieg.in2", {6, 14, 16, 18, 21, 25, 32}, {6, 10,  8,  8,  6,  6,  4}},
      {"c:\\sewell\\research\\assembly\\data\\buxey.in2", {7, 27, 30, 33, 36, 41, 47, 54}, {7, 13, 12, 11, 10,  8,  7,  7}},
      {"c:\\sewell\\research\\assembly\\data\\lutz1.in2", {6, 1414, 1572, 1768, 2020, 2357, 2828}, {6, 11, 10, 9, 8, 7, 6}},
      {"c:\\sewell\\research\\assembly\\data\\gunther.in2", {7, 41, 44, 49, 54, 61, 69, 81}, {7, 14, 12, 11,  9,  9,  8,  7}},
      {"c:\\sewell\\research\\assembly\\data\\hahn.in2", {5, 2004, 2338, 2806, 3507, 4676}, {5, 8, 7, 6, 5, 4}},
      {"c:\\sewell\\research\\assembly\\data\\warnecke.in2", {16, 54, 56, 58, 60, 62, 65, 68, 71, 74, 78, 82, 86, 92, 97, 104, 111}, {16, 31, 29, 29, 27, 27, 25, 24, 23, 22, 21, 20, 19, 17, 17,  15,  14}},
      {"c:\\sewell\\research\\assembly\\data\\wee-mag.in2", {24, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 45, 46, 47, 49, 50, 52, 54, 56}, {24, 63, 63, 62, 62, 61, 61, 61, 60, 60, 60, 60, 60, 60, 59, 55, 50, 38, 34, 33, 32, 32, 31, 31, 30}},
      {"c:\\sewell\\research\\assembly\\data\\lutz2.in2", {11, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21}, {11, 49, 44, 40, 37, 34, 31, 29, 28, 26, 25, 24}},
      {"c:\\sewell\\research\\assembly\\data\\lutz3.in2", {12, 75, 79, 83, 87, 92, 97, 103, 110, 118, 127, 137, 150}, {12, 23, 22, 21, 20, 19, 18,  17,  15,  14,  14,  13,  12}},
      {"c:\\sewell\\research\\assembly\\data\\mukherje.in2", {13, 176, 183, 192, 201, 211, 222, 234, 248, 263, 281, 301, 324, 351}, {13, 25,  24,  23,  22,  21,  20,  19,  18,  17,  16,  15,  14,  13}},
      {"c:\\sewell\\research\\assembly\\data\\barthold.in2", {8, 403, 434, 470, 513, 564, 626, 705, 805}, {8, 14,  13,  12,  11,  10,   9,   8,   7}},
      {"c:\\sewell\\research\\assembly\\data\\barthol2.in2", {27, 84, 85, 87, 89, 91, 93, 95, 97, 99, 101, 104, 106, 109, 112, 115, 118, 121, 125, 129, 133, 137, 142, 146, 152, 157, 163, 170}, {27, 51, 50, 49, 48, 47, 46, 45, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32, 31, 30, 29, 28, 27, 26, 25}},
      {"c:\\sewell\\research\\assembly\\data\\scholl.in2", {26, 1394, 1422, 1452, 1483, 1515, 1548, 1584, 1620, 1659, 1699, 1742, 1787, 1834, 1883, 1935, 1991, 2049, 2111, 2177, 2247, 2322, 2402, 2488, 2580, 2680, 2787}, {26, 50, 50, 48, 47, 46, 46, 44, 44, 42, 42, 40, 39, 38, 37, 36, 35, 34, 33, 32, 31, 30, 29, 28, 27, 26, 25}}
   };

   for(i = 0; i <31; i++) {
      problems[i] = probs[i];
   }
/*
   for(i = 0; i < 31; i++) {
      printf("%15s [", problems[i].file_name);
      for(j = 1; j <= problems[i].cycle_times[0];j++)  printf("%4d ", problems[i].cycle_times[j]);
      printf("] [");
      for(j = 1; j <= problems[i].upper_bounds[0];j++) printf("%4d ", problems[i].upper_bounds[j]);
      printf("]\n");
   }
*/
}

/*************************************************************************************************/

int sum(int *x, short *indices)
/*
   1. This function computes x[indices[1]] + x[indices[2]] + ... + x[indices[indices[0]].
   2. x[0] must equal the number of elements in x.
   3. indices[0] must equal the number of elements in indices.
   4. Written 4/23/09.
*/
{
   int      i, stop, sum;

   sum = 0;
   stop = indices[0];
   for(i = 1; i <= stop; i++) {
      assert((0 < indices[i]) && (indices[i] <= x[0]));
      sum += x[indices[i]];
   }

   return(sum);
}

//_________________________________________________________________________________________________

double sum_double(double *x, short *indices)
/*
   1. This function computes x[indices[1]] + x[indices[2]] + ... + x[indices[indices[0]].
   2. x[0] must equal the number of elements in x.
   3. indices[0] must equal the number of elements in indices.
   4. Written 4/23/09.
*/
{
   int      i, stop;
   double   sum;

   sum = 0;
   stop = indices[0];
   for(i = 1; i <= stop; i++) {
      assert((0 < indices[i]) && (indices[i] <= x[0]));
      sum += x[indices[i]];
   }

   return(sum);
}


/*****************************************************************************/

double ggubfs(double *dseed)
{
   int      div;
   double   product;

      product = 16807.0 * *dseed;
      div = product / 2147483647.0;
      *dseed = product - (div * 2147483647.0);
      return( *dseed / 2147483648.0 );
}

//_________________________________________________________________________________________________

int randomi(int n, double *dseed)
{
   int      truncate;
   //double   ggubfs();

   truncate = (n * ggubfs(dseed)) + 1;
   return(truncate);
}

}; // end namespace salb



