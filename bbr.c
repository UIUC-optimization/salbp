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
int		 *hash_values;           // hash_values(j) = hash value assigned to task j.
double   *LB2_values;            // LB2_values[j] = the value assigned to task j to use in computing LB2.
double   *LB3_values;            // LB3_values[j] = the value assigned to task j to use in computing LB3.
int      *descending_order;      // descending_order[k] = the task with the kth largest processing time.
int      *sorted_task_times;     // sorted_task_times[k] = the kth largest processing time.
int      verified_optimality=1;    // verified_optimality = 1 (0) if best_first_bbr proved optimality
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
int CPU_LIMIT = 3600;
int* heap_sizes = NULL;
clock_t global_start_time;
char* root_degrees = NULL;

}; // end namespace salb


int main(int ac, char **av)
{
   double   cpu;
   time_t   current_time; 

   salb::global_start_time = clock();
   salb::search_info.start_time = clock();
   salb::search_info.hoffman_cpu = 0.0;
   salb::search_info.best_first_cpu = 0.0;
   salb::search_info.bfs_bbr_cpu = 0.0;
   salb::search_info.find_insert_cpu = 0.0;

   current_time = time(NULL);
   
   salb::parseargs (ac, av);
   if (salb::prn_info > 0) printf("%s start at %s\n", av[ac-1], ctime(&current_time));

   salb::testprob();

   cpu = (double) (clock() - salb::global_start_time) / CLOCKS_PER_SEC;
   printf("   verified_optimality = %d; value = %d; cpu = %0.2f\n", salb::verified_optimality, salb::UB, 
		   ((double)(clock() - salb::global_start_time)/CLOCKS_PER_SEC));
   if(salb::verified_optimality == 0) printf("   ************* DID NOT VERIFY OPTIMALITY ************\n");
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
		 case 't':
			CPU_LIMIT = atoi(av[++cnt]);
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
   fprintf (stderr, "    -t: CPU time limit\n");
   exit (1);
}


/*****************************************************************************/

void testprob()
{
   int      count, graph, i, iter, j, min_n_stations, n_stations, *stations, sum, t_sum, upper_bound;
   int      n_explored, n_generated, n_states;
   double   best_first_cpu, bfs_bbr_cpu, best_hoffman_cpu, hoffman_cpu, total_cpu;
   clock_t  start_time;

   sum = 0;
      read_problem(prob_file);
      cycle = 1000;

         close_pred();

      std::vector<int> E(n_tasks + 1);
      std::vector<int> L(n_tasks + 1);

      // Determine whether to run in forward or reverse
      for (int j = 1; j <= n_tasks; ++j)
      {
          double ftime = t[j];
          double rtime = t[j];
          for (int i = 1; i <= n_tasks; ++i)
          {
              if (closed_predecessor_matrix[i][j]) ftime += t[i];       // If task i precedes task j
              if (closed_predecessor_matrix[j][i]) rtime += t[i];       // If task j precedes task i
          }

          E[j] = ceil(ftime/cycle);
          L[j] = ceil(rtime/cycle);
      }

      int f = 1;
      int r = 1;
      for (int m = 1; m <= 5; ++m)
      {
          int fcount = 0;
          int rcount = 0;
          for (int j = 1; j <= n_tasks; ++j)
          {
              if (E[j] <= m) ++fcount;
              if (L[j] <= m) ++rcount;
          }

          f *= fcount;
          r *= rcount;
      }

      if (r < f)
      {
          printf("running in reverse %d %d\n", f, r);
          reverse_pred();
      }
	  else printf("running forward %d %d\n", f, r);

      find_successors();
      //prn_successors();
      close_pred();
      //prn_pred(closed_predecessor_matrix);
      compute_potentially_dominates();
      //prn_pred(potentially_dominates);
      compute_positional_weights();
      //prn_vec(n_predecessors, n_tasks); prn_vec(n_successors, n_tasks); prn_vec(positional_weight, n_tasks);
      compute_descending_order();

      MALLOC(root_degrees, n_tasks+1, char);
      t_sum = 0;
      for(i = 1; i <= n_tasks; i++) {
         t_sum += t[i];
         count = 0;
         for(j = 1; j <= n_tasks; j++) {
            if(predecessor_matrix[j][i] == 1) count++;
         }
         root_degrees[i] = count;
      }

      MALLOC(stations, n_tasks+1, int);
	  MALLOC(states, STATE_SPACE+1, state);

         search_info.start_time = clock();
         cycle = 1000;

         // Use Hoffman type heuristic to find a reasonably good upper bound.

         start_time = clock();
         best_hoffman_cpu = 0.0;
         initialize_hoffman();

         min_n_stations = BIG_INT;
         for (alpha = 0.000; alpha <= 0.02; alpha += 0.005) 
		 {
            for (beta = 0.000; beta <= 0.02; beta += 0.005) 
			{
               for (gimmel = 0; gimmel <= 0.03; gimmel += 0.01) 
			   {
                  n_stations = hoffman(root_degrees, 1000, 1, 5000);
                  if(n_stations < min_n_stations) 
				  {
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

         if (ceil((double) t_sum / (double) cycle) < upper_bound) 
		 {
            start_time = clock();
            initialize_best_first_bbr();

            if (bin_pack_lb == 1) 
				initialize_bin_packing();
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
            if ((verified_optimality != 0) && (bin_pack_lb == 1)) 
				free_bin_packing();
            best_first_cpu = (double) (clock() - start_time) / CLOCKS_PER_SEC;

            if (verified_optimality == 0) 
			{
               start_time = clock();
               initialize_bfs_bbr();
               bfs_bbr(upper_bound);
               free_bfs_bbr();
               if (bin_pack_lb == 1) 
				   free_bin_packing();
               bfs_bbr_cpu = (double) (clock() - start_time) / CLOCKS_PER_SEC;
            }
         }

         total_cpu = (double) (clock() - search_info.start_time) / CLOCKS_PER_SEC;

      free(stations);

      for(j = 1; j <= n_tasks; j++) 
	  {
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

   free(root_degrees);
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



