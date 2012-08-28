#include "bbr.h"

namespace salb
{

static   int      *cycle_times;  // work vector used by sim_anneal
static   int      *cycle_times2; // work vector used by sim_anneal
static   int      *best_stations;// work vector used by sim_anneal
static   int      *curr_stations;// work vector used by sim_anneal
static   int      *earliest;     // work vector used by sim_anneal
static   int      *latest;       // work vector used by sim_anneal
static   int      *list;         // work vector used by sim_anneal
static   int      best_cycle;    // used by sim_anneal

//_________________________________________________________________________________________________

void initialize_anneal()
{
   MALLOC(cycle_times, n_tasks+1, int);
   MALLOC(cycle_times2, n_tasks+1, int);
   MALLOC(best_stations, n_tasks+1, int);
   MALLOC(curr_stations, n_tasks+1, int);
   MALLOC(earliest, n_tasks+1, int);
   MALLOC(latest, n_tasks+1, int);
   MALLOC(list, n_tasks+1, int);
}

//_________________________________________________________________________________________________

void free_anneal()
{
   free(cycle_times);
   free(cycle_times2);
   free(best_stations);
   free(curr_stations);
   free(earliest);
   free(latest);
   free(list);
}

//_________________________________________________________________________________________________

int sim_anneal(int desired_cycle, int *initial_stations, int n_stations, int n_iters, double beta, double tk)
/*
   1. This routine uses simulated annealing to attempt to construct a solution for the simple assembly line balancing problem.
      a. It starts with the assignment of tasks to n_station stations specified by initial_solutions.
      b. This initial assignment is infeasible because it violates the cycle time of some of the stations.
      c. It attempts to modify the assignment to reduce the maximum cycle time of a station.
      d. If it finds an assignment where the maximum cycle time of the stations is <= desired_cycle, then it returns.
   2. desired_cycle = the desired cycle time.  I.e., we are searching for a solution such that:
      a. The number of stations used = n_stations
      b. The total task time assigned to each station is <= desired_cycle.
   3. initial_solution[i] = station to which task i is initially assigned.
   4. n_stations = number of stations used by initial_stations.
   5. n_iters = maximum number of iterations to perform.
   6. tk = 
   5. The smallest cycle time found is returned.
   6. Written 3/15/06.
*/
{
   int      curr_cycle, delta, i, iter, m, neighbor_cycle, new_station, n_moves, task, task1, task2;
   double   Rk;

   // Compute the cost of the initial assignment and compute the cycle times of the stations.
   
   for(m = 1; m <= n_stations; m++) cycle_times[m] = 0;
   for(i = 1; i <= n_tasks; i++) {
      m = initial_stations[i];
      assert((1 <= m) && (m <= n_stations));
      cycle_times[m] += t[i];
      curr_stations[i] = m;
   }
   curr_cycle = 0;
   for(m = 1; m <= n_stations; m++) {
      if(cycle_times[m] > curr_cycle) curr_cycle = cycle_times[m];
   }

   // Copy the initial assignment into the best assignment.

   best_cycle = curr_cycle;
   for(i = 1; i <= n_tasks; i++) best_stations[i] = curr_stations[i];

   // Initialize the simulated annealing parameters.

   //beta = 0.98;
   //tk = curr_cycle;
   n_moves = 0;

   // Main loop.

   for(iter = 1; iter <= n_iters; iter++) {
      assert(check_assignment(curr_stations, n_stations, curr_cycle) == 1);
      tk = beta * tk;
      Rk = -tk * log(ggubfs(&seed));
      if(iter % 2 == 0) {
         gen_move(curr_stations, cycle_times, n_stations, &task, &new_station);
         neighbor_cycle = movecost(cycle_times, n_stations, task, new_station);
      } else {
         gen_swap_move(curr_stations, cycle_times, curr_cycle, n_stations, &task1, &task2);
         neighbor_cycle = swap_move_cost(curr_stations, cycle_times, n_stations, task1, task2);
      }
      delta = neighbor_cycle - curr_cycle;
      //if(iter % 1000 == 0) printf("iter = %7d tk = %9.2f Rk = %10.2f delta = %6d curr_cycle = %5d best_cycle = %5d n_moves = %6d\n", iter, tk, Rk, delta, curr_cycle, best_cycle, n_moves);
      if(delta <= Rk) {
         if(iter % 2 == 0) {
            if(new_station != curr_stations[task]) n_moves++;
            move(cycle_times, task, new_station);
         } else {
            if((task1 != task2) && (curr_stations[task1] != curr_stations[task2])) n_moves++;
            swap_move(curr_stations, cycle_times, n_stations, task1, task2);
         }
         curr_cycle = neighbor_cycle;
         if(neighbor_cycle < best_cycle) {
            best_cycle = neighbor_cycle;
            for(i = 1; i <= n_tasks; i++) best_stations[i] = curr_stations[i];
            if(best_cycle <= desired_cycle) return(best_cycle);
         }
      }
   }

   //printf("n_iters = %5d  tk = %8.3f  Rk = %8.3f  best_cycle = %5d\n", iter, tk, Rk, best_cycle);

   return(best_cycle);
}

//_________________________________________________________________________________________________


void gen_move(int *stations, int *cycle_times, int n_stations, int *task, int *new_station)
/*
   1. This function randomly chooses a neigbor of the assignmnet represented by stations.
*/
{
   int      earliest, j, jj, latest, stop;

   // Randomly choose a task to move.

   *task = randomi(n_tasks, &seed);

   // Determine the earliest and latest station to which task may be assigned without
   // violating the precedent constraints.

   earliest = 1;
   stop = predecessors[*task][0];
   for(jj = 1; jj <= stop; jj++) {
      j = predecessors[*task][jj];
      if(stations[j] > earliest) {
         earliest = stations[j];
      }
   }

   latest = n_stations;
   stop = successors[*task][0];
   for(jj = 1; jj <= stop; jj++) {
      j = successors[*task][jj];
      if(stations[j] < latest) {
         latest = stations[j];
      }
   }

   // Randomly choose a new station for task.

   *new_station = earliest + randomi(latest - earliest + 1, &seed) - 1;

}

//_________________________________________________________________________________________________


int movecost(int *cycle_times, int n_stations, int task, int new_station)
/*
   1. This function determines the new cost if task is moved to new_station.
*/
{
   int      m, new_cycle, old_station;

   old_station = curr_stations[task];
   cycle_times[old_station] -= t[task];
   cycle_times[new_station] += t[task];
   new_cycle = 0;
   for(m = 1; m <= n_stations; m++) {
      if(cycle_times[m] > new_cycle) new_cycle = cycle_times[m];
   }

   // Restore the original cycle times.

   cycle_times[old_station] += t[task];
   cycle_times[new_station] -= t[task];

   return(new_cycle);
}

//_________________________________________________________________________________________________


void move(int *cycle_times, int task, int new_station)
/*
   1. This function moves task to new_station.
*/
{
   int      old_station;

   old_station = curr_stations[task];
   curr_stations[task] = new_station;
   cycle_times[old_station] -= t[task];
   cycle_times[new_station] += t[task];
}

//_________________________________________________________________________________________________


void gen_swap_move(int *stations, int *cycle_times, int max_cycle_time, int n_stations, int *task1, int *task2)
/*
   1. This function generates a swap move from the assignmnet represented by stations.
      a. A station is critical if its cycle_time equals the maximum cycle time.
      b. The first task is chosen at random from among the set of tasks that are in the critical stations.
      c. The second task is chosen
   2. stations[i] = station to which task i is assigned.
   3. cycle_times[m] = cycle time of station m.
   4. max_cycle_time = maximum cycle time of the stations.
   5. n_stations = number of stations used by the assignment.
   6. task1 = first task chosen to be swapped.
   7. task2 = second task chosen to be swapped.
   8. Written 3/16/06.
*/
{
   int      i, j, jj, n_list, stop;

   // Create the list of tasks that are in critical stations.

   n_list = 0;
   for(i = 1; i <= n_tasks; i++) {
      if(cycle_times[stations[i]] == max_cycle_time) {
         list[++n_list] = i;
      }
   }

   // Randomly choose the first task to swap from among the tasks that are in critical stations.

   *task1 = list[randomi(n_list, &seed)];

   // Determine the earliest and latest station to which tasks may be assigned without
   // violating the precedent constraints.

   for(i = 1; i <= n_tasks; i++) {
      earliest[i] = 1;
      stop = predecessors[i][0];
      for(jj = 1; jj <= stop; jj++) {
         j = predecessors[i][jj];
         if(stations[j] > earliest[i]) {
            earliest[i] = stations[j];
         }
      }

      latest[i] = n_stations;
      stop = successors[i][0];
      for(jj = 1; jj <= stop; jj++) {
         j = successors[i][jj];
         if(stations[j] < latest[i]) {
            latest[i] = stations[j];
         }
      }
   }

   // Create the list of tasks which can be swapped with task1.

   n_list = 0;
   for(i = 1; i <= n_tasks; i++) {
      if((closed_predecessor_matrix[i][*task1] == 0) && (closed_predecessor_matrix[*task1][i] == 0) && (i != *task1)) {
         if((earliest[*task1] <= stations[i]) && (stations[i] <= latest[*task1])) {
            if((earliest[i] <= stations[*task1]) && (stations[*task1] <= latest[i])) {
               list[++n_list] = i;
            }
         }
      }
   }

   // Randomly choose the second task from among the list.

   if(n_list > 0) {
      *task2 = list[randomi(n_list, &seed)];
   } else {
      *task2 = *task1;
   }
}

//_________________________________________________________________________________________________


int swap_move_cost(int *stations, int *cycle_times, int n_stations, int task1, int task2)
/*
   1. This function determines the new cost if task1 and task2 are swapped.
*/
{
   int      m, new_cycle, station1, station2;

   station1 = stations[task1];
   station2 = stations[task2];
   cycle_times[station1] += t[task2] - t[task1];
   cycle_times[station2] += t[task1] - t[task2];
   new_cycle = 0;
   for(m = 1; m <= n_stations; m++) {
      if(cycle_times[m] > new_cycle) new_cycle = cycle_times[m];
   }

   // Restore the original cycle times.

   cycle_times[station1] += t[task1] - t[task2];
   cycle_times[station2] += t[task2] - t[task1];

   return(new_cycle);
}

//_________________________________________________________________________________________________


void swap_move(int *stations, int *cycle_times, int n_stations, int task1, int task2)
/*
   1. This function determines the new cost if task1 and task2 are swapped.
*/
{
   int      station1, station2;

   station1 = stations[task1];
   station2 = stations[task2];
   cycle_times[station1] += t[task2] - t[task1];
   cycle_times[station2] += t[task1] - t[task2];
   stations[task1] = station2;
   stations[task2] = station1;
}

//_________________________________________________________________________________________________

void gen_initial_assignment(int desired_cycle, int *stations, int n_stations)
/*
   1. This routine generates an assigment of tasks to stations.
      a. It assumes that the tasks are topologically sorted.
      b. It assigns tasks to the first station until the desired cycle time is violated.
         It then assigns tasks to the next station until the desired cycle time is violated.
   2. desired_cycle = the desired cycle time.  I.e., we are searching for a solution such that:
      a. The number of stations used = n_stations
      b. The total task time assigned to each station is <= desired_cycle.
   3. stations[i] = station to which task i is assigned.
   4. n_stations = number of stations to be used.
   6. Written 3/16/06.
*/
{
   int      c, i, m;

   m = 1;
   i = 1;
   c = 0;
   for(i = 1; i <= n_tasks; i++) {
      if(c > desired_cycle) {
         m++;
         c = 0;
      }
      stations[i] = m;
      c += t[i];
   }
}

//_________________________________________________________________________________________________

int check_assignment(int *stations, int n_stations, int max_cycle_time)
/*
   1. This routine checks that stations represents a feasible assignment of tasks to stations
      such that the cycle time of every station is <= max_cycle_time.
   2. stations[i] = station to which task i is assigned.
   3. max_cycle_time = maximum cycle time of the stations.
   4. n_stations = number of stations used by stations.
   5. 1 is returned if everything is OK,
      0 is returned o.w.
   6. Written 3/15/06.
*/
{
   int      i, j, jj, m, max, stop;

   assert((1 <= n_stations) && (n_stations <= n_tasks));

   for(m = 1; m <= n_stations; m++) cycle_times2[m] = 0;
   for(i = 1; i <= n_tasks; i++) {
      m = stations[i];
      assert((1 <= m) && (m <= n_stations));
      cycle_times2[m] += t[i];
      stop = successors[i][0];
      for(jj = 1; jj <= stop; jj++) {
         j = successors[i][jj];
         if(stations[j] < stations[i]) {
            printf("Successor of %d assigned to an earlier station\n", i);
            return(0);
         }
      }
   }

   max = 0;
   for(m = 1; m <= n_stations; m++) {
      if(cycle_times2[m] > max_cycle_time) {
         printf("cycle time is violated\n");
         return(0);
      }
      if(cycle_times2[m] > max) max = cycle_times2[m];
      if(cycle_times[m] != cycle_times2[m]) {
         printf("cycle_times are incorrect\n");
         return(0);
      }
         
   }

   if(max < max_cycle_time) {
      printf("None of the stations use max_cycle_time\n");
      return(0);
   }
 
   return(1);
}

}; // end namespace salb


