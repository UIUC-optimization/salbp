#include "bbr.h"

namespace salb
{

static   char     *degrees;      // work vector used by hoffman
static   short    *best_tasks;   // work vector used by hoffman
static   short    *eligible;     // work vector used by hoffman
static   short    *tasks;        // work vector used by hoffman
static   int      min_idle;      // used by hoffman
static   float    min_cost;      // used by hoffman
static   int      n_best_tasks;  // used by hoffman
static   int      max_n_full_loads;
static   int      n_full_loads;  // used by hoffman
static   short    *stations;     // work vector used by hoffman
static   int      *start_station;// work vector used by hoffman

//_________________________________________________________________________________________________

void initialize_hoffman()
{
   MALLOC(degrees, n_tasks+1, char);
   MALLOC(best_tasks, n_tasks+1, short);
   MALLOC(eligible, n_tasks+1, short);
   MALLOC(tasks, n_tasks+1, short);
   MALLOC(stations, n_tasks+1, short);
   MALLOC(start_station, n_tasks+2, int);
}

//_________________________________________________________________________________________________

void free_hoffman()
{
   free(degrees);
   free(best_tasks);
   free(eligible);
   free(tasks);
   free(stations);
   free(start_station);
}

//_________________________________________________________________________________________________

int hoffman(char *deg, int max_idle, int starting_station, int max_loads)
/*
   1. This routine uses the Hoffman heuristic to construct a solution for the simple assembly line balancing problem.
   3. deg(i) = # of immediate predecessors of task i that have not yet been assigned to a station.
   3. max_idle = maximum idle time allowed.
   4. starting_station = the number of the station to which we should begin assigning tasks.
   5. initialize_hoffman must be called before the first time this function is called.
   5. Written 2/24/06.
*/
{
   int      i, ii, /*idle,*/ j, jj, n_assigned, n_eligible, n_stations, sum_t;
   clock_t  start_time;

   start_time = clock();

   n_assigned = 0;
   for(i = 1; i <= n_tasks; i++) {
      assert((-1 <= deg[i]) && (deg[i] <= n_tasks));
      assert((1 <= t[i]) && (t[i] <= cycle));
      degrees[i] = deg[i];
      if(degrees[i] == -1) n_assigned++;
   }
   for(i = 0; i <= n_tasks; i++) {
      best_tasks[i] = -1;
      eligible[i] = -1;
      tasks[i] = -1;
      stations[i] = -1;
      start_station[i] = -1;
   }
   start_station[1] = 1;

   //idle = 0;
   n_stations = 0;
   max_n_full_loads = max_loads;

   while(n_assigned < n_tasks) {
      n_eligible = 0;
      for(i = 1; i <= n_tasks; i++) {
         assert((-1 <= degrees[i]) && (degrees[i] <= n_tasks));
         if(degrees[i] == 0) {
            eligible[++n_eligible] = i;
         }
      }

      min_idle = BIG_INT;
      min_cost = BIG_INT;
      n_best_tasks = 0;
      n_full_loads = 0;
   
      gen_load(1, cycle, 1, n_eligible, cycle);
   
      n_stations = n_stations + 1;
      start_station[n_stations+1] = start_station[n_stations] + n_best_tasks;
      for(i = 1, ii = start_station[n_stations]; ii < start_station[n_stations+1]; i++, ii++) {
         stations[ii] = best_tasks[i];
      }
   
      sum_t = 0;
      for(ii = 1; ii <= n_best_tasks; ii++) {
            i = best_tasks[ii];
         degrees[i] = -1;
         n_assigned++;
         sum_t += t[i];
         for(jj = 1; jj <= successors[i][0]; jj++) {
            j = successors[i][jj];
            degrees[j] = degrees[j] - 1;
         }
      }     
      //printf("n_stations = %d  idle = %d:  ", n_stations, cycle - sum_t);
      //prn_tasks(best_tasks, n_best_tasks);
   }

   assert(check_stations(deg, stations, start_station, n_stations) == 1);

   //printf("alpha = %6.3f  beta = %6.3f  n_stations = %2d\n", alpha, beta, n_stations);

   search_info.hoffman_cpu += (double) (clock() - start_time) / CLOCKS_PER_SEC;

   return(n_stations);
}

//_________________________________________________________________________________________________


void gen_load(int depth, int remaining_time, int start, int n_eligible, float cost)
/*
   1. GEN_LOAD generates a full load for a workstation.  It recursively generates loads
      and chooses the one with the minimum cost.
*/
{
   int      full_load, i, ii, j, jj, n_sub_eligible, stop, sub_remaining_time;
   float    sub_cost;
   //short *pnt, *stoppnt;

   assert((1 <= depth) && (depth <= n_tasks));

   full_load = 1;
   for(ii = start; ii <= n_eligible; ii++) {
      i = eligible[ii];
      assert((1 <= i) && (i <= n_tasks) && (degrees[i] == 0));
      if(t[i] <= remaining_time) {
         tasks[depth] = i;
         degrees[i] = -1;
         n_sub_eligible = n_eligible;
         full_load = 0;
         stop = successors[i][0];
         for(jj = 1; jj <= stop; jj++) {
            j = successors[i][jj];
            assert((1 <= j) && (j <= n_tasks) && (degrees[j] > 0));
            degrees[j]--;
            if(degrees[j] == 0) {
               eligible[++n_sub_eligible] = j;
            }
         }
      
         sub_remaining_time = remaining_time - t[i];
         sub_cost = cost - t[i] - alpha * positional_weight[i] - beta * successors[i][0] + gimmel;
         //if(sub_remaining_time < min_idle) {
         if(sub_cost < min_cost) {
            min_cost = sub_cost;
            for(jj = 1; jj <= depth; jj++) best_tasks[jj] = tasks[jj];
            n_best_tasks = depth;
         }
      
         gen_load(depth+1, sub_remaining_time,  ii + 1, n_sub_eligible, sub_cost);
      
         // Remove previously assigned task.
       
         tasks[depth] = -1;
         degrees[i] = 0;
        
         // Increment the degree of every successor of i.
      
         stop = successors[i][0];
         for(jj = 1; jj <= stop; jj++) {
            j = successors[i][jj];
            degrees[j]++;
         }
         //stoppnt = successors[i] + 1 + successors[i][0];
         //for(pnt = successors[i]+1; pnt <= stoppnt; pnt++) {
         //   j = *pnt;
         //   degrees[j]++;
         //}
      
         //if(min_idle == 0) {
         //   return;
         //}
         if(n_full_loads >= max_n_full_loads) return;
      }
   }
   n_full_loads += full_load;
}

//_________________________________________________________________________________________________

int check_stations(char *deg, short *stations, int *start_station, int n_stations)
/*
   1. This routine checks that stations represents a feasible solution.
   2. deg[i] = degree of i before started assigning tasks to workstations.
      This is used to determine which tasks were previously assigned.
   3. stations = vector containing the tasks assigned to each station.
      A sparse data structure is used, so that the tasks assigned to the first station
      appear first, then the tasks assigned to the second station, etc.
   4. start_station[m] = the index in stations where the first task for station m is stored.
      NOTE: start_station should be defined for 1,2,...,n_stations+1.
   5. 1 is returned if everything is OK,
      0 is returned o.w.
   6. Written 3/1/06.
*/
{
   int      *assigned, i, ii, j, station, sum;

   MALLOC(assigned, n_tasks+1, int);
   for(i = 1; i <= n_tasks; i++) assigned[i] = 0;
   for(i = 1; i <= n_tasks; i++) {
      if(deg[i] == -1) assigned[i] = 1;
   }

   for(station = 1; station <= n_stations; station++) {
      sum = 0;
      for(ii = start_station[station]; ii < start_station[station+1]; ii++) {
         i = stations[ii];

		 //added by AS 2013/06/06
		 if (reverse==1) {
  			if (optimalsolution[0]>n_stations) {
				optimalsolution[n_tasks+1-i]=n_stations+1-station;
			}
		 } else {
			if (optimalsolution[0]>n_stations) {
				optimalsolution[i]=station;
			}
		 }

		 assigned[i]++;
         sum += t[i];
      }
      if(sum > cycle) {
         printf("Too many tasks assigned to station\n");
         return(0);
      }

      for(ii = start_station[station]; ii < start_station[station+1]; ii++) {
         i = stations[ii];
         for(j = 1; j <= n_tasks; j++) {
            if((predecessor_matrix[j][i] == 1) && (assigned[j] != 1)) {
               printf("Predecessor of %d has not been assigned\n", i);
               return(0);
            }
         }
      }

   }

   //added by AS 2013/06/06
   if (optimalsolution[0]>n_stations) {
		optimalsolution[0]=n_stations;
   }

   for(i = 1; i <= n_tasks; i++) {
      if(assigned[i] < 1) {
         printf("Task %d has not been assigned\n", i);
         return(0);
      }
      if(assigned[i] > 1) {
         printf("Task %d has been assigned twice\n", i);
         return(0);
      }
   }
 
   free(assigned);
   return(1);
}

}; // end namespace salb



