#include "bbr.h"
#include <cstdint>

namespace salb
{

static   char     *degrees;      // work vector used by bfs_bbr and genloads
static   short    *eligible;     // work vector used by bfs_bbr and genloads
static   short    *tasks;        // work vector used by bfs_bbr and genloads
static   int      index;         // used by bfs_bbr and genloads
static   char     station;       // used by bfs_bbr and genloads
static   int      idle;          // used by bfs_bbr and genloads
static   int      hash_value;    // used by bfs_bbr and genloads
static   int      previous;      // used by bfs_bbr and genloads

//_________________________________________________________________________________________________

void initialize_bfs_bbr()
{
   MALLOC(degrees, n_tasks+1, char);
   MALLOC(eligible, n_tasks+1, short);
   MALLOC(tasks, n_tasks+1, short);
   search_info.n_branches = 0;
   search_info.n_generated = 0;
   search_info.n_explored = 0;
   search_info.n_states = 0;
}

//_________________________________________________________________________________________________

void free_bfs_bbr()
{
   free(degrees);
   free(eligible);
   free(tasks);
}

//_________________________________________________________________________________________________

void bfs_bbr(int upper_bound)
/*
   1. This function uses breadth first search (BFS) branch bound and remember (BBR) to find an optimal solution
	  for the simple assembly line balancing problem.
   2. upper_bound = upper bound on the number of stations needed.  Search for a solution with fewer than upper_bound stations.
   3. Written 3/3/06.
*/
{
   char     LB;
   int      count, i, j, index, LB1, level, n_eligible, status, t_sum;
   double   cpu;
   clock_t  start_time;

   start_time = clock();

   UB = upper_bound;

   initialize_hash_table();
   reinitialize_states();

   // Add the root problem to the hash table and the list of states.

   t_sum = 0;
   for(i = 1; i <= n_tasks; i++) {
	  count = 0;
	  t_sum += t[i];
	  for(j = 1; j <= n_tasks; j++) {
		 if(predecessor_matrix[j][i] == 1) count++;
	  }
	  degrees[i] = count;
   }
   LB1 = (int) ceil((double) t_sum / (double) cycle);
   if(LB1 < UB) {
	  LB = (char) LB1;
	  index = find_or_insert(0.0, degrees, 0, LB, 0, 0, -1, 0, &status);
   }
   if(bin_pack_flag == -1) bin_pack_flag = bin_pack_lb;

   // Main loop
   // Modified 5/19/09 to call gen_loads iff states[index].open = 1.

   index = get_state();
   level = 0;
   count = 0;
   while( index >= 0) {
	  cpu = (double) (clock() - search_info.start_time) / CLOCKS_PER_SEC;
		if (cpu > CPU_LIMIT) {
		   printf("Time limit reached\n");
			verified_optimality = 0;;
		   break;
		}
	  if(state_space_exceeded == 1) {
		 verified_optimality = 0;
		 break;
	  }

	  if (states[index].n_stations > level) {
		 level = states[index].n_stations;
		 printf("%2d %10d %10d\n", level, count, last_state - first_state + 2);
		 count = 0;
		 //prn_states(level);
		 //if(level >= 3) return;
	  }

	  if(states[index].open == 1) {
		 states[index].open = 0;
		 count++;
		 search_info.n_explored++;
		 station = states[index].n_stations + 1;
		 idle = states[index].idle;
		 hash_value = states[index].hash_value;
		 previous = states[index].previous;
		 for(i = 1; i <= n_tasks; i++) degrees[i] = states[index].degrees[i];
		 n_eligible = 0;
		 for(i = 1; i <= n_tasks; i++) {
			assert((-1 <= degrees[i]) && (degrees[i] <= n_tasks));
			if(degrees[i] == 0) {
			   eligible[++n_eligible] = i;
			}
		 }

		 gen_loads(1, cycle, 1, n_eligible);

	  } else {
		 states[index].open = 0;
	  }
	  
	  index = get_state();
   }

   search_info.bfs_bbr_cpu += (double) (clock() - start_time) / CLOCKS_PER_SEC;
   free_hash_table();
}

//_________________________________________________________________________________________________

void gen_loads(int depth, int remaining_time, int start, int n_eligible)
/*
   1. This function recursively generates full loads for a workstation.
*/
{
   char     LB;
   int      full_load, i, ii, j, jj, LB1, LB2, LB3, LB_bin, n, n_sub_eligible, status, stop, sub_idle, sub_remaining_time, t_unassigned;
   std::uint64_t sub_hash_value;    //changed by AS 2013/06/06
   short    *list_of_items;
   double   LB2_unassigned, LB3_unassigned;

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
	  
		 gen_loads(depth+1, sub_remaining_time,  ii + 1, n_sub_eligible);
	  
		 // Remove previously assigned task.
	   
		 tasks[depth] = -1;
		 degrees[i] = 0;
		
		 // Increment the degree of every successor of i.
	  
		 stop = successors[i][0];
		 for(jj = 1; jj <= stop; jj++) {
			j = successors[i][jj];
			degrees[j]++;
		 }
	  }
   }

   if(full_load == 1) {

	  // If there are no tasks assigned to this station, then return.

	  if(depth == 1) return;

	  //prn_load(depth);

	  // Ignore this load if it can be pruned by a simple lower bound.
	  // Ignore this load if another task can be added.
   
	  search_info.n_generated++;
	  t_unassigned = 0;
	  LB2_unassigned = 0;
	  LB3_unassigned = 0;
	  for(i = 1; i <= n_tasks; i++) {
		 if(degrees[i] >= 0) {
			t_unassigned += t[i];
			LB2_unassigned += LB2_values[i];
			LB3_unassigned += LB3_values[i];
			if((degrees[i] == 0) && (t[i] <= remaining_time)) return;
		 }
	  }

	  // LB1

	  LB1 = (int) (station + ceil((double) t_unassigned / (double) cycle));
	  if(LB1 >= UB) {
		 return;
	  }

	  // LB2 from Sholl and Becker (2006).

	  LB2 = (int) (station + ceil(LB2_unassigned));
	  if(LB2 >= UB) {
		 return;
	  }

	  // LB3 from Sholl and Becker (2006).

	  LB3 = (int) (station + ceil(LB3_unassigned));
	  if(LB3 >= UB) {
		 return;
	  }

	  LB = (char) LB1;
	  if(LB2 > LB) LB = (char) LB2;
	  if(LB3 > LB) LB = (char) LB3;

	  // Check if a task in this station is potentially dominated by an available task.
	  // Modified 5/19/09 to call find_or_insert if a task is potentially dominated.
	  //    This reduced the number of branches, but increased the number of states stored,
	  //    so I changed it back.
   
	  for(i = 1; i <= n_tasks; i++) {
		 if(degrees[i] == 0) {
			for(jj = 1; jj <= depth-1; jj++) {
			   j = tasks[jj];
			   if((potentially_dominates[i][j] == 1) && (t[i] - t[j] <= remaining_time)) {
				  //sub_idle = idle + remaining_time;
				  //sub_hash_value = hash_value;
				  //for(i = 1; i <= depth-1; i++) sub_hash_value += hash_values[tasks[i]];
				  //sub_hash_value = sub_hash_value % HASH_SIZE;
				  //index = find_or_insert(0.0, degrees, station, LB, sub_idle, sub_hash_value, previous, 0, &status);
				  //if(status != 1) {
				  //   states[index].open = 0;
				  //}
				  return;
			   }
			}
		 }
	  }

	  // Check if there exists a task in the station that has a successor.
	  // Note: This code is not complete.  Before the load can be pruned, must also check that at least
	  // one unassigned task has a successor.
	  // Modified 5/21/09.  Do not return immediately.  Call find_or_insert first, and then set the open
	  //    status to 0 if the state was not strictly dominated.
	  //    This reduced the number of branches, but increased the number of states stored,
	  //    so I changed it back.

	  ii = 0;
	  for(jj = 1; jj <= depth-1; jj++) {
		 j = tasks[jj];
		 if(successors[j][0] > 0) {
			ii = 1;
			break;
		 }
	  }
	  if(ii == 0) {
		 for(i = 1; i <= n_tasks; i++) {
			if(degrees[i] >= 0) {
			   if(successors[i][0] > 0) {
				  ii = 1;
				  break;
			   }
			}
		 }
		 if(ii == 1) return;
	  }
 
	  sub_idle = idle + remaining_time;
	  sub_hash_value = hash_value;
	  for(i = 1; i <= depth-1; i++) sub_hash_value += hash_values[tasks[i]];
	  sub_hash_value = sub_hash_value % HASH_SIZE;
	  index = find_or_insert(0.0, degrees, station, LB, sub_idle, sub_hash_value, previous, 0, &status);
	  //if((ii == 0) && (status != 1)) {
	  //   states[index].open = 0;
	  //}
	  //if status >= 1 fprintf(1, '%2d: ', station); prnintvec(sort(find(degrees == -1)), 2); prnint(tasks, 2); end
	  assert(check_state(index) == 1);

	  // If this state has not been seen before or if it strictly dominates an existing state, then
	  // compute the bin packing lower bound.

	  if(((status == 0) || (status == 3)) && (bin_pack_flag == 1)) {
		 MALLOC(list_of_items, n_tasks+1,  short);
		 n = 0;
		 for(i = 1; i <= n_tasks; i++) {
			j = descending_order[i];
			if(degrees[j] >= 0) {
			   list_of_items[++n] = j;
			}
		 }
		 list_of_items[0] = n;
		 LB_bin = bin_dfs_bbr(list_of_items);
		 if(LB_bin < 0) bin_pack_flag = 0;
		 LB_bin += station;
		 if(LB_bin > LB) {
			LB = (char) LB_bin;
			states[index].LB = LB;
			if(LB >= UB) {
			   //prn_dfs_bbr_info(list_of_items, 0, 0, 0);
			   states[index].open = 0;
			}
		 }
		 free(list_of_items);
	  }

   }
}

//_________________________________________________________________________________________________

void backtrack(int index)
/*
   1. This routine constructs a solution by backtracking through the states.
   2. index = index of the state (in states) from which to begin backtracking.
   3. This routine does not return the solution.  It creates it, calls check_solution to
	  check it, and then deletes it.
   4. Written 4/19/06.
*/
{
   int      i, m, n_stations, previous, *stations;

   MALLOC(stations, n_tasks+1, int);
   for(i = 1; i <= n_tasks; i++) stations[i] = 0;

   n_stations = states[index].n_stations;
   previous = states[index].previous;
   while(previous >= 0) {
	  m = states[index].n_stations;
	  for(i = 1; i <= n_tasks; i++) {
		 if((states[index].degrees[i] == -1) && (states[previous].degrees[i] >= 0)) {
			stations[i] = m;
		 }
	  }
	  index = previous;
	  previous = states[index].previous;
   }

   i = check_solution(stations, n_stations);
   if(i == 0) exit(1);

   free(stations);
}

//_________________________________________________________________________________________________

int check_solution(int *stations, int n_stations)
/*
   1. This routine checks that stations represents a feasible assignment of tasks to stations.
   2. stations[i] = station to which task i is assigned.
   3. n_stations = number of stations used by stations.
   4. 1 is returned if everything is OK,
	  0 is returned o.w.
   5. Written 4/19/06.
*/
{
	int      *cycle_times, i, j, jj, m, stop;

   assert((1 <= n_stations) && (n_stations <= n_tasks));
   //printf("Solution with %d stations\n", n_stations);

   MALLOC(cycle_times, n_tasks+1, int);
   for(m = 1; m <= n_stations; m++) cycle_times[m] = 0;

   for(i = 1; i <= n_tasks; i++) {
	  m = stations[i];

	//added by AS 2013/06/06
	  if (reverse==1) {
  		if (optimalsolution[0]>=n_stations) {
			optimalsolution[n_tasks+1-i]=n_stations+1-m;
		}
	  } else {
  		if (optimalsolution[0]>=n_stations) {
			optimalsolution[i]=m;
		}
	  }
	  //printf("%d\t%d\n", i, m);

	  assert((1 <= m) && (m <= n_stations));
	  cycle_times[m] += t[i];
	  stop = successors[i][0];
      printf("Successors of task %d with time %d:", i, t[i]);
	  for(jj = 1; jj <= stop; jj++) {
		 j = successors[i][jj];
         printf("%d ", j);
		 if(stations[j] < stations[i]) {
			printf("Successor of %d assigned to an earlier station\n", i);
			return(0);
		 }
	  }
      printf("\n");
   }

	//added by AS 2013/06/06
   if (optimalsolution[0]>=n_stations) {
		optimalsolution[0]=n_stations;
   }


   for(m = 1; m <= n_stations; m++) {
	  if(cycle_times[m] > cycle) {
		 printf("cycle time is violated\n");
		 return(0);
	  }         
   }
 
   free(cycle_times);
   return(1);
}

//_________________________________________________________________________________________________

int check_state(int index)
/*
   1. This routine performs several simple checks on the data contained in a state.
   2. index = index of the state (in states) to be checked.
   3. 1 is returned if everything is OK,
	  0 is returned o.w.
   4. Written 3/21/06.
*/
{
   char     degree;
   int      i, /*idle,*/ j, jj, stop, t_assigned;
   std::uint64_t   hash_value;

   // Check the idle time and the hash_value.

   hash_value = 0;
   t_assigned = 0;
   for(i = 1; i <= n_tasks; i++) {
	  if(states[index].degrees[i] == -1) {
		 t_assigned += t[i];
		 hash_value += hash_values[i];
	  }
   }
   hash_value = hash_value % HASH_SIZE;
   //idle = cycle * states[index].n_stations - t_assigned;

   if(hash_value != states[index].hash_value) {
	 printf("hash_value is incorrect: %ld %ld\n", hash_value,    
    states[index].hash_value); 
	  return(0);
   }

   // Check that the degrees are consistent.

   for(i = 1; i <= n_tasks; i++) {
	  if(states[index].degrees[i] >= 0) {
		 degree = 0;
		 stop = predecessors[i][0];
		 for(jj = 1; jj <= stop; jj++) {
			j = predecessors[i][jj];
			if(states[index].degrees[j] >= 0) {
			   degree++;
			}
		 }

		 if(states[index].degrees[i] != degree) {
			printf("degree of node %d is incorrect\n", i);
			return(0);
		 }
	  }
   }

   return(1);
}
 


//_________________________________________________________________________________________________

void prn_load(int depth)
{
   int      i;

   printf("%2d: (", station);
   for(i = 1; i <= n_tasks; i++) if(degrees[i] == -1) printf("%2d ", i);
   printf(") (");
   for(i = 1; i <= depth-1; i++) printf("%2d ", tasks[i]);
   printf(")\n");
}

}; // end namespace salb




