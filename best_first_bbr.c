#include "bbr.h"
#include <cstdint>

namespace salb
{

static   char     *degrees;      // work vector used by bset_first_bbr and genloads2
static   short    *eligible;     // work vector used by best_first_bbr and genloads2
static   short    *tasks;        // work vector used by best_first_bbr and genloads2
static   int      index;         // used by best_first_bbr and genloads2
static   char     station;       // used by best_first_bbr and genloads2
static   int      idle;          // used by best_first_bbr and genloads2
static   int      hash_value;    // used by best_first_bbr and genloads2
static   int      previous;      // used by best_first_bbr and genloads2
static   int      n_full_loads;  // used by best_first_bbr and genloads2

//_________________________________________________________________________________________________

void initialize_best_first_bbr()
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

void free_best_first_bbr()
{
   free(degrees);
   free(eligible);
   free(tasks);
}

//_________________________________________________________________________________________________

void best_first_bbr(int upper_bound)
/*
   1. This function uses best first search branch bound and remember (BBR) to find an optimal solution
	  for the simple assembly line balancing problem.
   2. upper_bound = upper bound on the number of stations needed.  Search for a solution with fewer than upper_bound stations.
   3. Written 3/23/06.
   4. Note: Currently, this is not implemented quite right.  If a state dominates an existing state, then the state is replaced.
	  But if that state has already been processed, then the new state will not be processed.
*/
{
   int      count, root_LB, i, j, index, n_eligible, n_unassigned, status, t_sum;
   double   cpu, key, LB2, LB3;
   short    *list_of_items;
   clock_t  start_time;

   start_time = clock();

   UB = upper_bound;
   verified_optimality = 1;   // verified_optimality = 1 (0) if the best_first_bbr proved optimality
							  // This occurs if the maximum number of states was not exceeded,
							  // none of the heaps were filled, and the maximum_n_full_loads was not exceeded.

   initialize_hash_table();
   initialize_states();
   initialize_heaps();

   global_start_time = clock();

   // Add the root problem to the hash table and the list of states.

   double lb_cpu_start = clock();
   t_sum = 0;
   for(i = 1; i <= n_tasks; i++) {
	  count = 0;
	  t_sum += t[i];
	  for(j = 1; j <= n_tasks; j++) {
		 if(predecessor_matrix[j][i] == 1) count++;
	  }
	  degrees[i] = count;
   }
   root_LB = (int) ceil((double) t_sum / (double) cycle);
   LB2 = 0;
   LB3 = 0;
   for(i = 1; i <= n_tasks; i++) {
	  LB2 += LB2_values[i];
	  LB3 += LB3_values[i];
   }
   LB2 = ceil(LB2);
   LB3 = ceil(LB3);
   if(LB2 > root_LB) root_LB = (int) LB2;
   if(LB3 > root_LB) root_LB = (int) LB3;
   search_info.lb_cpu += (double) (clock() - lb_cpu_start);
   // LB3b works correctly.  If it is used, then 6 additional Wee-Mag problems (c = 45, 46, 49, 50, 52, 54)
   // can be solved without using the bin packing LB. 8/13/09.
   //i = LB3b();
   //if(i > root_LB) {
   //   root_LB = i;
   //}
   bin_pack_flag = bin_pack_lb;
   printf("Second lower bound %d\n", root_LB);

   if((bin_pack_flag == 1) && (root_LB < UB)) 
   {
	  MALLOC(list_of_items, n_tasks+1,  short);
	  for (i = 1; i <= n_tasks; i++) 
	  {
			j = descending_order[i];
			list_of_items[i] = j;
	  }
	  list_of_items[0] = n_tasks;
	  i = bin_dfs_bbr(list_of_items);
	  if(i < 0) {
		 bin_pack_flag = 0;
	  } else {
		 if(i > root_LB) {
			root_LB = i;
		 }
	  }
	  free(list_of_items);
	   printf("Bin-packing lower bound %d\n", root_LB);
   }
   if(root_LB < UB) 
	  index = find_or_insert(0.0, degrees, 0, 0, 0, 0, -1, 1, &status);
   else printf("Optimality proved by LB2 or BPLB\n");

   printf("lower bound time: %0.2fs\n", search_info.lb_cpu / CLOCKS_PER_SEC);
   printf("bin packing time: %0.2fs\n", search_info.bin_cpu / CLOCKS_PER_SEC);
   // Main loop

   //printf("maximum idle time = %d\n", cycle*(UB-1) - t_sum);
   //index = delete_min(dbfs_heaps[0]);
   index = get_min();
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

	  count++;
	  if (count % 10000 == 0) {
		 n_unassigned = 0;
		 for(i = 1; i <= n_tasks; i++) if(states[index].degrees[i] >= 0) n_unassigned++;
		 key = ((double) states[index].idle / (double) states[index].n_stations) - 0.02 * n_unassigned;
		 printf("%10d %10d %10d %2d %4d %3d %10.3f\n", count, last_state - count + 1, last_state + 1, states[index].n_stations, states[index].idle, n_tasks - n_unassigned, key);
	  }

	  states[index].open = 0;
	  if(states[index].LB < UB) {
		 search_info.n_explored++;
		 station = states[index].n_stations + 1;
		 idle = states[index].idle;
		 hash_value = states[index].hash_value;
		 previous = index;
		 for(i = 1; i <= n_tasks; i++) degrees[i] = states[index].degrees[i];
		 n_eligible = 0;
		 for(i = 1; i <= n_tasks; i++) {
			assert((-1 <= degrees[i]) && (degrees[i] <= n_tasks));
			if(degrees[i] == 0) {
			   eligible[++n_eligible] = i;
			}
		 }
		 n_full_loads = 0;

		 gen_loads2(1, cycle, 1, n_eligible);
	  }
	  
	  if(root_LB >= UB) {
		 verified_optimality = 1;
		 break;
	  }

	  //index = delete_min(dbfs_heaps[0]);
	  index = get_min();
   }

   search_info.best_first_cpu += (double) (clock() - start_time) / CLOCKS_PER_SEC;
   free_hash_table();
}

//_________________________________________________________________________________________________

void gen_loads2(int depth, int remaining_time, int start, int n_eligible)
/*
   1. This function recursively generates full loads for a workstation.
*/
{
   char     LB;
   int      full_load, i, ii, j, jj, LB1, LB2, LB3, LB_bin, n_sub_eligible, n, n_unassigned, status, stop, sub_idle, sub_remaining_time, t_unassigned;
   std::uint64_t sub_hash_value;    //changed by AS 2013/06/06
   short    *list_of_items;
   double   cpu, key, LB2_unassigned, LB3_unassigned;

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
	  
		 gen_loads2(depth+1, sub_remaining_time,  ii + 1, n_sub_eligible);
	  
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
	  if(n_full_loads >= 10000) {
		 if(verified_optimality == 1) printf("   exceeded max_n_full_loads\n");
		 verified_optimality = 0;
		 return;
	  }
   }

   if(full_load == 1) {

	  n_full_loads++;

	  // If there are no tasks assigned to this station, then return.

	  if(depth == 1) return;

	  //prn_load(depth);

	  // Ignore this load if it can be pruned by a simple lower bound.
	  // Ignore this load if another task can be added.
   
	  search_info.n_generated++;
	  n_unassigned = 0;
	  t_unassigned = 0;
	  LB2_unassigned = 0;
	  LB3_unassigned = 0;
	  for(i = 1; i <= n_tasks; i++) {
		 if(degrees[i] >= 0) {
			n_unassigned++;
			t_unassigned += t[i];
			LB2_unassigned += LB2_values[i];
			LB3_unassigned += LB3_values[i];
			if((degrees[i] == 0) && (t[i] <= remaining_time)) return;
		 }
	  }

	  // Update UB if a better solution has been found.

	  if((t_unassigned == 0) && (station < UB)) {
		 UB = station;
		 cpu = (double) (clock() - search_info.start_time) / CLOCKS_PER_SEC;
		 printf("   UB = %2d %8.3f\n", UB, cpu);
		 sub_idle = idle + remaining_time;
		 key = ((double) sub_idle / (double) station) - 0.02 * n_unassigned;
		 sub_hash_value = hash_value;
		 for(i = 1; i <= depth-1; i++) sub_hash_value += hash_values[tasks[i]];
		 sub_hash_value = sub_hash_value % HASH_SIZE;
		 LB = (char) UB;
		 index = find_or_insert(key, degrees, station, LB, sub_idle, sub_hash_value, previous, 1, &status);
		 backtrack(index);
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
   
	  for(i = 1; i <= n_tasks; i++) {
		 if(degrees[i] == 0) {
			for(jj = 1; jj <= depth-1; jj++) {
			   j = tasks[jj];
			   if((potentially_dominates[i][j] == 1) && (t[i] - t[j] <= remaining_time)) {
				  return;
			   }
			}
		 }
	  }

	  // Check if there exists a task in the station that has a successor.

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
	  key = ((double) sub_idle / (double) station) - 0.02 * n_unassigned;
	  sub_hash_value = hash_value;
	  for(i = 1; i <= depth-1; i++) sub_hash_value += hash_values[tasks[i]];
	  sub_hash_value = sub_hash_value % HASH_SIZE;
	  index = find_or_insert(key, degrees, station, LB, sub_idle, sub_hash_value, previous, 1, &status);
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

}; // end namespace salb
