#include "bbr.h"

namespace salb
{

/*
   1. These functions solve a bin packing problem to be used as a lower bound for the
      assembly line balancing problem.
   2. The algorithm is based on An Improved Algorithm for Optimal Bin Packing by Korf.
      a. He uses memory in a limited fashion to keep a nogood list to reduce the number
         of bin completions.  These functions do not keep such a list.  Instead, it keeps
         a list of all the states encountered in the branch and bound tree.
      b. These functions do not use Korf's special method of generating pairs of nondominated items.
         This could be beneficial in speeding up the program.
   3. If int on memory, then it is not necessary to store states where the Best Fit Decreasing (BFD)
      heuristic equals the local lower bound.
   4. The depth first search (DFS) function is designed to find the optimal solution for every subproblem
      on which it is called.  It does not use global lower and upper bounds for pruning.  It only uses 
      local bounds for pruning.  The reason for doing this is that it is desired to build a database 
      of states as the overall BBR algorithm for the assembly line balancing problem proceeds.  In 
      order to reuse the states from one call of bin_dfs_bbr to the next, we need to know the optimal 
      number of bins for each state.  If a state was pruned using global bounds, then we do not know 
      its optimal value, hence cannot reuse it.
      a. It should be possible to store a lower bound for states that were pruned using global bounds.
         Then the state's lower bound could be reused for other subproblems.  If the state's lower bound
         is inadequate to prune a different subproblem, then the state would need to be solved again.
         I did not use this approach because in this particular application the local bounds should
         usually be as good as the global bounds.  The local lower bounds are identical to the global
         lower bounds.  The local upper bound is from the Best Fit Decreasing heuristic, which should
         seldom produce a solution with more than one extra bin, so it should seldom differ from the
         global upper bound.
   5. Hash Table
      a. The hash table for bin packing is separate from the hash table for the assembly line problem.
      b. Since we are using DFS, all the information for a state is kept in the hash table.  
         We do not need to keep a separate list of states nor any heaps for choosing the next state 
         to explore.
      c. A character array is used as a bit vector in the hash table to indicate which items
         still need to be assigned to a bin.  Bit i = 1 iff item i has not yet been assigned to a bin.
         Note that if bit i = 0, then item i may have been already assigned to a bin, or it may
         have been assigned to station in the assembly line problem.
      d. Hashing is performed on the sizes of items rather than the items themselves.  Due to duplicate
         sizes, two bin packing states may be identical, even though they have different sets of items.
   6. Written 4/243/09.
*/

#define  MAX_N_LOADS 50          // Maximum number of loads that can be stored in gen_nondominated_loads
//#define  BIN_HASH_SIZE 40031
#define  BIN_HASH_SIZE 400031
//#define  BIN_HASH_SIZE 4000039   // Must be a prime number.  Currently using linear
                                 // probing, but if quadratic probing is used, then
                                 // it must be a prime of the form 4j+3.  20000003=4*5000000+3   40000003=4*10000000+3

static   int      bin_status;             // used to stop the search process if the maximum number of loads is exceeded.
static   int      capacity;               // size of the bins, which equals the cycle time.
static   int      max_size;               // maximum item size.
static   int      n_items;                // number of items, which equals the number of tasks.
static   int    ***loads;               // loads[d][.][.] contains the loads at level d.
static   int      *n_loads;               // n_loads[d] = number of loads at level d.
static   int      *sizes;                 // sizes[j] = size of item j, which equals t[j].
static   int      *sizes_in_key;          // sizes_in_key[s] = number of items of size s in the key (used by compare_bin_keys).
static   clock_t  start_time;

// The following variables are used in bin_gen_nondominated_loads and the functions it calls (such as feasible and test_domination).

//static   int      bin;                    // bin = the number of the bin that is being loaded.
static   int    *included;              // list of items currently in the bin.
static   int      *excluded_sizes;        // excluded_sizes(s) = number of items of size s that are currently excluded from the bin.
static   int      n_included;             // number of items currently in the bin.
static   int      n_remaining_items;      // number of items still available to put in the bin.
static   int    *remaining_items;       // list of items still available to be put in the bin.
static   int      *sum_remaining_items;   // sum_remaining_items[j] = sum(k = j, j+1, ..., n_remaining_items} sizes[remaining_items[k]].

static   int      n_in_bin_hash_table;
static bin_hash_record bin_hash_table[BIN_HASH_SIZE];
static   int      *bin_hash_values;       // bin_hash_values(s) = hash value assigned to size s for the bin packing problem.

//_________________________________________________________________________________________________

void initialize_bin_packing()
{
   int      i, j, max_n_items_in_load, sum;
   clock_t  start_time;

   start_time = clock();

   capacity = cycle;
   n_items = n_tasks;
   sizes = t;

   MALLOC(loads, n_items+1, int **);
   sum = 0;
   for(i = n_items; i >= 1; i--) {
      sum += sorted_task_times[i];
      if(sum > capacity) break;
   }
   max_n_items_in_load = n_items - i;
   for(i = 0; i <= n_items; i++) {
      MALLOC(loads[i], MAX_N_LOADS+1, int *);
      loads[i][0] = NULL;
      for(j = 1; j <= MAX_N_LOADS; j++) {
         MALLOC(loads[i][j], max_n_items_in_load+1, int);
      }
   }
   MALLOC(n_loads, n_items+1, int);

   MALLOC(included, n_items+1, int);
   for(i = 1; i <= n_items; i++) included[i] = 0;
   max_size = 0;
   for(i = 1; i <= n_items; i++) {
      if(sizes[i] > max_size) max_size = sizes[i];
   }
   MALLOC(excluded_sizes, max_size+1, int);
   MALLOC(sizes_in_key, max_size+1, int);
   excluded_sizes[0] = max_size;
   for(i = 1; i <= max_size; i++) {
      excluded_sizes[i] = 0;
      sizes_in_key[i] = 0;
   }
   MALLOC(remaining_items, n_items+1, int);
   MALLOC(sum_remaining_items, n_items+1, int);

   MALLOC(bin_hash_values, max_size+1, int);
   for (i = 1; i <= max_size; i++) {
      bin_hash_values[i] = randomi(BIN_HASH_SIZE - 1, &seed);
   }
   //for(i = 1; i <= max_size; i++) printf("%8d ", bin_hash_values[i]); printf("\n");

   initialize_bin_hash_table();

   search_info.bin_cpu += (double) (clock() - start_time) / CLOCKS_PER_SEC;
}

//_________________________________________________________________________________________________

void free_bin_packing()
{
   int      i, j;
   clock_t  start_time;

   start_time = clock();

   for(i = 0; i <= n_items; i++) {
      for(j = 0; j <= MAX_N_LOADS; j++) {
         if(loads[i][j] != NULL) free(loads[i][j]);
      }
      free(loads[i]);
   }
   free(loads);
   free(n_loads);

   free(included);
   free(excluded_sizes);
   free(remaining_items);
   free(sum_remaining_items);
   free(bin_hash_values);
   free(sizes_in_key);

   for(i = 0; i < BIN_HASH_SIZE; i++) {
      if(bin_hash_table[i].key != NULL) free(bin_hash_table[i].key);
   }

   search_info.bin_cpu += (double) (clock() - start_time) / CLOCKS_PER_SEC;
}

/*************************************************************************************************/

int bin_dfs_bbr(int *list_of_items)
/*
   1. This function uses depth first search (DFS) branch, bound, and remember (BBR) to find an optimal solution
      for the bin packing problem.
   2. This function assumes that the items have been sorted such that sizes[list_of_items[1]] >= sizes[list_of_items[2]] >= ...
   3. Written 4/?/09.
*/
{
   int      bin_hash_value, index, n_preprocessed_bins, z, z_backtrack;
   int    *remaining_items;

   start_time = clock();

   // Perform preprocessing.

   MALLOC(remaining_items, n_items+1, int);
   remaining_items[0] = 0;
   n_preprocessed_bins = bin_preprocess(list_of_items, remaining_items);
   
   bin_hash_value = hash_items(remaining_items);
   //bin_hash_value = 0;
   bin_status = 0;

   z = dfs_bbr(1, remaining_items, bin_hash_value, sum(sizes, remaining_items), 
               sum_double(LB2_values, remaining_items), sum_double(LB3_values, remaining_items), &index);
   if(bin_status == 0) {
      if(z > 0) {
         z_backtrack = bin_backtrack2(index);
         assert(z_backtrack == z);
      }
      z += n_preprocessed_bins;
      //prn_dfs_bbr_info(list_of_items, 0, -1, z);
   } else {
      z = -1;
   }

   search_info.bin_cpu += (double) (clock() - start_time) / CLOCKS_PER_SEC;

   free(remaining_items);
   return(z);
}

//_________________________________________________________________________________________________

int dfs_bbr(int depth, int *eligible, int bin_hash_value, int lb1_sum, double lb2_sum, double lb3_sum, int *index)
/*
   1. This function performs depth first search (DFS) branch, bound, and remember to find an optimal solution for the bin packing problem.
   2. This function is designed to find the optimal solution for every subproblem on which it is called.
      It does not use global lower and upper bounds for pruning.  It only uses local bounds for pruning.
      The reason for doing this is that it is desired to build a database of states as the overall BBR algorithm
      for the assembly line balancing problem is used.  In order to reuse the states from one call of
      bin_dfs_bbr to the next, we need to know the optimal number of bins for each state.  If a state
      was pruned using global bounds, then we do not know its optimal value, hence cannot reuse it.
      a. It should be possible to store a lower bound for states that were pruned using global bounds.
         Then the state's lower bound could be reused for other subproblems.  If the state's lower bound
         is inadequate to prune a different subproblem, then the state would need to be solved again.
         I did not use this approach because in this particular application the local bounds should
         usually be as good as the global bounds.  The local lower bounds are identical to the global
         lower bounds.  The local upper bound is from the Best Fit Decreasing heuristic, which should
         seldom produce a solution with more than one extra bin, so it should seldom differ from the
         global upper bound.
   3. Input Variables
      a. depth = the depth in the branch and bound tree.
      b. eligible = list of items that must be assigned to bins.
                    The number of items in eligible should be stored in eligible[0].
                    This function assumes sizes[eligible[1]] >= sizes[eligible[2] >= ...
      c. bin_hash_value = the hash value for the eligible items 
                        = sum(j = 1,...,n_elgible) bin_hash_values[sizes[eligible[j]]] mod BIN_HASH_SIZE.
      d. lb1_sum = sum of the sizes of the eligible items.
      e. lb2_sum = sum of the lb2 values of the eligible items.
      f. lb3_sum = sum of the lb3 values of the eligible items.
   4. Output Variables
      a. z = optimal number of bins.
      b. index = index in the bin_hash_table where this state was stored.
   5. Written 4/17/09.
*/
{
   int      best_child, i, j, k, lb, lb1, lb2, lb3, n_eligible, n_items_in_load, *solution, z;
   int      n_sub_items, sub_hash_value, sub_index, sub_lb1_sum, sum_hash_values, z_sub;
   int    *items, *sub_eligible;
   double   sub_lb2_sum, sub_lb3_sum;

   if((double) (clock() - start_time) / CLOCKS_PER_SEC > 1.0) bin_status = 2;
   if(bin_status > 0) return(-1);

   // If there are no eligible items, then return.

   n_eligible = eligible[0];
   if(n_eligible == 0) {
      *index = -1;
      return(0);
   }

   assert((n_eligible <= 1) || (sizes[eligible[1]] >= sizes[eligible[2]]));

   // Check memory to see if this state has been previously encountered.  If so, return the answer.

   assert(hash_items(eligible) == bin_hash_value);
   *index = find_in_bin_hash(eligible, bin_hash_value);
   if(*index >= 0) {
      //prn_dfs_bbr_info(eligible, depth, -1, bin_hash_table[*index].z);
      return(bin_hash_table[*index].z);
   }

   // Use the best fit decreasing heuristic to find a solution.

   MALLOC(solution, n_items+1, int);
   solution[0] = n_items;
   z = best_fit_decreasing(eligible, solution);
   //prn_bfd_solution(eligible, solution, z);

   // Compute lower bounds (LB1, LB2, LB3 from Scholl and Becker (2006)) for this problem.

   assert(sum(sizes, eligible) == lb1_sum);
   assert(abs(sum_double(LB2_values, eligible) - lb2_sum) < 0.0000001);
   assert(abs(sum_double(LB3_values, eligible) - lb3_sum) < 0.0000001);
   lb1 = (int) ceil((float) lb1_sum / (float) capacity);
   if(lb2_sum - floor(lb2_sum) > 0.000001)
      lb2 = (int) ceil(lb2_sum);
   else
      lb2 = (int) floor(lb2_sum);
   if(lb3_sum - floor(lb3_sum) > 0.000001)
      lb3 = (int) ceil(lb3_sum);
   else
      lb3 = (int) floor(lb3_sum);
   lb = MAX(lb1, lb2);
   lb = MAX(lb, lb3);

   //printf("%2d %2d %2d: ", depth, lb, z); prn_int(eligible, n_eligible); printf("          "); for (i = 1; i <= n_eligible; i++) {printf("%2d ", sizes[eligible[i]]);} printf("\n");

   // Compare the lb to the number of bins used by the BFD solution.

   assert(lb <= z);
   if(lb == z) {
      *index = insert_in_bin_hash(eligible, bin_hash_value, -1, z);
      //prn_dfs_bbr_info(eligible, depth, lb, z);
      free(solution);
      return(z);
   }

   // Generate the loads for the bin at depth d.  The largest item is put into the bin.

   n_loads[depth] = 0;
   bin_gen_nondominated_loads(depth, eligible, eligible[1], lb1_sum, lb2_sum, lb3_sum, z);
   //prn_loads(depth, eligible, z);

   // Generate a subproblem for each load.

   best_child = -1;
   MALLOC(items, n_items+1, int);
   MALLOC(sub_eligible, n_items+1, int);
   for(i = 1; i <= n_loads[depth]; i++) {

      // Create the subproblem

      n_items_in_load = loads[depth][i][0];
      sub_lb1_sum = lb1_sum;
      sub_lb2_sum = lb2_sum;
      sub_lb3_sum = lb3_sum;
      sum_hash_values = 0;
      for(j = 1; j <= n_items_in_load; j++) {
         k = items[j] = loads[depth][i][j];
         sum_hash_values += bin_hash_values[sizes[k]];
         sub_lb1_sum -= sizes[k];
         sub_lb2_sum -= LB2_values[k];
         sub_lb3_sum -= LB3_values[k];
      }
      sub_hash_value = (bin_hash_value - sum_hash_values) % BIN_HASH_SIZE;    // Warning: If BIN_HASH_SIZE is very large, then overflow could occur here.
      if(sub_hash_value < 0) sub_hash_value += BIN_HASH_SIZE;                 //          It might be necessary to perform the mod operation on each item separately.
      n_sub_items = 0;
      items[n_items_in_load+1] = n_items + 1;      // Put a sentinel into items.
      for(j = 1, k = 1; j <= n_eligible; j++) {
         if(eligible[j] != items[k]) {
            sub_eligible[++n_sub_items] = eligible[j];
         } else {
            k++;
         }
      }
      sub_eligible[0] = n_sub_items;
      assert(n_sub_items == n_eligible - n_items_in_load);

      // Recursive call to solve the subproblem.

      z_sub = dfs_bbr(depth + 1, sub_eligible, sub_hash_value, sub_lb1_sum, sub_lb2_sum, sub_lb3_sum, &sub_index);
      if(bin_status > 0) {free(solution); free(items); free(sub_eligible); return(-1);}

      // Check if a better solution has been found.

      if(1 + z_sub < z) {
         z = 1 + z_sub;
         best_child = sub_index;
         if(check_child(eligible, best_child) == 1) {
            prn_int(eligible, eligible[0]);
            prn_int(sub_eligible, sub_eligible[0]);
            prn_sizes(sub_eligible, sub_eligible[0]);
            prn_bin_hash_table_entry(best_child);
         }
         if(lb == z) {
            *index = insert_in_bin_hash(eligible, bin_hash_value, best_child, z);
            //bin_backtrack(*index);      // We don't need the bin packing solution.  This was for debugging purposes.
            //prn_dfs_bbr_info(eligible, depth, lb, z);
            free(solution);
            free(items);
            free(sub_eligible);
            return(z);
         }
      }
   }

   // Store the state.

   *index = insert_in_bin_hash(eligible, bin_hash_value, best_child, z);
   //bin_backtrack(*index);         // We don't need the bin packing solution.  This was for debugging purposes.
   //prn_dfs_bbr_info(eligible, depth, lb, z);

   free(solution);
   free(items);
   free(sub_eligible);

   return(z);
}

//_________________________________________________________________________________________________

void bin_backtrack(int index)
/*
   1. This routine constructs a solution for a bin packing problem by backtracking through the states.
   2. index = index of the state (in bin_hash_table) from which to begin backtracking.
   3. This routine does not return the solution.  It creates it, calls check_solution to
      check it, and then deletes it.
   4. Written 5/14/09.
   5. This routine is not functioning correctly.  Use bin_backtrack2.
*/
{
   int      *bfd_solution, best_child, flag, i, j, n, n_assigned, n_bfd_bins, n_bins, n_in_child, n_in_parent, n_remaining, parent_index, *solution;
   int    item, *items, *items_in_child_not_parent, *items_in_parent_not_child, *remaining_items;

   assert((0 <= index) && (index < BIN_HASH_SIZE));

   MALLOC(solution, n_items+1, int);
   for(i = 1; i <= n_items; i++) solution[i] = 0;

   // Create the list of items in the problem.

   MALLOC(items, n_items+1, int);
   n = 0;
   for(i = 1; i <= n_items; i++) {
      if (IN_SET(bin_hash_table[index].key,i)) {
         items[++n] = i;
      }
   }
   items[0] = n;

   // Backtrack.
   // The following method of backtracking is incorrect.  It puts all the items that are in the parent but not in the child into
   // the current bin.  But there may be some items in the child that are not in the parent (but have the same sizes as items
   // in the parent).  Therefore, not all such items should be assigned to the current bin.

   //n_bins = 0;
   //best_child = bin_hash_table[index].best_child;
   //while(best_child >= 0) {
   //   n_bins++;
   //   for(i = 1; i <= n_tasks; i++) {
   //      if(IN_SET(bin_hash_table[index].key,i)) {
   //         if(!IN_SET(bin_hash_table[best_child].key,i)) {
   //            solution[i] = n_bins;
   //         }
   //      } 
   //   }
   //   index = best_child;
   //   best_child = bin_hash_table[index].best_child;
   //}

   // Backtrack.  Corrected 7/13/09 to handle a child that contains items that are not in the parent.

   MALLOC(items_in_child_not_parent, n_items+1, int);
   MALLOC(items_in_parent_not_child, n_items+1, int);
   n_bins = 0;
   n_assigned = 0;
   parent_index = index;
   best_child = bin_hash_table[index].best_child;
   while(best_child >= 0) {
      n_bins++;

      // Determine which items are in the parent but not the child, and vice versa.

      n_in_child = 0;
      n_in_parent = 0;
      for(i = 1; i <= n_tasks; i++) {
         if(IN_SET(bin_hash_table[index].key,i)) {
            if(!IN_SET(bin_hash_table[best_child].key,i)) {
               items_in_parent_not_child[++n_in_parent] = i;
            }
         } else {
            if(IN_SET(bin_hash_table[best_child].key,i)) {
               items_in_child_not_parent[++n_in_child] = i;
            }
         }
      }

      // For each item in the child but not the parent, remove an item of the same size from the items in parent but not the child.

      for(i = 1; i <= n_in_child; i++) {
         item = items_in_child_not_parent[i];
         flag = 0;
         for(j = 1; j <= n_in_parent; j++) {
            if(sizes[item] == sizes[items_in_parent_not_child[j]]) {
               items_in_parent_not_child[j] = items_in_parent_not_child[n_in_parent--];
               flag = 1;
               break;
            }
         }
         if(flag == 0) {
            fprintf(stderr, "Unable to find an item in the parent of the same size as the item in the child\n");
            exit(1);
         }
      }

      // Assign the remaining items in items_in_parent_not_child to the current bin.

      for(i = 1; i <= n_in_parent; i++) {
         solution[items_in_parent_not_child[i]] = n_bins;
         n_assigned++;
      }

      parent_index = index;
      index = best_child;
      best_child = bin_hash_table[index].best_child;
   }

   // Use the BFD heuristic to assign the remaining items to bins.

   MALLOC(remaining_items, n_items+1, int);
   n_remaining = 0;
   for(i = 1; i <= n_items; i++) {
      if (IN_SET(bin_hash_table[index].key,i)) {
         if((parent_index != index) && (!IN_SET(bin_hash_table[parent_index].key,i))) continue;
         remaining_items[++n_remaining] = i;
      }
   }
   remaining_items[0] = n_remaining;
   assert(n_assigned + n_remaining == n);
   MALLOC(bfd_solution, n_items+1, int);
   for(i = 1; i <= n_items; i++) bfd_solution[i] = 0;
   n_bfd_bins = best_fit_decreasing(remaining_items, bfd_solution);
   for(i = 1; i <= n_remaining; i++) solution[remaining_items[i]] = n_bins + bfd_solution[remaining_items[i]];
   n_bins += n_bfd_bins;

   check_bin_solution(items, solution, n_bins);

   free(solution);
   free(items);
   free(remaining_items);
   free(bfd_solution);
   free(items_in_child_not_parent);
   free(items_in_parent_not_child);
}

//_________________________________________________________________________________________________

int bin_backtrack2(int index)
/*
   1. This routine constructs a solution for a bin packing problem by backtracking through the states.
   2. index = index of the state (in bin_hash_table) from which to begin backtracking.
   3. This routine does not return the solution.  It creates it, calls check_solution to
      check it, and then deletes it.
   4. Written 7/14/09.
*/
{
   int      *bfd_solution, best_child, flag, i, *in_items, j, n, n_assigned, n_bfd_bins, n_bins, n_remaining;
   int      /*parent_index,*/ s, *sizes_in_child, *sizes_in_parent, *solution;
   int    *items, *remaining_items;

   assert((0 <= index) && (index < BIN_HASH_SIZE));

   MALLOC(solution, n_items+1, int);
   for(i = 1; i <= n_items; i++) solution[i] = 0;

   // Create the list of items in the problem.

   MALLOC(items, n_items+1, int);
   n = 0;
   for(i = 1; i <= n_items; i++) {
      if (IN_SET(bin_hash_table[index].key,i)) {
         items[++n] = i;
      }
   }
   items[0] = n;

   // Determine which sizes are used.

   MALLOC(sizes_in_child, max_size+1, int);
   MALLOC(sizes_in_parent, max_size+1, int);
   for(s = 1; s <= max_size; s++) {
      sizes_in_child[s] = 0;
      sizes_in_parent[s] = 0;
   }

   MALLOC(in_items, n_items+1, int);
   for(i = 1; i <= n_items; i++) in_items[i] = 0;

   for(i = 1; i <= n; i++) {
      assert(in_items[items[i]] == 0);
      in_items[items[i]] = 1;
      sizes_in_parent[sizes[items[i]]]++;
   }

   // Backtrack.

   n_bins = 0;
   n_assigned = 0;
   /*parent_index = index;*/
   best_child = bin_hash_table[index].best_child;
   while(best_child >= 0) {
      n_bins++;

      // Determine which sizes are in the parent.

      for(s = 1; s <= max_size; s++) sizes_in_parent[s] = 0;
      for(i = 1; i <= n_tasks; ++i) {
         if(IN_SET(bin_hash_table[index].key,i)) {
            sizes_in_parent[sizes[i]]++;
         }
      }

      // Determine which sizes are in the child.

      for(s = 1; s <= max_size; s++) sizes_in_child[s] = 0;
      for(i = 1; i <= n_tasks; i++) {
         if(IN_SET(bin_hash_table[best_child].key,i)) {
            sizes_in_child[sizes[i]]++;
         }
      }

      // Assign the sizes that are in the parent but not in the child to the current bin.

      for(s = 1; s <= max_size; s++) {
         assert(sizes_in_parent[s] >= sizes_in_child[s]);
         while(sizes_in_parent[s] > sizes_in_child[s]) {

            // Search for an item of size s that has not yet been assigned to a bin.

            flag = 0;
            for(i = 1; i <= n; i++) {
               if((sizes[items[i]] == s) && (solution[items[i]] == 0)) {
                  solution[items[i]] = n_bins;
                  n_assigned++;
                  flag = 1;
                  break;
               }
            }
            if(flag == 0) {
               fprintf(stderr, "Unable to find an item of the correct size to assign to the current bin\n");
               exit(1);
            }
            sizes_in_parent[s]--;
         }
      }

      //parent_index = index;
      index = best_child;
      best_child = bin_hash_table[index].best_child;
   }

   // Use the BFD heuristic to assign the remaining items to bins.

   MALLOC(remaining_items, n_items+1, int);
   n_remaining = 0;
   for(i = 1; i <= n_items; i++) {
      j = descending_order[i];
      if ((in_items[j] > 0) && (solution[j] == 0)) {
         remaining_items[++n_remaining] = j;
      }
   }
   remaining_items[0] = n_remaining;
   assert(n_assigned + n_remaining == n);
   MALLOC(bfd_solution, n_items+1, int);
   for(i = 1; i <= n_items; i++) bfd_solution[i] = 0;
   n_bfd_bins = best_fit_decreasing(remaining_items, bfd_solution);
   for(i = 1; i <= n_remaining; i++) solution[remaining_items[i]] = n_bins + bfd_solution[remaining_items[i]];
   n_bins += n_bfd_bins;

   check_bin_solution(items, solution, n_bins);

   free(solution);
   free(items);
   free(remaining_items);
   free(bfd_solution);
   free(sizes_in_child);
   free(sizes_in_parent);
   free(in_items);

   return(n_bins);
}

//_________________________________________________________________________________________________

void check_bin_solution(int *items, int *solution, int n_bins)
/*
   1. This routine checks that solution represents a feasible assignment of items to bins.
   2. Input Variables
      a. items = list of items that are supposed to be assigned to bins.
      b. solution[i] = bin to which item i is assigned.
      c. n_bins = number of bins used by solution.
   3. Written 5/15/09.
*/
{
   int      b, i, j, *in_items, n, *sizes_in_items, *sizes_in_solution, *sum_sizes_in_bin;

   assert((1 <= n_bins) && (n_bins <= n_items));

   // Check that the set of sizes of the items in items is the same as the set of sizes of the items in solution.
   // Note that the solution does not have to use the same set of items as in items, it just has to use the same set of sizes.

   MALLOC(in_items, n_items+1, int);
   for(i = 1; i <= n_items; i++) in_items[i] = 0;

   MALLOC(sizes_in_items, max_size+1, int);
   MALLOC(sizes_in_solution, max_size+1, int);
   for(i = 1; i <= max_size; i++) {
      sizes_in_items[i] = 0;
      sizes_in_solution[i] = 0;
   }

   n = items[0];
   for(i = 1; i <= n; i++) {
      assert((1 <= items[i]) && (items[i] <= n_items));
      assert(in_items[items[i]] == 0);
      in_items[items[i]] = 1;
      sizes_in_items[sizes[items[i]]]++;
   }

   for(i = 1; i <= n_items; i++) {
      if (solution[i] > 0) {
         assert((0 < solution[i]) && (solution[i] <= n_bins));
         sizes_in_solution[sizes[i]]++;
      }
   }

   for(i = 1; i <= max_size; i++) {
      if(sizes_in_items[i] != sizes_in_solution[i]) {
         fprintf(stderr,"The set of sizes of the items in items is not the same as the set of the sizes of solution\n"); 
         prn_int(items, items[0]);
         prn_sizes(items, items[0]);
         for (j = 1; j <= n_items; j++) {
            if(solution[j] > 0) printf("%2d ", j); 
         }
         printf("\n");
         for (j = 1; j <= n_items; j++) {
            if(solution[j] > 0) printf("%2d ", sizes[j]); 
         }
         printf("\n");
         exit(1);
      }
   }

   // Compute the amount of space used in each bin.

   MALLOC(sum_sizes_in_bin, n_bins+1, int);
   for(b = 1; b <= n_bins; b++) sum_sizes_in_bin[b] = 0;

   for(i = 1; i <= n_items; i++) {
      b = solution[i];
      assert(0 <= b);
      if(b > 0) {
         assert(b <= n_bins);
         sum_sizes_in_bin[b] += sizes[i];
      }
   }

   // Check that none of the bins are overloaded.

   for(b = 1; b <= n_bins; b++) {
      if(sum_sizes_in_bin[b] > capacity) {
         fprintf(stderr, "capacity is violated\n");
         exit(1);
      }         
   }
 
   free(sum_sizes_in_bin);
   free(in_items);
   free(sizes_in_items);
   free(sizes_in_solution);
}

//_________________________________________________________________________________________________

int check_child(int *items, int best_child)
/*
   1. This routine checks if the set of the sizes of the items in best_child is a subset of the set of
      sizes of the items in items.
   2. Input Variables
      a. items = list of items that must be assigned to bins.
                 The number of items in items should be stored in items[0].
                 This function assumes sizes[items[1]] >= sizes[items[2] >= ...
      b. index = index of the child state (in bin_hash_table).
   3. 1 is returned if the set of items in best_child is not a subset of the items in items.
      0 o.w.
   3. Written 6/15/09.
*/
{
   int      i, *in_items, n, *sizes_in_best_child, *sizes_in_items, sum_sizes;

   assert((0 <= best_child) && (best_child < BIN_HASH_SIZE));

   MALLOC(in_items, n_items+1, int);
   for(i = 1; i <= n_items; i++) in_items[i] = 0;
   MALLOC(sizes_in_items, max_size+1, int);
   MALLOC(sizes_in_best_child, max_size+1, int);
   for(i = 1; i <= max_size; i++) {
      sizes_in_items[i] = 0;
      sizes_in_best_child[i] = 0;
   }

   n = items[0];
   for(i = 1; i <= n; i++) {
      assert((1 <= items[i]) && (items[i] <= n_items));
      assert(in_items[items[i]] == 0);
      in_items[items[i]] = 1;
      sizes_in_items[sizes[items[i]]]++;
   }

   for(i = 1; i <= n_items; i++) {
      if (IN_SET(bin_hash_table[best_child].key,i)) {
         sizes_in_best_child[sizes[i]]++;
      }
   }

   for(i = 1; i <= max_size; i++) {
      if(sizes_in_items[i] < sizes_in_best_child[i]) {
         fprintf(stderr,"The set of sizes of the items in best_child is not a subset of the sizes of the parent\n"); 
         return(1);
      }
   }

   // Check if the sizes that are in the parent but not the child will fit into a single bin.

   sum_sizes = 0;
   for(i = 1; i <= max_size; i++) {
      sum_sizes += i * (sizes_in_items[i] - sizes_in_best_child[i]);
   }
   if(sum_sizes > capacity) {
      fprintf(stderr,"The sizes that are in the parent but not the child will fit into a single bin\n"); 
      return(1);
   }

   free(in_items);
   free(sizes_in_items);
   free(sizes_in_best_child);
   return(0);
}

/*************************************************************************************************/

void bin_gen_nondominated_loads(int depth, int *eligible, int fixed_item, int lb1_sum, double lb2_sum, double lb3_sum, int ub)
/*
   1. This function sets up the data to call feasible, which generates full loads for a bin in a 
      bin packing problem.
   2. Based on Korf's generation algorithm in An Improved Algorithm for Optimal Bin Packing.
      a. Korf assumes that the largest eligible item will be fixed in the bin.
         I permit the user to specify which item should be fixed in the bin.
      b. I compute the initial lower_sum differntly than Korf.
   3. This function differs from gen_loads in that it creates a list of loads that can be used in a depth first
      search without adding states to memory.
   4. Input Variables
      a. depth = depth in the B&B tree = the number of the bin that is being loaded.
      b. eligible = list of items that are eligible to be assigned to this bin.
                    The number of items in eligible should be stored in eligible[0].
                    This function assumes sizes[eligible[1]] >= sizes[eligible[2] >= ...
      c. fixed_item = item that should be fixed in the bin.  I.e., search for all nondominated loads
                      that contain the fixed item.
      d. lb1_sum = sum of the sizes of the eligible items.
      e. lb2_sum = sum of the lb2 values of the eligible items.
      f. lb3_sum = sum of the lb3 values of the eligible items.
      g. ub = upper bound on the number of bins needed for all the unassigned items.
   5. Written 4/23/09.
*/
{
   int      i, j, lower_sum, n_eligible, remaining_size;
   bin_data bin_data;

   if((double) (clock() - start_time) / CLOCKS_PER_SEC > 1.0) bin_status = 2;
   if(bin_status > 0) return;

   for(i = 1; i <= excluded_sizes[0]; i++) excluded_sizes[i] = 0;    // Delete this line if we can ensure that it always is reset to zero when this function finishes.

   // Put the fixed item into the bin.

   assert((0 < fixed_item) && (fixed_item <= n_items));
   n_included = 1;
   included[1] = fixed_item;
   remaining_size = capacity - sizes[fixed_item];

   // Construct the list of remaining items.

   n_remaining_items = 0;
   n_eligible = eligible[0];
   for(i = 1; i <= n_eligible; i++) {
      j = eligible[i];
      if((j != fixed_item) && (sizes[j] <= remaining_size)) {
         remaining_items[++n_remaining_items] = j;
      }
   }

   // Compute the cumulative sum of the sizes of the remaining items, starting from the end of the list.
   // sum_remaining_items[j] = sum(k = j, j+1, ..., n_remaining_items} sizes[remaining_items[k]].

   if(n_remaining_items > 0) {
      sum_remaining_items[n_remaining_items] = sizes[remaining_items[n_remaining_items]];
      for(i = n_remaining_items-1; i > 0; i--) sum_remaining_items[i] = sum_remaining_items[i+1] + sizes[remaining_items[i]];
   } else {
      sum_remaining_items[1] = 0;
   }

   // Load data into bin_data.

   bin_data.bin = depth;
   bin_data.eligible = eligible;
   bin_data.lb1_sum = lb1_sum;
   bin_data.lb2_sum = lb2_sum;
   bin_data.lb3_sum = lb3_sum;
   bin_data.ub = ub;

   // Compute a lower bound on the sum of the sizes of the remaining items put into the bin.
   // Note: Korf uses "The largest single element that can feasibly be added to the bin, plus one."
   //       I do not think the plus one is correct.  This would prevent any loads from being
   //       generated if only one more item can fit in the bin.
   // I use a second lower bound based on the maximum amount of wasted space in this bin.

   lower_sum = capacity - sizes[fixed_item] - (capacity * (ub - 1) - lb1_sum);
   if(lower_sum < 0) lower_sum = 0;
   if(n_remaining_items > 0) lower_sum = MAX(lower_sum, sizes[remaining_items[1]]); 

   // Call feasible to generate the loads.

   if(n_remaining_items > 0) {
      feasible(1, lower_sum, remaining_size, &bin_data);
   } else {
      feasible(1, 0, remaining_size, &bin_data);
   }
}

//_________________________________________________________________________________________________

void feasible(int index, int lower_sum, int upper_sum, bin_datapnt bin_data)
/*
   1. This function recursively generates feasible loads for the bin packing problem.
   2. Based on Korf's generation algorithm in An Improved Algorithm for Optimal Bin Packing.
      a. Korf's pseudocode did not specify how the lower_sum is used.  I use it to
         prune if the sum of the sizes of the remaining items is less than lower_sum.
      b. I did not write a function to generate all nondominated pairs of items in linear time.
         Such a fucntion might speed up this function.
      c. I included several tests to prune during the generation process that Korf either did not
         use or waited until the load was full to test.
      d. It should be possible to compute the subset sums during the generation process and perform
         some of the domination testing during the generation process.
   3. It recursively adds items to the current bin until it is full (or there are no more items).
      To be eligible to be added, an item j must satisfy the following:
      a. sizes(j) <= remaining_size.  There is still room for item j in the current bin.
      b. excluded(j) = 0.  At the root call, excluded should be set to all zeros.  After this function loads
         item k, it will exclude k from further consideration.  This is to avoid enumeration of redundant loads.
   3. It calls test_domination to eliminate dominated loads.
   5. When a full load is generated, this function will add the corresponding subproblem to the list of loads.
   4. Input Variables
      a. index = index of next item to consider putting into the bin.
      b. lower_sum is a lower bound on the sum of the sizes of the remaining items put into the bin.
         Note:  I cannot see how lower_sum is used in the algorithm presented in the paper.
      c. upper_sum is an upper bound on the sum of the sizes of the remaining items put into the bin.
   5. Written 4/23/09
*/
{
   int      bin, dominated, i, j, k, lb, lb1, lb2, lb3, lb1_sum_unassigned, size_j;
   double   lb2_sum_unassigned, lb3_sum_unassigned;

   if((double) (clock() - start_time) / CLOCKS_PER_SEC > 1.0) bin_status = 2;
   if(bin_status > 0) return;

   //printf("%2d %2d %2d\n", index, lower_sum, upper_sum);
   //prn_int(included, n_included);

   if((index > n_remaining_items) || (upper_sum < sizes[remaining_items[n_remaining_items]])) {
      
      included[0] = n_included;
      //printf("%2d %2d %2d: ", sum(sizes,included), lower_sum, upper_sum); prn_int(included, n_included); printf("          ");   for (i = 1; i <= n_included; i++) {printf("%2d ", sizes[included[i]]);} printf("\n");

      // Compute lower bounds (LB1, LB2, LB3 from Scholl and Becker (2006)) for this load.

      lb1_sum_unassigned = bin_data->lb1_sum;
      lb2_sum_unassigned = bin_data->lb2_sum;
      lb3_sum_unassigned = bin_data->lb3_sum;
      for(j = 1; j <= n_included; j++) {
         k = included[j];
         lb1_sum_unassigned -= sizes[k];
         lb2_sum_unassigned -= LB2_values[k];
         lb3_sum_unassigned -= LB3_values[k];
      }

      lb1 = 1 + (int) ceil((float) lb1_sum_unassigned / (float) capacity);
      lb2 = 1 + (int) ceil(lb2_sum_unassigned);
      lb3 = 1 + (int) ceil(lb3_sum_unassigned);
      lb = MAX(lb1, lb2);
      lb = MAX(lb, lb3);

      // Ignore this load if it can be pruned by a simple lower bound.
      
      if(lb >= bin_data->ub) {
         return;
      }
      
      // Ignore this load if it is dominated.

      dominated = test_domination(included, bin_data);
      if(dominated == 1) {
         return;
      }
      
      //printf("%2d %2d %2d: ", sum(sizes, included), lower_sum, upper_sum); prn_int(included, n_included);  printf("          ");  for (i = 1; i <= n_included; i++) {printf("%2d ", sizes[included[i]]);} printf("\n");
      
      bin = bin_data->bin;
      n_loads[bin]++;
      //if(n_loads[bin] > MAX_N_LOADS) {fprintf(stderr,"Maximum number of loads exceeded\n"); exit(1);}
      if(n_loads[bin] > MAX_N_LOADS) {fprintf(stderr,"Maximum number of loads exceeded\n"); bin_status = 1; return;}
      loads[bin][n_loads[bin]][0] = n_included;
      for(i = 1; i <= n_included; i++) loads[bin][n_loads[bin]][i] = included[i];
      
      return;
   }

   assert((index >= n_remaining_items) || (sizes[remaining_items[index]] >= sizes[remaining_items[index+1]]));

   // Prune if the sum of the sizes of the remaining items is less than lower_sum.

   if(sum_remaining_items[index] < lower_sum) {
      return;
   }

   // Prune if the remaining space in the bin equals the size of an excluded item.
   // Korf does not include this prune.

   if((upper_sum <= excluded_sizes[0]) && (excluded_sizes[upper_sum] > 0)) {
      return;
   }

   j = remaining_items[index];
   size_j = sizes[j];

   // If at most one item will fit, add the largest such item.

   if((index < n_remaining_items) && (sum_remaining_items[n_remaining_items-1] > upper_sum)) {
      while(sizes[remaining_items[index]] > upper_sum) {
         index++;
      }
      j = remaining_items[index];
      size_j = sizes[j];
      if(excluded_sizes[size_j] == 0) {         // Korf does not include this test.
         included[++n_included] = j;
         feasible(index+1, 0, 0, bin_data);
         included[n_included--] = 0;
      }
      return;
   }

   // Main recursion.

   if(size_j > upper_sum) {
      excluded_sizes[size_j]++;   
      feasible(index+1, lower_sum, upper_sum, bin_data);
      excluded_sizes[size_j]--;      
   } else if(size_j == upper_sum) {
      if(excluded_sizes[size_j] == 0) {         // Korf does not include this test.
         included[++n_included] = j;
         feasible(index+1, MAX(0,lower_sum - size_j), upper_sum - size_j, bin_data);
         included[n_included--] = 0;
      }
   } else {
      if(excluded_sizes[size_j] == 0) {         // Korf does not include this test.
         included[++n_included] = j;
         feasible(index+1, MAX(0,lower_sum - size_j), upper_sum - size_j, bin_data);
         included[n_included--] = 0;
      }

      excluded_sizes[size_j]++;      
      feasible(index+1, MAX(lower_sum,size_j+1), upper_sum, bin_data);
      excluded_sizes[size_j]--;         
   }
}

//_________________________________________________________________________________________________

int test_domination(int *items, bin_datapnt bin_data)
/*
   1. This function tests if a load is dominated.
   2. Based on Korf's algorithm in An Improved Algorithm for Optimal Bin Packing.
      a. Korf assumed that the largest item in the load is the fixed item.  I am not assuming this.
         The fixed item is the first item in the load.
   3. Description of the test.
      a. I = set of items included in the load.
      b. w = size of the fixed item in the load.  This item should be common to all the loads tested during a single
             call of bin_gen_nondominated_loads.
      c. I' = I\{w}.
      d. r = capacity - w.
      e. E = set of items excluded from the bin.
      f. s(Y) = sum of the sizes of the items in Y.
      g. I is dominated <==> there exists a subset of I'' of I' and x in E such that s(I'') <= x and x - s(I'') <= r - s(I').
                             (I.e. I' contains a subset sum that can be replaced by an excluded element w/o exceedingg the capacity.)
   4. Input Variables
      a. items = set of items in the load.  Assume sizes[items[2]] >= sizes[items[3]] >= ...
                 Do not assume sizes[items[1]] >= sizes[items[2]].
                 The number of items in items should be stored in items[0].                 
   5. Written 4/23/09
*/
{
   int      dominated, i, j, largest_size, n_items_in_load;
   int      s, s2, s3, size_i, size_of_load, stop, *subset_sums, wasted_space;

   dominated = 0;
   size_of_load = sum(sizes, items);

   // The load is dominated if an excluded item can be added without exceeding the capacity.

   i = 1;
   while((i <= excluded_sizes[0]) && (excluded_sizes[i] == 0)) i++;

   if(i > excluded_sizes[0]) {         // There are no excluded items, so the load is not dominated.
      return(dominated);
   } else {
      if(size_of_load + i <= capacity) {
         dominated = 1;
         return(dominated);
      }
   }

   // If an excluded item can replace a single item so as to increase the size of the load 
   // (without exceeding the capacity), then the load is dominated.

   wasted_space = capacity - size_of_load;
   n_items_in_load = items[0];

   if(wasted_space > 0) {
      for(j = 2; j <= n_items_in_load; j++) {
         i = items[j];
         size_i = sizes[i];
         stop = MIN(size_i+wasted_space, excluded_sizes[0]);
         for(s = size_i+1; s <= stop; s++) {
            if(excluded_sizes[s] > 0) {
               dominated = 1;
               return(dominated);
            }
         }
      }
   }

   // Main test.

   largest_size = sizes[bin_data->eligible[1]];
   MALLOC(subset_sums, largest_size+1, int);
   for(i = 0; i <= largest_size; i++) subset_sums[i] = 0;
   subset_sums[sizes[items[n_items_in_load]]] = 1;

   for(j = n_items_in_load-1; j >= 2; j--) {
      i = items[j];
      size_i = sizes[i];
      for(s = largest_size-size_i; s > 0; s--) {
         if(subset_sums[s] > 0) {
            s2 = s + size_i;
            if(subset_sums[s2] == 0) {
               
               // s2 is a subset sum that has not been encountered previously.
               // Update subset_sums and check if there exists an excluded item that can replace the subset.
               
               subset_sums[s2] = 1;
               stop = MIN(s2+wasted_space, excluded_sizes[0]);
               for(s3 = s2; s3 <= stop; s3++) {
                  if(excluded_sizes[s3] > 0) {
                     dominated = 1;
                     free(subset_sums);
                     return(dominated);
                  }
               }
            }
         }
      }
      subset_sums[size_i] = 1;
   }

   free(subset_sums);

   return(dominated);
}

/*************************************************************************************************/

int best_fit_decreasing(int *available_items, int *solution)
/*
   1. This function uses the best fit decreasing (BFD) heuristic to assign the items to the bins
      for the bin packing problem.
   2. The largest item is put into the first bin.  The remaining items are assigned in order to
      the fullest bin in which it will fit.  If an item does not fit into a bin, it is assigned
      to a new bin.
   3. This function uses an O(n^2) implementation, although the algorithm can be implemented to run in O(n log(n)).
   4. Input Variables
      a. available_items = list of items to pack into the bins.
                           The number of items in available_items should be stored in available_items[0].
                           This function assumes sizes(available_items(1)) >= sizes(available_items(2) >= ...
      b. bin = the number of the first bin to use.  This function is designed to be called during a branch & bound
               algorithm where some bins have already been filled.
   5. Output Variables
      a. n_bins_used = number of bins used in the solution constructed by the BFD heuristic.
      b. solution[i] = the bin to which item i was assigned.
                     = 0 if item i was not one of the available items.
   6. Written 4/24/09.
*/
{
   int      i, /*ii,*/ j, index, k, n_available_items, n_bins_used, new_remaining_size, n_open_bins, size_j;
   open_bin *open_bins;

   n_available_items = available_items[0];
   n_bins_used = 0;
   for(i = 1; i <= n_items; i++) solution[i] = 0;

   if(n_available_items == 0) return(n_bins_used);

   MALLOC(open_bins, n_available_items+1, open_bin);
   n_open_bins = 0;
   //for(i = 1; i <= n_available_items; i++) printf("%2d ", sizes[available_items[i]]); printf("\n");

   // Main loop.

   index = 1;
   for(i = 1; i <= n_available_items; i++) {
      j = available_items[i];
      size_j = sizes[j];
/*      
      printf("%2d %2d ", j, size_j); 
      if(n_open_bins > 0) {
         for(ii = 1; ii <= n_open_bins; ii++) printf("%2d ", open_bins[ii].remaining_size); printf("\n      "); 
         for(ii = 1; ii <= n_open_bins; ii++) printf("%2d ", open_bins[ii].bin); printf("\n");
      } else {
         printf("\n");
      }
*/
      // If there are no open bins, then put j into a new bin.
      
      if(n_open_bins == 0) {
         n_bins_used++;
         n_open_bins = 1;
         solution[j] = n_bins_used;
         open_bins[1].remaining_size = capacity - size_j;
         open_bins[1].bin = solution[j];
         index = 1;
         continue;
      }
         
      // Find the fullest bin into which j fits.
      
      if(size_j < open_bins[index].remaining_size) {
         while((index > 1) && (size_j <= open_bins[index-1].remaining_size)) index--;
      } else {
         while((index <= n_open_bins) && (size_j > open_bins[index].remaining_size)) index++;
         
         if(index > n_open_bins) {
            
            // Item j did not fit into any of the open bins, so it must be put into a new bin.
            // The new bin should always have the largest remaining space, so it should be added to the end of the list of open bins.
            
            n_bins_used++;
            n_open_bins++;
            solution[j] =n_bins_used;
            open_bins[n_open_bins].remaining_size = capacity - size_j;
            open_bins[n_open_bins].bin = solution[j];
            continue;
         }
      }
      
      // Put item j into the open bin.
      
      assert((0 < index) && (index <= n_open_bins));
      assert(size_j <= open_bins[index].remaining_size);
      if((index > 1) && (size_j < open_bins[index-1].remaining_size)) {fprintf(stderr,"Incorrect index in best_fit_decreasing\n"); exit(1);}

      solution[j] = open_bins[index].bin;
      open_bins[index].remaining_size = open_bins[index].remaining_size - size_j;
      
      if(open_bins[index].remaining_size > 0) {
         
         // Move the bin so that the bins are sorted.
         
         k = index - 1;
         new_remaining_size = open_bins[index].remaining_size;
         while((k > 0) && (open_bins[k].remaining_size > new_remaining_size)) {
            open_bins[k+1] = open_bins[k];
            k--;
         }
         open_bins[k+1].remaining_size = new_remaining_size;
         open_bins[k+1].bin = solution[j];
         
      } else {
         
         // Remove this bin from the list of open bins.  Slide all open bins with greater remaining space one unit to the left.
         
         for(k = index+1; k <= n_open_bins; k++) open_bins[k-1] = open_bins[k];
         n_open_bins--;
         if(index > n_open_bins) index = n_open_bins;
      }
   }

   //printf("%2d: ", n_bins_used); prn_vec(solution, n_items);
   free(open_bins);

   return(n_bins_used);
}

/*************************************************************************************************/

int bin_preprocess(int *eligible, int *remaining_items)
/*
  1. This function performs some simple preprocessing for the bin packing problem.
  2. Input Variables
     a. eligible = list of items that must be assigned to bins.
                   The number of items in eligible should be stored in eligible[0].
                   This function assumes sizes[eligible[1]] >= sizes[eligible[2] >= ...
  3. Output Variables
     a. n_bins_used = the number of bins used by the items that were put into bins by preprocessing.
     b. remaining_items contains the set of items that were not eliminated by preprocessing.
  4. Written 5/8/09.
*/
{
   int      i, j, n_bins_used, n_eligible, n_small, n_remaining;
   int    *small_items;

   assert(check_bin_preprocess_data(eligible) == 1);
   n_eligible = eligible[0];
   MALLOC(small_items, n_eligible+1, int);

   n_bins_used = 0;
   n_remaining = 0;
   n_small = 0;
   i = 1;
   j = n_eligible;
   while(i < j) {
      if(sizes[eligible[i]] + sizes[eligible[j]] > capacity) {
         remaining_items[++n_remaining] = eligible[i];
         i++;
      } else if(sizes[eligible[i]] + sizes[eligible[j]] == capacity) {
         // Items i and j fit perfectly into a single bin.
         n_bins_used++;
         i++;
         j--;
      } else {
         small_items[++n_small] = eligible[j];
         j--;
      }
   }

   if(i == j) {
      remaining_items[++n_remaining] = eligible[i];
   }

   assert(n_remaining + n_small + 2 * n_bins_used == n_eligible);

   for(i = n_small; i > 0; i--) {
      remaining_items[++n_remaining] = small_items[i];
   }
   remaining_items[0] = n_remaining;
   //prn_preprocess_info(eligible, n_bins_used, remaining_items);

   free(small_items);
   return(n_bins_used);
}
//_________________________________________________________________________________________________

int check_bin_preprocess_data(int *eligible)
/*
  1. This function performs some simple tests on the data input into the bin_preprocess function.
  2. Input Variables
     a. eligible = list of items that must be assigned to bins.
                   The number of items in eligible should be stored in eligible[0].
                   This function assumes sizes[eligible[1]] >= sizes[eligible[2] >= ...
  3. Output Variables
     a. 1 is returned if no errors are found, o.w. 0 is returned.
  4. Written 5/8/09.
*/
{
   int      i, n_eligible, prev_size, status;

   status = 1;
   n_eligible = eligible[0];

   prev_size = BIG_INT;
   for(i = 1; i <= n_eligible; i++) {
      if((sizes[eligible[i]] < 1) || (sizes[eligible[i]] > capacity)) {
         printf("Illegal entry in bin_preprocessing");
         status = 0;
         return(status);
      }
      if(prev_size < sizes[eligible[i]]) {
         printf("sizes are not sorted in bin_preprocess");
         status = 0;
         return(status);
      }
      prev_size = sizes[eligible[i]];
   }

   return(status);
}


/*************************************************************************************************/

void prn_loads(int depth, int *eligible, int ub)
{
   int      i, j, n_eligible;

   n_eligible = eligible[0];
   printf("%3d %3d\n", n_eligible, ub);
   for(i = 1; i <= n_eligible; i++) {
      printf("%2d ", sizes[eligible[i]]); 
   }
   printf("\n");

   printf("%2d\n", n_loads[depth]);
   for(i = 1; i <= n_loads[depth]; i++) {
      printf("%2d ", loads[depth][i][0]);
      for(j = 1; j <= loads[depth][i][0]; j++) {
         printf("%2d ", sizes[loads[depth][i][j]]);
      }
      printf("\n");
   }
}

//_________________________________________________________________________________________________

void prn_bfd_solution(int *eligible, int *solution, int z)
{
   int      i, n_eligible;

   n_eligible = eligible[0];
   printf("%3d %3d ", n_eligible, z);
   for(i = 1; i <= n_eligible; i++) {
      printf("%2d ", sizes[eligible[i]]); 
   }

   for(i = 1; i <= n_eligible; i++) {
      printf("%2d ", solution[eligible[i]]);
   }
   printf("\n");
}

//_________________________________________________________________________________________________

void prn_dfs_bbr_info(int *eligible, int depth, int lb, int z)
{
   int      i, /*index,*/ n_eligible;

   n_eligible = eligible[0];
   //index = hash_items(eligible);
   printf("%2d %2d %2d %2d ", depth, lb, z, n_eligible); 
   //printf("%2d %2d %2d %2d %8d ", depth, lb, z, n_eligible, index); 
   //prn_int(eligible, n_eligible); 
   //printf("          "); 
   for(i = 1; i <= n_eligible; i++) {
      printf("%2d ", sizes[eligible[i]]);
   } 
   printf("\n");
}

//_________________________________________________________________________________________________

void prn_preprocess_info(int *eligible, int n_bins_used, int *remaining_items)
{
   int      i, n_eligible, n_remaining;

   n_eligible = eligible[0];
   n_remaining = remaining_items[0];
   printf("%2d %2d %2d ", n_eligible, n_bins_used, n_remaining); 
   for(i = 1; i <= n_eligible; i++) {
      printf("%2d ", sizes[eligible[i]]);
   } 
   for(i = 1; i <= n_remaining; i++) {
      printf("%2d ", sizes[remaining_items[i]]);
   } 
   printf("\n");
}

//_________________________________________________________________________________________________

void prn_sizes(int *eligible, int n)
{
   int      i;

   for (i = 1; i <= n; i++) {
      printf("%2d ", sizes[eligible[i]]); 
   }
   printf("\n");
}


/*************************************************************************************************/

// See Fundamentals of Data Structure by Horowitz and Sahni and Algorithms in
// C++ by Sedgwick for explanations of hashing.

//_________________________________________________________________________________________________

void initialize_bin_hash_table()
/*
   1. This routine initializes the bin hash table.
   2. BIN_HASH_SIZE = the length of the hash table.  It must be a prime number.  
      Currently using linear probing, but if quadratic probing is used, then
      it must be a prime of the form 4j+3.  4000039=4*1000009+3
   3. This routine initializes the key of every entry in the hash table to NULL.
   4. n_in_bin_hash_table = # of entries stored in the bin hash table.
   5. Created 5/12/09 by modifying intitialize_hash_table from 
      c:\sewell\research\schedule\rtardy\cprogram\memory.c.
*/
{
   int      i;

   n_in_bin_hash_table = 0;
   for (i = 0; i < BIN_HASH_SIZE; i++) {
      bin_hash_table[i].key = NULL;
   }
}

//_________________________________________________________________________________________________

void compute_key(int *key, int *items)
/*
   1. This routine computes the key corresponding to a set of items.
   2. The jth bit of key is set to one if item j is in items, o.w. it is set to zero.
   3. Items are in positions 1,...,n.
      The number of items in items should be stored in items[0].
   4. Created 5/12/09 by modifying compute_key from 
      c:\sewell\research\schedule\rtardy\cprogram\memory.c.
*/
{
   int      i, n, n_bytes;

   n_bytes = (n_items / 8) + ((n_items % 8) == 0 ? 0 : 1);
   for (i = 0; i < n_bytes; i++) key[i] = 0;

   n = items[0];
   for (i = 1; i <= n; i++) {
      assert((1 <= items[i]) && (items[i] <= n_items));
      SET1(key, items[i]);
   }
}

//_________________________________________________________________________________________________

int hash_items(int *items)
/* 
   1. This routine computes the hash value of a set of items.
   2. It uses a simple modular hash function.
   3. items are in positions 1,...,n.
      The number of items in items should be stored in items[0].
   4. bin_hash_values[s] = hash value assigned to size s for the bin packing problem..
   5. The hash value is returned.
   6. Created 5/12/09 by modifying hash_jobs from 
      c:\sewell\research\schedule\rtardy\cprogram\memory.c.
*/
{
   int      i, index, n;

   index = 0;
   n = items[0];
   for (i = 1; i <= n; i++) {
      assert((1 <= items[i]) && (items[i] <= n_items));
      index = (index + bin_hash_values[sizes[items[i]]]) % BIN_HASH_SIZE;
   }
   return(index);
}

//_________________________________________________________________________________________________

int hash_key(int *key)
/* 
   1. This routine computes the hash value of a key.
   2. It uses a simple modular hash function.
   3. bin_hash_values[s] = hash value assigned to size s for the bin packing problem..
   4. The hash value is returned.
   6. Created 5/12/09 by modifying hash_key from 
      c:\sewell\research\schedule\rtardy\cprogram\memory.c.
*/
{
   int      i, index;

   index = 0;
   for (i = 1; i <= n_items; i++) {
      if (IN_SET(key,i)) index = (index + bin_hash_values[sizes[i]]) % BIN_HASH_SIZE;
   }
   return(index);
}

//_________________________________________________________________________________________________

int insert_in_bin_hash(int *items, int hash_index, int best_child, int z)
/*
   1. This routine uses the linear probing method to insert a
      a set of items into the bin hash table.
   2. hash_index = the index in the hash table to begin attempting to insert the items.
      If hash_index == 0, then it is computed from scratch using the items.
   3. -1 is returned if the hash table is full,
      -2 is returned if the key is already in the hash table,
      o.w. the index where the key is stored in bin_hash_table is returned.
   4. Created 5/12/09 by modifying insert_hash from 
      c:\sewell\research\schedule\rtardy\cprogram\memory.c.
*/
{
   int      index, n_bytes;

   if (n_in_bin_hash_table >= BIN_HASH_SIZE - 1) {
      fprintf(stderr, "Bin hash table is full\n");
      return(-1);
   }

   assert((0 <= hash_index) && (hash_index < BIN_HASH_SIZE));
   if (hash_index == 0)
      index = hash_items(items);
   else
      index = hash_index;
   assert((0 <= index) && (index < BIN_HASH_SIZE));
   while (bin_hash_table[index].key != NULL) {
      if (compare_sizes(bin_hash_table[index].key, items) == 1) {
         fprintf(stderr, "Key is already in the bin hash table\n");
         return(-2);
      } else {
         index = (index + 1) % BIN_HASH_SIZE;
      }
   }

   n_bytes = (n_items / 8) + ((n_items % 8) == 0 ? 0 : 1);
   MALLOC(bin_hash_table[index].key, n_bytes, int);
   compute_key(bin_hash_table[index].key, items);
   bin_hash_table[index].best_child = best_child;
   bin_hash_table[index].z = z;
   n_in_bin_hash_table++;

   return(index);
}

//_________________________________________________________________________________________________

int find_in_bin_hash(int *items, int hash_index)
/*
   1. This routine searches the bin hash table for a key that represents the same set of item sizes
      as those for items.
   2. It uses linear probing.
   3. If such a key is found, the index in the hash table is returned, 
      o.w., -1 is returned.
   4. hash_index = the index in the hash table to begin searching for the key.
      If hash_index == 0, then it is computed from scratch using items.
   5. Created 5/12/09 by modifying find_key from 
      c:\sewell\research\schedule\rtardy\cprogram\memory.c.
*/
{
   int      index;

   assert((0 <= hash_index) && (hash_index < BIN_HASH_SIZE));
   if (hash_index == 0)
      index = hash_items(items);
   else
      index = hash_index;
   assert((0 <= index) && (index < BIN_HASH_SIZE));
   while (bin_hash_table[index].key != NULL) {
      if (compare_sizes(bin_hash_table[index].key, items) == 1) {
         return(index);
      } else {
         index = (index + 1) % BIN_HASH_SIZE;
      }
   }
   return(-1);
}

//_________________________________________________________________________________________________

int compare_sizes(int *key, int *items)
/*
   1. This routine compares the set of items represented by key to determine if it represents
      the same set of sizes as the items in items.
   2. 1 is returned if the sets of sizes are the same, o.w. 0 is returned.
   3. Written 5/12/09.
*/
{
   int      i, n, n_key, status;
   int    *items_in_key;

   status = 1;

   // Determine which sizes are in the set of items represented by the key.
   // sizes_in_key[s] = number of items of size s in key.

   n_key = 0;
   MALLOC(items_in_key, n_items+1, int);
   for(i = 1; i <= n_items; i++) {
      if (IN_SET(key,i)) {
         sizes_in_key[sizes[i]]++;
         items_in_key[++n_key] = i;
      }
   }

   // Determine if items represents the same set of sizes.

   n = items[0];
   if(n == n_key) {
      for(i = 1; i <= n; i++) {
         if(sizes_in_key[sizes[items[i]]] > 0) {
            sizes_in_key[sizes[items[i]]]--;
         } else {
            status = 0;
            break;
         }
      }
   } else {
      status = 0;
   }

   // Reset sizes_in_key to zero.

   for(i = 1; i <= n_key; i++) sizes_in_key[sizes[items_in_key[i]]] = 0;
   free(items_in_key);

   return(status);
}

//_________________________________________________________________________________________________

void prn_bin_hash_table()
{
   int      /*cnt,*/ i, j, n_key, s;

   for(s = 1; s <= max_size; s++) printf("%4d ", bin_hash_values[s]);
   printf("\n");
   //cnt = 0;
   for(i = 0; i < BIN_HASH_SIZE; i++) {
      if(bin_hash_table[i].key != NULL) {
         printf("%8d %2d %8d: ", i, bin_hash_table[i].z, bin_hash_table[i].best_child);
         n_key = 0;
         for(j = 1; j <= n_items; j++) {
            if(IN_SET(bin_hash_table[i].key, j)) {
               sizes_in_key[sizes[j]]++;
               n_key++;
            }
         }
         for(s = max_size; s > 0; s--) {
            while(sizes_in_key[s] > 0) {
               printf("%2d ", s);
               sizes_in_key[s]--;
            }
         }
         printf("\n");
      }
   }
}

//_________________________________________________________________________________________________

void prn_bin_hash_table_entry(int index)
{
   int      j, n_key, s;

   for(s = 1; s <= max_size; s++) printf("%4d ", bin_hash_values[s]);
   printf("\n");
   printf("%8d %2d %8d: ", index, bin_hash_table[index].z, bin_hash_table[index].best_child);
   n_key = 0;
   for(j = 1; j <= n_items; j++) {
      if(IN_SET(bin_hash_table[index].key, j)) {
         sizes_in_key[sizes[j]]++;
         n_key++;
         printf("%2d ", j);
      }
   }
   printf("\n");
   for(s = max_size; s > 0; s--) {
      while(sizes_in_key[s] > 0) {
         printf("%2d ", s);
         sizes_in_key[s]--;
      }
   }
   printf("\n");
}

//_________________________________________________________________________________________________

int get_n_in_bin_hash_table()
{
   return(n_in_bin_hash_table);
}

}; // end namespace salb




