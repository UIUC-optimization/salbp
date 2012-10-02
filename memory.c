#include "bbr.h"

namespace salb
{

/*****************************************************************************/

/*
   1. The following functions manage the list of states for the simple assembly line balancing problem.
   2. A state is defined by
      a. degrees[i] =     The number of immediate predecessors of task i not yet assigned to a workstation
      b. n_stations =     The total number of work stations that have been used so far
      c. LB =             The best lower bound computed for this state.
      d. int   idle;      The total idle time for this state = cycle*n_stations - sum(i: degree[i]=-1) t[i]
      e. hash_value = -1  The hash value of the jobs that have been assigned to a workstation
      f. previous;        Previous state.  Used in backtracking to constuct optimal solution
   3. The space for all the states is pre-allocated in the array states.
   4. next_state = the index (minus 1) in states where the next state can be stored.
   5. Written 3/3/06.
*/

void initialize_states()
{
   int      i;

   first_state = 0;
   last_state = -1;

   //for(i = 0; i <= STATE_SPACE; i++) states[i].n_stations = -1;
}

//_________________________________________________________________________________________________

void reinitialize_states()
{
   int      i;

   for(i = 0; i <= last_state; i++) {
      //states[i].n_stations = -1;
      free(states[i].degrees);
   }

   first_state = 0;
   last_state = -1;
}

//_________________________________________________________________________________________________

void store_state(char *degrees, char n_stations, char LB, int idle, int hash_value, int previous)
/*
   1. This routine stores a new state in the array states.
      a. It stores it in the next available position, which is determined
         by last_state.
   2. If there is insufficient space for the new state, then the program is exited.
   3. The index (in states) is returned.
   4. Written 3/3/06.
*/
{
   int      i;
   clock_t  start_time;

   start_time = clock();

   assert((-1 <= previous) && (previous <= STATE_SPACE));
   assert((0 <= n_stations) && (n_stations <= n_tasks));
   assert((0 <= hash_value) && (hash_value < HASH_SIZE));

   last_state++;
   if (last_state >= STATE_SPACE) {
      verified_optimality = 0;
      state_space_exceeded = 1;
      fprintf(stderr, "Out of space for states\n");
	   printf("   verified_optimality = %d; value = %d; cpu = %0.2f\n", verified_optimality, UB, ((double)(clock() - global_start_time)/CLOCKS_PER_SEC));
	   if(verified_optimality == 0) printf("   ************* DID NOT VERIFY OPTIMALITY ************\n");
      //return;
      exit(1);
   }

   search_info.n_states++;
   
   states[last_state].n_stations = n_stations;
   states[last_state].LB = LB;
   states[last_state].idle = idle;
   states[last_state].hash_value = hash_value;
   states[last_state].previous = previous;
   states[last_state].open = 1;
   MALLOC(states[last_state].degrees, n_tasks+1, char);
   states[last_state].degrees[0] = 0;
   for(i = 1; i <= n_tasks; i++) states[last_state].degrees[i] = degrees[i];
   
   search_info.states_cpu += (double) (clock() - start_time) / CLOCKS_PER_SEC;
}

//_________________________________________________________________________________________________

int get_state()
/*
   1. This function gets the next state from the list of states.
   2. The list uses a FIFO discipline (to implement breadth first search).
   3. first_state = the index in states of the first open state.
   4. last_state = the index in states of the last open state.
   5. STATE_SPACE = maximum number of states permitted.
   6. -1 is returned, if there are no open states 
      index of the next open states is returned o.w.
   7. Written 3/3/06.
*/
{
   int      index;

   if(first_state > last_state) {
      index = -1;
   } else {
      index = first_state;
      first_state++;
   }
   return(index);
}


//_________________________________________________________________________________________________

void prn_states(int n_stations)
{
   int      i, j;

   for(i = 0; i <= last_state; i++) {
      if(states[i].n_stations == n_stations) {
         printf("%6d  %2d %7d (", i, states[i].n_stations, states[i].hash_value);
         for(j = 1; j <= n_tasks; j++) {
            if(states[i].degrees[j] == -1) {
               printf("%2d ", j);
            }
         }
         printf(")\n");
      }
   }
}

/*****************************************************************************/

// See Fundamentals of Data Structure by Horowitz and Sahni and Algorithms in
// C++ by Sedgwick for explanations of hashing.

static int  n_in_hash_table;
static hash_record* hash_table;

//_________________________________________________________________________________________________

void initialize_hash_table()
/*
   1. This routine initializes the hash table.
   2. HASH_SIZE = the length of the hash table.  It must be a prime number.  
      Currently using linear probing, but if quadratic probing is used, then
      it must be a prime of the form 4j+3.  4000039=4*1000009+3
   3. This routine initializes the index of every entry in the hash table to -1.
   4. n_in_hash_table = # of entries stored in the hash table.
   5. Written 3/3/06.
*/
{
   int      i;

   MALLOC(hash_table, HASH_SIZE, hash_record);

   n_in_hash_table = 0;
   for (i = 0; i < HASH_SIZE; i++) {
      hash_table[i].index = -1;
   }
}

void free_hash_table()
{
	free(hash_table);
}

//_________________________________________________________________________________________________

int find_or_insert(double key, char *degrees, char n_stations, char LB, int idle, int hash_value, int previous, int method, int *status)
/*
   1. This routine uses the linear probing method to search the hash table
      for a state.
   2. If the state is found, then
      a. If the new state dominates the old one, then the old one is replaced by the new one.
      b. If the old state dominates the new one, then the new one is discarded.
   3. If the state is not found, then it is inserted into the hash table (unless the hash table is full).
   4. hash_value = the index in the hash table to begin searching for the subproblem.
   5. index = the index where the state is stored in states
   6. method = 1 insert the state into the heap for best first search.
             = 0 do not use the heap
   7. status = 2 if this state replaced an existing state
             = 1 if this state was not in states
             = 0 if this state was dominated by an existing state
   8. Written 3/3/06.
   7. Modified 5/19/09.
      a. status = 3 if this subproblem strictly dominates an existing subproblem (i.e., has the same set of scheduled tasks, but uses fewer stations)
                = 2 if this subproblem is equivalent to an existing subproblem (i.e., has the same set of scheduled tasks and uses the same number of stations)
                = 1 if this subproblem was strictly dominated by an existing subproblem
                = 0 if this subproblem was not in the hash table
                = -1 if the hash table was full.
      b. set hash_table(index).open equal to 1 if the new subproblem strictly dominates the old one.

*/
{
   int hash_index, index;
   clock_t  start_time;

   start_time = clock();

   // Do not perform the search if the hash table is full.

   if (n_in_hash_table >= HASH_SIZE - 1) {
      verified_optimality = 0;
      fprintf(stderr, "Hash table is full\n");
      exit(1);
   }

   // Search for the key.  Return index if it is found.

   hash_index = hash_value;
   assert((0 <= hash_index) && (hash_index < HASH_SIZE));
   while ((index = hash_table[hash_index].index) != -1) {
      if (memcmp(states[index].degrees+1, degrees+1, n_tasks) == 0) {
         if(n_stations < states[index].n_stations) {
            states[index].n_stations = n_stations;
			   states[index].hash_value = hash_value;
			   states[index].previous = previous;
            *status = 3;
            if((states[index].open == 0) && (method == 1)) {
               //printf("   State uses fewer stations\n");
               switch (search_strategy) {
                  case 1:  insert(&dbfs_heaps[n_stations], heap_sizes + n_stations, key, degrees, n_stations, LB, idle, hash_value, previous, 0); break;
                  case 2:  insert(&bfs_heap, heap_sizes, key, degrees, n_stations, LB, idle, hash_value, previous, 0); break;
                  default: fprintf(stderr,"Unknown search_strategy in find_or_insert\n"); exit(1); break;
               }
            }
         } else if(n_stations == states[index].n_stations) {
            *status = 2;
         } else {
            *status = 1;
         }
         search_info.find_insert_cpu += (double) (clock() - start_time) / CLOCKS_PER_SEC;
         return(index);
      } else {
         hash_index = (hash_index + 1) % HASH_SIZE;
      }
   }

   // The state was not found, so insert it into states.

   if(method == 1) {
      switch (search_strategy) {
         case 1:  insert(&dbfs_heaps[n_stations], heap_sizes + n_stations, key, degrees, n_stations, LB, idle, hash_value, previous, 1); break;
         case 2:  insert(&bfs_heap, heap_sizes, key, degrees, n_stations, LB, idle, hash_value, previous, 1); break;
         default: fprintf(stderr,"Unknown search_strategy in find_or_insert\n"); exit(1); break;
      }
   } else {
      store_state(degrees, n_stations, LB, idle, hash_value, previous);
   }
   *status = 0;
   index = last_state;
   hash_table[hash_index].index = index;

   n_in_hash_table++;
   
   search_info.find_insert_cpu += (double) (clock() - start_time) / CLOCKS_PER_SEC;
   return(index);
}

/*****************************************************************************/

// Binary heaps.
// See Network Flows by Ahuja, Magnanti, and Orlin; and Algorithms in
// C++ by Sedgwick for explanations of heaps.
//

/*
   1. The following functions manage the heaps for implementing a best bound search.
   2. A state is defined by
      a. degrees[i] =     The number of immediate predecessors of task i not yet assigned to a workstation
      b. n_stations =     The total number of work stations that have been used so far
      c. hash_value = -1  The hash value of the jobs that have been assigned to a workstation
      d. previous;        Previous state.  Used in backtracking to constuct optimal solution
   3. The states are stored in the array states.  The heaps provide a mechanism to locate the open state
      with the best bound.
   4. An item in the heap is defined by
      a. key = a number that measures the quality of the state corresponding to this item.
         It is used in deciding which open state should be chosen next.
      b. index = the index of this state in the array states.
   5. A single heap consists of a vector of heap_record.
      a. The items of the heap are stored in heap[1], heap[2], ...
      b. heap[0].index = number of items currently in the heap.
   6. heaps is an array of heap_record.  Each row of heaps is a heap.
      a. heap[m] is a heap for all the open states that use m workstations.
   7. HEAP_SIZE = maximum number of items in a heap.
   8. Written 3/30/06.
*/

//_________________________________________________________________________________________________

void initialize_heaps()
{
   int      i;
   int initHeapSize = 100000;

   switch (search_strategy) 
   {
      case 1:  MALLOC(dbfs_heaps, n_tasks+1, heap_record *);
			   MALLOC(heap_sizes, n_tasks+1, int);
               for(i = 0; i <= UB; i++) 
			   {
				  heap_sizes[i] = initHeapSize;
                  MALLOC(dbfs_heaps[i], initHeapSize+1, heap_record);
                  dbfs_heaps[i][0].index = 0;
               }
               for(i = UB + 1; i <= n_tasks; i++) MALLOC(dbfs_heaps[i], 1, heap_record);
               break;

      case 2:  MALLOC(heap_sizes, 1, int);
			   MALLOC(bfs_heap, STATE_SPACE+1, heap_record);   // Use STATE_SPACE instead of HEAP_SIZE so that there is enough room to store all the states in one heap.
			   heap_sizes[0] = initHeapSize;
               bfs_heap[0].index = 0;
               break;

      default: fprintf(stderr,"Unknown search_strategy in initialize_heaps\n"); exit(1); break;
   }
}

//_________________________________________________________________________________________________

void reinitialize_heaps()
{
   int      i;

   switch (search_strategy) {
      case 1:  for(i = 0; i <= n_tasks; i++) dbfs_heaps[i][0].index = 0; break;
      case 2:  bfs_heap[0].index = 0; break;
      default: fprintf(stderr,"Unknown search_strategy in reinitialize_heaps\n"); exit(1); break;
   }
}

//_________________________________________________________________________________________________

void free_heaps()
{
   int      i;

   switch (search_strategy) {
      case 1:  for(i = 0; i <= n_tasks; i++) free(dbfs_heaps[i]); free(dbfs_heaps); break;
      case 2:  free(bfs_heap); break;
      default: fprintf(stderr,"Unknown search_strategy in free_heaps\n"); exit(1); break;
   }
   free(heap_sizes);
}

//_________________________________________________________________________________________________

int get_min()
/*
   1. This gets (and deletes) the item with minimum key from the next nonempty heap.
   2. The index of this item is returned.
   3. Written 3/30/06.
*/
{
   int         i, index;
   static int  m = 0;

   switch (search_strategy) {
      case 1:  index = -1;
               m = (m + 1) % UB;
               for(i = 1; i <= UB; i++) {
                  if(dbfs_heaps[m][0].index > 0) {
                     index = delete_min(dbfs_heaps[m]);
                     return(index);
                  } else {
                     m = (m + 1) % UB;
                  }
               }
               return(index);
               break;
      case 2:  index = -1;
               if(bfs_heap[0].index > 0) index = delete_min(bfs_heap);
               return(index);
               break;
      default: fprintf(stderr,"Unknown search_strategy in get_min\n"); exit(1); break;
   }
}

//_________________________________________________________________________________________________

int delete_min(heap_record *heap)
/*
   1. This function deletes the item with minimum key from the heap.
   2. The index of this item is returned.
   3. Written 3/23/06.
*/
{
   int         index, n_in_heap;

   n_in_heap = heap[0].index;
   if(n_in_heap <= 0) return(-1);

   index = heap[1].index;
   heap[1] = heap[n_in_heap];
   n_in_heap--;
   heap[0].index = n_in_heap;
   siftdown(heap, 1);
   return(index);
}

//_________________________________________________________________________________________________

void insert(heap_record** heap, int* heap_size, double key, char *degrees, char n_stations, char LB, int idle, int hash_value, int previous, int add_to_states)
/*
   1. This function inserts a state into the heap and calls store_state to add it to the list of states.
   2. add_to_states = 1 indicates that store_state should be called.
   2. Written 3/23/06.
*/
{
   int      n_in_heap;

   n_in_heap = (*heap)[0].index;
   if(n_in_heap >= *heap_size)
   {
	   if ((*heap_size) * 2 > STATE_SPACE)
	   {
		   if (verified_optimality == 1) printf("heap full\n");
		   verified_optimality = 0;
		   return;
	   }

	   else
	   { 
		   printf ("resizing heap\n");
		   *heap_size *= 2;
		   *heap = (heap_record*)realloc(*heap, (*heap_size + 1) * sizeof(heap_record));
	   }
   } 

   n_in_heap++;
   (*heap)[0].index = n_in_heap;
   (*heap)[n_in_heap].key = key;
   store_state(degrees, n_stations, LB, idle, hash_value, previous);
   (*heap)[n_in_heap].index = last_state;
   siftup(*heap, n_in_heap);
}

//_________________________________________________________________________________________________

void siftup(heap_record *heap, int k)
/*
   1. This function performs a siftup operation on the item in position k.
   2. It repeatedly swaps the item in position k with its parent until either it becomes the root or
      or its keys is larger than its parent.
   3. Written 3/23/06.
*/
{
   int         k2;
   heap_record temp;

   k2 = k / 2;
   while((k > 1) && (heap[k2].key > heap[k].key)) {
      temp = heap[k2];
      heap[k2] = heap[k];
      heap[k] = temp;
      k = k2;
      k2 = k / 2;
   }
}

//_________________________________________________________________________________________________

void siftdown(heap_record *heap, int k)
/*
   1. This function performs a siftdown operation on the item in position k.
   2. It repeatedly swaps the item in position k with its smallest child until either it becomes a leaf or
      or its keys is smaller than both its children.
   3. Written 3/23/06.
*/
{
   int         j, n_in_heap;
   heap_record temp;

   n_in_heap = heap[0].index;
   j = k + k;
   while(j <= n_in_heap) {
      if((j < n_in_heap) && (heap[j].key > heap[j+1].key)) j++;
      if(!(heap[k].key > heap[j].key)) break;
      temp = heap[j];
      heap[j] = heap[k];
      heap[k] = temp;
      k = j;
      j = k + k;
   }
}

}; // end namespace salb



