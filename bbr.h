#include  <stdio.h>
#include  <stdlib.h>   
#include  <time.h>
#include  <assert.h>
#include  <math.h>
#include  <memory.h>
#include <vector>

namespace salb
{

#define  MALLOC(x,n,type) do {                                         \
         if ((x = (type *) malloc( (n) * sizeof(type))) == NULL) {     \
	         fprintf(stderr,"out of memory\n");                         \
            fprintf(stderr,"x %d type\n",n);                           \
	         exit(1);                                                   \
	 }} while (0)
#define  ABS(i) ((i < 0) ? -(i) : (i) )
#define  MAX(i,j) ((i < j) ? (j) : (i) )
#define  MIN(i,j) ((i < j) ? (i) : (j) )

#define IN_SET(set,j) ((set[(j-1)/8] << ((j-1) % 8)) & 128)  // Return the value of bit j
#define SET1(set,j) (set[(j-1)/8] |= (128 >> ((j-1) % 8)))   // Set bit j to one
#define SET0(set,j) (set[(j-1)/8] &= ~(128 >> ((j-1) % 8)))  // Set bit j to zero

#define  MAX_N_TASKS 500
#define  BIG_INT 2147483647
#define  STATE_SPACE  80000000 /* allocate space for this many states  */
#define  HASH_SIZE 800000011 // Must be a prime number.  Currently using linear
                            // probing, but if quadratic probing is used, then
                            // it must be a prime of the form 4j+3.  20000003=4*5000000+3   40000003=4*10000000+3
//#define  HEAP_SIZE 30000000   // Maximum number of elements in a heap.


typedef struct searchinfo {
   int     best_branch;         // branch at which best schedule was found
   int     n_branches;          // # of branches in branch & bound tree
   int     n_generated;         // # of subproblems generated
   int     n_explored;          // # of states explored
   int     n_states;            // # of states in dynamic program
   clock_t start_time;          // starting cpu time
   clock_t end_time;            // ending cpu time
   double  best_cpu;            // time at which best schedule was found
   double  cpu;                 // cpu used during search process
   double  states_cpu;          // cpu used to find and store states
   double  hoffman_cpu;			// cpu used by hoffman heuristic
   double  best_first_cpu;		// cpu used by best_first_bbr heuristic
   double  bfs_bbr_cpu;			// cpu used by bfs_bbr algorithm
   double  find_insert_cpu;   // cpu used by find_or_insert
   double  bin_cpu;           // cpu used by bin packing functions
} searchinfo, *search_infopnt;

struct state {
   int* assigned_tasks;
   int  n_assigned_tasks;
   int  n_stations;
   int  LB;            // The best lower bound computed for this state.
   int   previous;      // Previous state.  Used in backtracking to constuct optimal solution
   char  open;          // = 1 if this state has not been explored yet.
} __attribute__((packed));
typedef struct state state, *statepnt;

typedef struct backtrackinfo
{
	~backtrackinfo() { free(degrees); }
	int* degrees;
	int idle;
	unsigned int hash_value;
} backtrackinfo;

typedef struct hash_record {
   int   index;
} hash_record, *hash_recordpnt;

typedef struct heap_record {
   double   key;
   int      index;
} heap_record, *heap_recordpnt;

typedef struct problem {
   const char  *file_name;
   int   cycle_times[28];
   int   upper_bounds[28];
} problem, *problempnt;

typedef struct bin_hash_record {
   int *key;                   // Used as a bit vector.  Bit i = 1 iff item i has not yet been assigned to a bin.
   int   z;                      // Optimal number of bins for this state.
   int   best_child;             // index in the bin_hash_table where the best child is stored.  Used
                                 // for backtracking.  -1 indicates all items packed or BFD heuristic is optimal.
} bin_hash_record, *bin_hash_recordpnt;

typedef struct bin_data {
   int      bin;                 // The number of the bin that is being loaded.
   int    *eligible;           // Points to the list of items that are eligible to be assigned to this bin.
   int      lb1_sum;             // Sum of the sizes of the eligible items.
   double   lb2_sum;             // Sum of the lb2 values of the eligible items.
   double   lb3_sum;             // Sum of the lb3 values of the eligible items.
   int      ub;                  // Upper bound on the number of bins needed for all the eligible items.
} bin_data, *bin_datapnt;

typedef struct open_bin {
   int      remaining_size;      // The amount of space left in the bin.
   int      bin;                 // The number of this bin.
} open_bin, *open_binpnt;

extern   searchinfo search_info;
extern   int      first_state;            // index (in states) where first unexplored is stored
extern   int      last_state;             // index (in states) last  state is stored
extern   state*   states;				  // Stores states
extern   heap_record **dbfs_heaps;
extern   heap_record *bfs_heap;
extern   int      cycle;                  // Cycle time for the stations
extern   int      n_tasks;                // number of tasks
extern   int      UB;                     // upper bound on the number of stations needed
extern   char     **predecessor_matrix;   // predecessor_matrix(i,j) = 1 indicates that i immediately precedes j.
extern   char     **closed_predecessor_matrix;   // closed_predecessor_matrix(i,j) = 1 indicates that i precedes j.
extern   char     **potentially_dominates;// potentially_dominates[i][j] = 1 if task i potentially dominates task j.
extern   int **predecessors;         // predecessors[j] = vector of immediates predecessors of task j.
extern   int **successors;           // successors[j] = vector of immediates successors of task j.
extern   int      *t;                     // t[i] = processing time of task i
extern   int      *n_successors;          // n_successors[i] = number of successors of i in closed graph.
extern   int      *n_predecessors;        // n_predecessors[i] = number of predecessors of i in closed graph.
extern   int      *positional_weight;     // positional_weight[i] = t[i] + sum(t[j]: j is a successor of i).
extern   int	  *hash_values;           // hash_values(j) = hash value assigned to task j.
extern   double   *LB2_values;            // LB2_values[j] = the value assigned to task j to use in computing LB2.
extern   double   *LB3_values;            // LB3_values[j] = the value assigned to task j to use in computing LB3.
extern   int      *descending_order;      // descending_order[k] = the task with the kth largest processing time. 
extern   int      *sorted_task_times;     // sorted_task_times[k] = the kth largest processing time.
extern   int      verified_optimality;    // verified_optimality = 1 (0) if best_first_bbr proved optimality
extern   int      state_space_exceeded;   // state_spaced_exceeded = 1 (0) if we attempt to store more than STATE_SPACE states
extern   char     *prob_file;             // problem file
extern   float    alpha;
extern   float    beta;
extern   float    gimmel;
extern   int      bin_pack_flag;
extern   int      bin_pack_lb; // -b option: 1 = use bin packing LB, 0 = do not use
extern   int      search_strategy;  /* -m option: search_strategy during Phase II                       
                                       1 = distributed best first search
                                       2 = best first search */
extern   int      prn_info;    // -p option: controls level of printed info
extern   double   seed;        // -s option: seed for random number generation
extern	 int CPU_LIMIT;
extern   int*     heap_sizes;
extern   clock_t  global_start_time;
extern int* root_degrees;


// Functions in bbr.c

void parseargs(int ac, char **av);
void usage (char *prog);
void testprob();
void close_pred();
void reverse_pred();
void find_successors();
void compute_potentially_dominates();
void compute_LB2_values();
void compute_LB3_values();
void compute_positional_weights();
void compute_descending_order();
int LB3b();
int sum(int *x, int *indices);
double sum_double(double *x, int *indices);
double ggubfs(double *dseed);
int randomi(int n, double *dseed);

// Functions in bfs_bbr.c

void initialize_bfs_bbr();
void free_bfs_bbr();
void bfs_bbr(int upper_bound);
void gen_loads(int depth, int remaining_time, int start, int n_eligible);
void backtrack(int index);
int check_solution(int *stations, int n_stations);
int check_state(int index);
void prn_load(int depth);

// Functions in io.c

void read_problem(const char *f);
void prn_problem();
void prn_tasks(int *tasks, int n);
void prn_pred(char **predecessor_matrix);
void prn_successors();
void prn_vec(int *vector, int n);
void prn_int(int *vector, int n);

// Functions in hoffman.c

void initialize_hoffman();
void free_hoffman();
int hoffman(int *deg, int max_idle, int starting_station, int max_loads);
void gen_load(int depth, int remaining_time, int start, int n_eligible, float cost);
int check_stations(int *deg, int *stations, int *start_station, int n_stations);

// Functions in memory.c

void initialize_states();
void reinitialize_states();
void store_state(int *degrees, int n_stations, int LB, int previous, const std::vector<int>& tmp_assigned_tasks);
int get_state();
backtrackinfo* get_state_info(int index);
void prn_states(int n_stations);
void initialize_hash_table();
void free_hash_table();
int find_or_insert(double key, int *degrees, int n_stations, int LB, int idle, long hash_value, int previous, int method, int *status);
void initialize_heaps();
void reinitialize_heaps();
void free_heaps();
int get_min();
int delete_min(heap_record *heap);
void insert(heap_record** heap, int* heap_size, double key, int *degrees, int n_stations, int LB, int previous, int add_to_states, const std::vector<int>& tmp_assigned_tasks);
void siftup(heap_record *heap, int k);
void siftdown(heap_record *heap, int k);

// Functions in anneal.c

void initialize_anneal();
void free_anneal();
int sim_anneal(int desired_cycle, int *initial_stations, int n_stations, int n_iters, double beta, double tk);
void gen_move(int *stations, int *cycle_times, int n_stations, int *task, int *new_station);
int movecost(int *cycle_times, int n_stations, int task, int new_station);
void move(int *cycle_times, int task, int new_station);
void gen_swap_move(int *stations, int *cycle_times, int max_cycle_time, int n_stations, int *task1, int *task2);
int swap_move_cost(int *stations, int *cycle_times, int n_stations, int task1, int task2);
void swap_move(int *stations, int *cycle_times, int n_stations, int task1, int task2);
void gen_initial_assignment(int desired_cycle, int *stations, int n_stations);
int check_assignment(int *stations, int n_stations, int max_cycle_time);

// Functions in best_first_bbr.c

void initialize_best_first_bbr();
void free_best_first_bbr();
void best_first_bbr(int upper_bound);
void gen_loads2(int depth, int remaining_time, int start, int n_eligible);

// Functions in bin_packing.c

void initialize_bin_packing();
void free_bin_packing();
int bin_dfs_bbr(int *list_of_items);
int dfs_bbr(int depth, int *eligible, int bin_hash_value, int lb1_sum, double lb2_sum, double lb3_sum, int *index);
void bin_backtrack(int index);
int bin_backtrack2(int index);
void check_bin_solution(int *items, int *solution, int n_bins);
int check_child(int *items, int best_child);
void bin_gen_nondominated_loads(int depth, int *eligible, int fixed_item, int lb1_sum, double lb2_sum, double lb3_sum, int ub);
void feasible(int index, int lower_sum, int upper_sum, bin_datapnt bin_data);
int test_domination(int *items, bin_datapnt bin_data);
int best_fit_decreasing(int *available_items, int *solution);
int bin_preprocess(int *eligible, int *remaining_items);
int check_bin_preprocess_data(int *eligible);
void prn_loads(int depth, int *eligible, int ub);
void prn_bfd_solution(int *eligible, int *solution, int z);
void prn_dfs_bbr_info(int *eligible, int depth, int lb, int z);
void prn_preprocess_info(int *eligible, int n_bins_used, int *remaining_items);
void prn_sizes(int *eligible, int n);
void initialize_bin_hash_table();
void compute_key(int *key, int *items);
int hash_items(int *items);
int hash_key(int *key);
int insert_in_bin_hash(int *items, int hash_index, int best_child, int z);
int find_in_bin_hash(int *items, int hash_index);
int compare_sizes(int *key1, int *items);
void prn_bin_hash_table();
void prn_bin_hash_table_entry(int index);
int get_n_in_bin_hash_table();

}; // end namespace salb;



