salbp
=====

Code for the simple assembly line balancing problem

Usage: ./salb probfile
    -b: 1 = use bin packing LB, 0 = do not use (def=0)
    -m: method (search_strategy) to use during Phase II 1 = DBFS, 2 = BFS (def=1)
    -p: controls level of printed information (def=0)
    -s: seed for random number generation
    -t: CPU time limit
    -d: Set direction (-1 = auto (default), 0 = reverse, 1 = forward)
    
Description
===========

This code reads in a simple assembly line balancing problem and performs a branch-and-bound search for the optimal
solution, as described in Sewell and Jacobson (2012).  The input file format supported is the .alb file format; if 
compiled under Linux, make sure the input file uses Unix-style line endings or the input procedure will not read the 
files correctly.

The total space allocated for the search tree is controlled by two defines at the beginning of bbr.h:

#define STATE_SPACE 
#define HASH_SIZE

The STATE_SPACE macro controls the size of the search tree, and the HASH_SIZE macro controls the size of the hash
table used to store the search tree states.  A general rule of thumb is that the HASH_SIZE should be about ten times the
size of the STATE_SPACE, and it must be a prime number.  You can use WolframAlpha to find a prime number that is close
to 10 * STATE_SPACE.

The output from the program is in the following format:

<task> <station>
...
<task> <station>
   verified_optimality = (0|1); value = X; cpu = X
Hoffman cpu = X  best_first_bbr cpu = X  bfs_bbr cpu = X find_insert_cpu = X bin_cpu = X cpu = X

The first group of lines prints the best solution found by the algorithm; the second line indicates whether BBR was 
able to verify optimality, the best solution it found, and the total running time in CPU seconds.  The last line breaks 
down the timing statistics into more detail for individual components of the algorithm.

Branches
========

There are two branches contained in this repository; the first is a "standard" implementation of the BBR code.  The
second uses a backtracking method as described in Morrison et al. (2013).  The normal implementation stores the 
complete information needed to reconstruct each partial solution at every subproblem in the search tree.  On the other
hand, the backtracking implementation only stores the tasks that have been assigned to the most recent station -- to 
construct the complete solution, the code must backtrack through the search tree.  This saves some amount of memory,
at the expense of about 30% computation time.


References
==========

Morrison, D. R., E. C. Sewell, and S. H. Jacobson. “A Computational Study of the Simple Assembly Line 
	Balancing Problem Using Cyclic Best-First Search.” Under review (June 2013).

Sewell, E. C, and S. H Jacobson. “A Branch, Bound, and Remember Algorithm for the Simple Assembly Line Balancing 
	Problem.” INFORMS Journal on Computing 24, no. 3 (2012): 433–442. doi:10.1287/ijoc.1110.0462.


