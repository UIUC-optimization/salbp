#include "bbr.h"

void read_problem(char *f)
/*
   1. This function was created 2/24/06 by modifying read_problem from
      c:\sewell\research\schedule\rtardy\cprogram\io.c.
*/
{
   FILE     *in,*fopen();
   int      i, j, k;
   int      tt;

   if ((in = fopen(f,"r")) == NULL) {
      fprintf(stderr,"Unable to open %s for input\n",f);
      exit(1);
   }

   fscanf(in,"%d",&n_tasks);
   MALLOC(t,n_tasks+1,int);
   t[0] = n_tasks;

   for(i = 1; i <= n_tasks; i++) {
      fscanf(in,"%d",&tt);
      t[i] = tt;
   }

   MALLOC(predecessor_matrix, n_tasks+1, char *);
   for(i = 1; i <= n_tasks; i++) {
      MALLOC(predecessor_matrix[i], n_tasks+1, char);
      for(j = 1; j <= n_tasks; j++) {
         predecessor_matrix[i][j] = 0;
      }
   }

   for(k = 1; k <= n_tasks*n_tasks; k++) {
      fscanf(in, "%d, %d", &i, &j);
      if((i == -1) & (j == -1)) {
         break;
      }
      if ((i == j) || (i < 1) || (i > n_tasks) || (j < 1) || (j > n_tasks)) {
         fprintf(stderr,"Error reading predecessors.\n");
         return;
      }
      predecessor_matrix[i][j] = 1;
   }

   MALLOC(hash_values, n_tasks+1, int);
   for (i = 1; i <= n_tasks; i++) {
      hash_values[i] = randomi(HASH_SIZE, &seed) - 1;
   }

   fclose(in);
}


void prn_problem()
/*
   1. This function was created 2/24/06 by modifying prn_problem from
      c:\sewell\research\schedule\rtardy\cprogram\io.c.
*/
{
   int      i;

   printf("\n");
   printf("%d\n",n_tasks);
   for(i = 1; i <= n_tasks; i++) {
      printf("%3d %3d\n", i, t[i]);
   }
   prn_pred(predecessor_matrix);
   //prn_successors();
}


void prn_tasks(short *tasks, int n)
{
   int      i, j;

   for (i = 1; i <= n; i++) {
      j = tasks[i];
      printf("%2d ", j); 
   }
   printf("\n");
}


void prn_pred(char **predecessor_matrix)
{
   int      i, j;

   for (i = 1; i <= n_tasks; i++) {
      for (j = 1; j <= n_tasks; j++) {
         printf("%1d ", predecessor_matrix[i][j]);
      }
      printf("\n");
   }
}


void prn_successors()
{
   int      i, j;

   for (i = 1; i <= n_tasks; i++) {
      printf("%3d: ", i);
      for (j = 1; j <= successors[i][0]; j++) {
         printf("%3d ", successors[i][j]);
      }
      printf("\n");
   }
}

void prn_vec(int *vector, int n)
{
   int      i;

   for (i = 1; i <= n; i++) {
      printf("%2d ", vector[i]); 
   }
   printf("\n");
}

void prn_short(short *vector, int n)
{
   int      i;

   for (i = 1; i <= n; i++) {
      printf("%2d ", vector[i]); 
   }
   printf("\n");
}

