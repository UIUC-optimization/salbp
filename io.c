#include "bbr.h"
#include <fstream>
#include <sstream>

using namespace std;

namespace salb
{

void read_problem(const char *f)
/*
   1. This function was created 2/24/06 by modifying read_problem from
	  c:\sewell\research\schedule\rtardy\cprogram\io.c.
*/
{
   int      i, j;

	ifstream input(f);
	if (!input) 
	{
		fprintf(stderr, "Unable to open %s for input\n", f);
		exit(1);
	}
	
	string line;
	while(getline(input, line))
	{
		if (line[0] == '<' || line == "") continue;
		stringstream(line) >> n_tasks;
		printf("n=%d\n", n_tasks);	//added by AS 2013/06/06
		break;
	}
	while (getline(input, line))
	{ 
		if (line[0] == '<' || line == "") continue;
		stringstream(line) >> cycle;
		printf("cycle time=%d\n", cycle);  //added by AS 2013/06/06
		break; 
	}

   MALLOC(t,n_tasks+1,int);
   MALLOC(optimalsolution,n_tasks+1,int);	//added by AS 2013/06/06
   optimalsolution[0]=n_tasks+1;			//added by AS 2013/06/06
   t[0] = n_tasks;

	for (i = 1; i <= n_tasks; ++i)
	{
		getline(input, line);
		if (line[0] == '<' || line == "") { --i; continue; };
		int dummy;
		stringstream(line) >> dummy >> t[i];
		printf("t%d=%d ", i, t[i]);    //added by AS 2013/06/06
	}
	printf("\n");

   MALLOC(predecessor_matrix, n_tasks+1, char *);
   for (i = 1; i <= n_tasks; i++) 
   {
	  MALLOC(predecessor_matrix[i], n_tasks+1, char);
	  for (j = 1; j <= n_tasks; j++) 
		 predecessor_matrix[i][j] = 0;
   }

	while (getline(input, line))
	{
		if (line[0] == '<' || line == "") continue;

		stringstream sline(line);
		sline >> i;
		sline.ignore();
		sline >> j;
		//printf("%d,%d\n ", i, j);

		if ((i == j) || (i < 1) || (i > n_tasks) || (j < 1) || (j > n_tasks))
		{
			fprintf(stderr, "Error reading predecessors.\n");
			return;
		}
		
		predecessor_matrix[i][j] = 1;
	}

   MALLOC(hash_values, n_tasks+1, int);
   for (i = 1; i <= n_tasks; i++) 
	  hash_values[i] = randomi(HASH_SIZE, &seed) - 1;

}

//added by AS 2013/06/06
void write_solution(char *f)
{
    ofstream file;
	char *pcTmp, pcName[500]; //oder *pcName
	pcTmp = strtok(f,".");
	if(pcTmp != NULL){
		sprintf(pcName, "%s.sol",pcTmp);
	}
	printf("%s %s %s\n", f, pcTmp, pcName);
	file.open(pcName,ios::out);
    file<<"Solution with "<<optimalsolution[0]<<" stations\n";
    file<<"\n<task assignments>\n";
 	  for(int j = 1; j <= n_tasks; j++) 
	  {
		file<<j<<"\t"<<optimalsolution[j]<<"\n";
	  }
    file<<"<task sequence>\n";
	for (int k=1;k<=optimalsolution[0];k++) {
      file<<"station "<<k<<"\n";
 	  for(int j = 1; j <= n_tasks; j++) 
	  {
		if (optimalsolution[j]==k) {
		  file<<j<<"\n";
		}
	  }
	}
    file.close();
}

//added by AS 2013/06/06
void write_results(char *f, double cpu)
{
    ofstream file;
	file.open(f,ios::app);
    file<<prob_file<<"\t"<<optimalsolution[0]<<"\t"<<cpu<<"\n";
    file.close();
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


void prn_tasks(int *tasks, int n)
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

void prn_int(int *vector, int n)
{
   int      i;

   for (i = 1; i <= n; i++) {
	  printf("%2d ", vector[i]); 
   }
   printf("\n");
}

}; // end namespace salb




