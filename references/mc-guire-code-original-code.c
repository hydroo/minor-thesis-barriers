#include <stdio.h>	/* printf */
#include <stdlib.h>	/* exit */
#include <pthread.h>/* pthread* */

unsigned long long int N=100000000;
#define NUM_THREADS 2
volatile unsigned int cnt[2] = {0};
volatile unsigned int barrier = 1; 
unsigned int primes[2]={2,3};
unsigned int oosync=0;	/* not a precise counter */


void *Thread(void *);

void * Thread(void *v)
{
	unsigned long long int n;
	int idx=(int)(long *)v;
	unsigned int me=primes[idx];
	unsigned int other=primes[!idx];
	unsigned int wall=me*other;

	for(n=0;n<N;n++){
		/* run to wall */
		while((barrier%wall)){
			if(barrier%me){
				barrier*=me;
			}
		}

		/* if both tasks always revisit this
		 * point reliably then the counters 
		 * within the barrier must always be equal
		 */
		if(cnt[0] != cnt[1]){
			printf("not equal at %u %u\n",cnt[0],cnt[1]);
			oosync++;
		}
		/* reset barrier */
		do{
			if(!(barrier%other)){
				barrier/=other;
			}
		}while(barrier!=1);
		cnt[idx]++;
	}
	return NULL;
}


int main(int argc, char **argv)
{
	int n,i;
	pthread_t t[NUM_THREADS];

	printf("looping for %llu cycles...might take some time\n",N);
	fflush(stdout);

	if(pthread_create( &t[0], NULL, Thread, (void *)0)){
		perror("pthread_create");
		exit(-1);
	}
	if(pthread_create( &t[1], NULL, Thread, (void *)1)){
		perror("pthread_create");
		exit(-1);
	}

	for (n = 0; n < NUM_THREADS; ++n){
                if(pthread_join(t[n],NULL)){
                        perror("pthread_join");
                        exit(-1);
                }
	}
	printf("task each did %u %u loops, with %d out of sync\n",
		cnt[0],cnt[1],oosync);

	return 0;
}