#include <assert.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

void* Thread(void*);


typedef struct {
    int threadCount;
    int64_t repetitions;
    volatile int64_t *successfulBarrierVisitsCount;
    volatile int64_t entryBarrier; 
    volatile int someoneLeftTheEntryBarrier;
    volatile int64_t exitBarrier; 
    int *primes;
    int outOfSyncCount;  /* not a precise counter */

    int64_t productOfAllPrimes;
} Context;

typedef struct {
    int index;
    Context *c;
} ThreadInfo;


Context * newContext(int threadCount, int64_t repetitions) {

    Context *ret = (Context*) malloc(sizeof(Context));
    assert(ret != NULL);

    ret->threadCount = threadCount;
    ret->repetitions = repetitions;

    ret->successfulBarrierVisitsCount = (int64_t*) malloc(sizeof(int64_t) * threadCount);
    for (int i = 0; i < threadCount; ++i) {
        ret->successfulBarrierVisitsCount[i] = 0;
    }

    ret->entryBarrier = 1;
    ret->someoneLeftTheEntryBarrier = 0;
    ret->exitBarrier = 1;

    ret->primes = (int*) malloc(sizeof(int)*threadCount);
    int primeCandidate = 2;
    for (int i = 0; i < threadCount; ++primeCandidate) {
        int n = 2;
        for (; n < primeCandidate; ++n) {
            if (primeCandidate % n == 0) {
                break;
            }
        }
        if (n == primeCandidate) {
            ret->primes[i] = primeCandidate;
            ++i;
        }
    }

    ret->outOfSyncCount = 0;

    ret->productOfAllPrimes = 1;
    for (int i = 0; i < ret->threadCount; ++i) {
        ret->productOfAllPrimes *= ret->primes[i];
    }

    if (ret->productOfAllPrimes <= 0) {
        printf("the product of primes exceed a 64bit integer. %lli\n", (long long) ret->productOfAllPrimes);
        assert(0);
    }

    return ret;
}


void printContext(Context *c) {

    printf("thread count: %i\n", c->threadCount);
    printf("repetitions: %lli\n", (long long) c->repetitions);
    printf("out of sync count: %i\n", c->outOfSyncCount);
    printf("threads:\n");
    for (int i = 0 ; i < c->threadCount; ++i) {
        printf("  %i: prime: %i, successful barrier visits: %lli\n", i,
                c->primes[i],(long long) c->successfulBarrierVisitsCount[i]);
    }

    printf("product of all primes: %lli\n", (long long) c->productOfAllPrimes);
}


void finishContext(Context *c) {
    free((int64_t*) c->successfulBarrierVisitsCount);
    free(c->primes);
    free(c);
}


void* Thread(void *userData) {

    ThreadInfo *info = (ThreadInfo*) userData;
    Context *c = info->c;

    int index = info->index;
    int threadCount = c->threadCount;
    int64_t productOfAllPrimes = c->productOfAllPrimes;
    int prime = c->primes[index];
    int repetitions = c->repetitions;

    //unlink("a");
    //FILE *log = fopen("a", "a");


    for(int64_t repetition = 0; repetition < repetitions; repetition++){

        int64_t entryBarrierCopy;
        c->entryBarrier = 1;

        /* run to wall and wait busily */
        do {
            entryBarrierCopy = c->entryBarrier;
            //fprintf(log, "%i r %lli\n", prime, (long long) entryBarrierCopy);
            //fflush(log);
            if (entryBarrierCopy % prime != 0) {
                entryBarrierCopy *= prime;
                c->entryBarrier = entryBarrierCopy;
                //fprintf(log, "%i w %lli\n", prime, (long long) entryBarrierCopy);
                //fflush(log);
            }
        }while (entryBarrierCopy != productOfAllPrimes && c->someoneLeftTheEntryBarrier == 0);

        c->someoneLeftTheEntryBarrier = 1;

        int64_t exitBarrierCopy;
        c->exitBarrier = 1;

        for (int i = 0; i < threadCount - 1; ++i) {
            if (c->successfulBarrierVisitsCount[i] != c->successfulBarrierVisitsCount[i+1]) {
                printf("thread %i and %i are not equal at %lli %lli\n", i, i+1,
                        (long long)c->successfulBarrierVisitsCount[i],
                        (long long)c->successfulBarrierVisitsCount[i+1]);
                ++c->outOfSyncCount;
                assert(0);
            }
        }

        /* wait busily until everyone has left the barrier */
        do {
            exitBarrierCopy = c->exitBarrier;
            if (exitBarrierCopy % prime != 0) {
                exitBarrierCopy *= prime;
                c->exitBarrier = exitBarrierCopy;
            }
        }while (exitBarrierCopy != productOfAllPrimes && c->someoneLeftTheEntryBarrier == 1);

        c->someoneLeftTheEntryBarrier = 0;

        ++(c->successfulBarrierVisitsCount[index]);
    }

    return NULL;
}


int main(int argc, char **args) {

    if (argc < 3) {
        printf("  barrier <threadcount> <repetitions>\n");
        exit(0);
    }

    int threadCount = atoi(args[1]);
    int repetitions = atoll(args[2]);

    assert(threadCount > 0);
    assert(repetitions > 0);

    Context *context = newContext(threadCount, repetitions);
    pthread_t t[threadCount];
    ThreadInfo infos[threadCount];

    printContext(context);

    /* start all threads */
    for (int i = 0; i < threadCount; ++i) {
        infos[i].index = i;
        infos[i].c = context;
        if(pthread_create( &t[i], NULL, Thread, (void *)&(infos[i]))){
            perror("pthread_create");
            exit(-1);
        }
    }

    /* join all threads */
    for (int i = 0; i < threadCount; ++i){
        if(pthread_join(t[i], NULL)){
            perror("pthread_join");
            exit(-1);
        }
    }

    printContext(context);

    finishContext(context);

    return 0;
}
