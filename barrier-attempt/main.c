#define _GNU_SOURCE
#include <assert.h>
#include <pthread.h>
#include <sched.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

void* Thread(void*);


typedef struct {
    int threadCount;
    int64_t repetitionCount;
    volatile int64_t *successfulBarrierVisitsCount;
    volatile uint64_t entry; //upper barrier
    volatile int left; // true if somebody left the entry barrier, 
                       // false if someone left the exit barrier
    volatile uint64_t exit; // lower barrier
    int outOfSyncCount;  /* not a precise counter */
} Context;

typedef struct {
    int index;
    Context *c;
} ThreadInfo;


Context * newContext(int threadCount, int64_t repetitionCount) {

    if (threadCount > 64) {
        printf("this implementation cannot handle more than 64 threads. %i\n", threadCount);
        assert(0);
    }


    Context *ret = (Context*) malloc(sizeof(Context));
    assert(ret != NULL);

    ret->threadCount = threadCount;
    ret->repetitionCount = repetitionCount;

    ret->successfulBarrierVisitsCount = (int64_t*) malloc(sizeof(int64_t) * threadCount);
    for (int i = 0; i < threadCount; ++i) {
        ret->successfulBarrierVisitsCount[i] = 0;
    }

    ret->entry = 0x0000000000000000;
    ret->left = 0;
    ret->exit = 0x0000000000000000;

    ret->outOfSyncCount = 0;

    return ret;
}


void printContext(Context *c) {

    printf("thread count: %i\n", c->threadCount);
    printf("repetitions: %lli\n", (long long) c->repetitionCount);
    printf("out of sync count: %i\n", c->outOfSyncCount);
    printf("threads:\n");
    for (int i = 0 ; i < c->threadCount; ++i) {
        printf("  %i: successful barrier visits: %lli\n", i,
                (long long) c->successfulBarrierVisitsCount[i]);
    }
}


void finishContext(Context *c) {
    free((int64_t*) c->successfulBarrierVisitsCount);
    free(c);
}


void* Thread(void *userData) {

    ThreadInfo *info = (ThreadInfo*) userData;
    Context *c = info->c;

    int index = info->index;
    int threadCount = c->threadCount;
    int64_t repetitionCount = c->repetitionCount;

    uint64_t me = 0x1 << index;
    uint64_t full = 0x0000000000000000;

    uint64_t copy; //thread local copy of the entry/exit barrier

    for (int i = 0; i < threadCount; ++i) {
        full |= 0x1 << i;
    }

    // set thread affinity
    cpu_set_t cpuset;
    CPU_ZERO(&cpuset);
    CPU_SET(index, &cpuset);
    assert(pthread_setaffinity_np(pthread_self(), sizeof(cpu_set_t), &cpuset) == 0);

    //DEBUG
    //pthread_getaffinity_np(pthread_self(), sizeof(cpu_set_t), &cpuset);
    //printf("%i uses cpus: ", index);
    //for (int i = 0; i < threadCount; ++i) {
    //    if (CPU_ISSET(i, &cpuset)) {
    //        printf("%i, ", i);
    //    }
    //}
    //printf("\n");

    //printf("%016llX %016llX\n", (long long unsigned) me, (long long unsigned) full);

    //unlink("a");
    //FILE *log = fopen("a", "a");


    for(int64_t repetition = 0; repetition < repetitionCount; repetition++){

        c->entry = 0x0000000000000000;

        /* run to wall and wait busily */
        do {
            copy = c->entry;
            //fprintf(log, "%i r %lli\n", prime, (long long) copy);
            //fflush(log);
            if ((copy & me) == 0) {
                copy |= me;
                c->entry = copy;
                //fprintf(log, "%i w %lli\n", prime, (long long) copy);
                //fflush(log);
            }
        }while (copy != full && c->left == 0);

        c->left = 1;

        c->exit = 0x0000000000000000;

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
            copy = c->exit;
            if ((copy & me) == 0) {
                copy |= me;
                c->exit = copy;
            }
        }while (copy != full && c->left == 1);

        c->left = 0;

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
    int repetitionCount = atoll(args[2]);

    assert(threadCount > 0);
    assert(repetitionCount > 0);

    Context *context = newContext(threadCount, repetitionCount);
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
