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
    volatile uint64_t entryBarrier; 
    volatile int someoneLeftTheEntryBarrier;
    volatile uint64_t exitBarrier; 
    int outOfSyncCount;  /* not a precise counter */
} Context;

typedef struct {
    int index;
    Context *c;
} ThreadInfo;


Context * newContext(int threadCount, int64_t repetitions) {

    if (threadCount > 64) {
        printf("this implementation cannot handle more than 64 threads. %i\n", threadCount);
        assert(0);
    }


    Context *ret = (Context*) malloc(sizeof(Context));
    assert(ret != NULL);

    ret->threadCount = threadCount;
    ret->repetitions = repetitions;

    ret->successfulBarrierVisitsCount = (int64_t*) malloc(sizeof(int64_t) * threadCount);
    for (int i = 0; i < threadCount; ++i) {
        ret->successfulBarrierVisitsCount[i] = 0;
    }

    ret->entryBarrier = 0x0000000000000000;
    ret->someoneLeftTheEntryBarrier = 0;
    ret->exitBarrier = 0x0000000000000000;

    ret->outOfSyncCount = 0;

    return ret;
}


void printContext(Context *c) {

    printf("thread count: %i\n", c->threadCount);
    printf("repetitions: %lli\n", (long long) c->repetitions);
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
    int64_t repetitions = c->repetitions;

    uint64_t me = 0x1 << index;
    uint64_t full = 0x0000000000000000;

    for (int i = 0; i < threadCount; ++i) {
        full |= 0x1 << i;
    }

    //printf("%016llX %016llX\n", (long long unsigned) me, (long long unsigned) full);

    //unlink("a");
    //FILE *log = fopen("a", "a");


    for(int64_t repetition = 0; repetition < repetitions; repetition++){

        uint64_t copy;
        c->entryBarrier = 0x0000000000000000;

        /* run to wall and wait busily */
        do {
            copy = c->entryBarrier;
            //fprintf(log, "%i r %lli\n", prime, (long long) copy);
            //fflush(log);
            if ((copy & me) == 0) {
                copy |= me;
                c->entryBarrier = copy;
                //fprintf(log, "%i w %lli\n", prime, (long long) copy);
                //fflush(log);
            }
        }while (copy != full && c->someoneLeftTheEntryBarrier == 0);

        c->someoneLeftTheEntryBarrier = 1;

        c->exitBarrier = 0x0000000000000000;

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
            copy = c->exitBarrier;
            if ((copy & me) == 0) {
                copy |= me;
                c->exitBarrier = copy;
            }
        }while (copy != full && c->someoneLeftTheEntryBarrier == 1);

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
