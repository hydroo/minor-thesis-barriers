#define _GNU_SOURCE
#include <assert.h>
#include <pthread.h>
#include <sched.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

void* Thread(void*);


typedef struct {
    int threadCount;
    int entryExitLength;
    int64_t repetitionCount;
    volatile int64_t *successfulBarrierVisitsCount;
    volatile uint8_t *entry;
    volatile int left;
    volatile uint8_t *exit;
    int outOfSyncCount;  /* imprecise */
} Context;

typedef struct {
    int index;
    Context *c;
} ThreadInfo;


Context * newContext(int threadCount, int64_t repetitionCount) {

    //long cpuCount = sysconf( _SC_NPROCESSORS_ONLN );

    //if (threadCount > cpuCount) {
    //    printf("this implementation supports only as many threads as there are cpus (%li). %i\n", cpuCount, threadCount);
    //    assert(0);
    //}


    Context *ret = (Context*) malloc(sizeof(Context));
    assert(ret != NULL);

    ret->threadCount = threadCount;
    ret->entryExitLength = ((threadCount-1)/8)+1;
    ret->repetitionCount = repetitionCount;

    ret->successfulBarrierVisitsCount = (int64_t*) malloc(sizeof(int64_t) * threadCount);
    for (int i = 0; i < threadCount; ++i) {
        ret->successfulBarrierVisitsCount[i] = 0;
    }

    ret->entry = (uint8_t*) malloc(sizeof(uint8_t) * ret->entryExitLength);
    memset((uint8_t*) ret->entry, 0, ret->entryExitLength);
    ret->left = 0;
    ret->exit = (uint8_t*) malloc(sizeof(uint8_t) * ret->entryExitLength);
    memset((uint8_t*) ret->exit, 0, ret->entryExitLength);

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
    free((uint8_t*) c->entry);
    free((uint8_t*) c->exit);
    free(c);
}


void* Thread(void *userData) {

    ThreadInfo *info = (ThreadInfo*) userData;
    Context *c = info->c;

    int index = info->index;
    int arrayIndex = index/8;
    int threadCount = c->threadCount;
    int entryExitLength = c->entryExitLength;
    int64_t repetitionCount = c->repetitionCount;

    uint8_t me = 0x1 << (index % 8);

    uint8_t *full = (uint8_t*) malloc(sizeof(uint8_t) * entryExitLength);
    memset(full, 0, sizeof(uint8_t) * entryExitLength);
    for (int i = 0; i < threadCount; i+=1) {
        full[i/8] |= (0x1 << (i%8));
        //if (index == 0) printf("%d, %d\n", i/8, (0x1 << (i%8)));
    }

    uint8_t *copy = (uint8_t*) malloc(sizeof(uint8_t) * entryExitLength);
    int copyEqualsFull = 0;

    // set thread affinity
    //cpu_set_t cpuset;
    //CPU_ZERO(&cpuset);
    //CPU_SET(index, &cpuset);
    //assert(pthread_setaffinity_np(pthread_self(), sizeof(cpu_set_t), &cpuset) == 0);

    for(int64_t repetition = 0; repetition < repetitionCount; repetition++){

        do {

            //memcpy(copy, (uint8_t*) c->entry, sizeof(uint8_t) * entryExitLength);
            for (int i = 0; i < entryExitLength; i += 1) {
                copy[i] = c->entry[i];
            }

            if ((copy[arrayIndex] & me) == 0) {
                copy[arrayIndex] |= me;
                c->entry[arrayIndex] = copy[arrayIndex];
            }
        //}while (memcmp(copy, full, sizeof(uint8_t) * entryExitLength) != 0 && c->left == 0);

            copyEqualsFull = 1;
            for (int i = 0; i < entryExitLength; i += 1) {
                if (copy[i] != full[i]) {
                    copyEqualsFull = 0;
                    break;
                }
            }

            if (copyEqualsFull == 0) {
                continue;
            }

        }while (copyEqualsFull == 0 && c->left == 0);

        c->left = 1;

        //memset((uint8_t*) c->exit, 0, entryExitLength);
        for (int i = 0; i < entryExitLength; i += 1) {
            c->exit[i] = 0;
        }

        for (int i = 0; i < threadCount - 1; ++i) {
            if (c->successfulBarrierVisitsCount[i] != c->successfulBarrierVisitsCount[i+1]) {
                printf("thread %i and %i are not equal at %lli %lli\n", i, i+1,
                        (long long)c->successfulBarrierVisitsCount[i],
                        (long long)c->successfulBarrierVisitsCount[i+1]);
                ++c->outOfSyncCount;
                assert(0);
            }
        }

        do {

            //memcpy(copy, (uint8_t*) c->exit, sizeof(uint8_t) * entryExitLength);
            for (int i = 0; i < entryExitLength; i += 1) {
                copy[i] = c->exit[i];
            }

            if ((copy[arrayIndex] & me) == 0) {
                copy[arrayIndex] |= me;
                c->exit[arrayIndex] = copy[arrayIndex];
            }

        //}while (memcmp(copy, full, sizeof(uint8_t) * entryExitLength) != 0 && c->left == 1);
            copyEqualsFull = 1;
            for (int i = 0; i < entryExitLength; i += 1) {
                if (copy[i] != full[i]) {
                    copyEqualsFull = 0;
                    break;
                }
            }

        }while (copyEqualsFull == 0 && c->left == 1);

        c->left = 0;

        //memset((uint8_t*) c->entry, 0, entryExitLength);
        for (int i = 0; i < entryExitLength; i += 1) {
            c->entry[i] = 0;
        }


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
    printf("\n");

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
