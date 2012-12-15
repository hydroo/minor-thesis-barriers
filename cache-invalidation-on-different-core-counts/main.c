#define _GNU_SOURCE
#include <assert.h>
#include <pthread.h>
#include <sched.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>

typedef enum {
    Start = 0,
    Initialized = 1,
    CachePrepared = 2,
    Done = 3
}ThreadState;

long int g_invalidatedThreadCount;
long int g_threadCount;
volatile ThreadState *g_threadState;
long int g_repetitionCount;
uint64_t g_cycles = 0;

uint8_t g_data[128] = {
         0,    1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14,  15,

        16,    9, 9, 9, 9, 9, 9, 9, 9, 9,  9,  9,  9,  9,  9,   9,
        32,    9, 9, 9, 9, 9, 9, 9, 9, 9,  9,  9,  9,  9,  9,   9,
        48,    9, 9, 9, 9, 9, 9, 9, 9, 9,  9,  9,  9,  9,  9,   9,
        64,    9, 9, 9, 9, 9, 9, 9, 9, 9,  9,  9,  9,  9,  9,   9,
        70,    9, 9, 9, 9, 9, 9, 9, 9, 9,  9,  9,  9,  9,  9,   9,
        86,    9, 9, 9, 9, 9, 9, 9, 9, 9,  9,  9,  9,  9,  9,   9,
        92,    9, 9, 9, 9, 9, 9, 9, 9, 9,  9,  9,  9,  9,  9, 127 };
uint8_t *g_date;

void* Thread(void*);

uint64_t mytime() {
    static struct timespec t;
    clock_gettime(CLOCK_REALTIME, &t);
    return 1000 * 1000 * t.tv_sec + t.tv_nsec;
}

void* Thread(void *userData) {

    long int index = (long int)userData;
    int threadCount;
    int invalidatedThreadCount;
    volatile ThreadState *threadState;
    int repetitionCount;
    uint8_t *date;
    void *dummy;

    uint64_t before;
    int beforeLower;
    int beforeUpper;
    uint64_t after;
    int afterLower;
    int afterUpper;

    long int repetition;
    /* int i; */

    cpu_set_t cpuset;

    /* *** initialize the thread *** */
    if (index > 0) {
        while(g_threadState[index-1] != Initialized) {}
    }

    threadCount = g_threadCount;
    invalidatedThreadCount = g_invalidatedThreadCount;
    threadState = (ThreadState*) g_threadState;
    repetitionCount = g_repetitionCount;
    date = g_date;


    /* set thread affinity */
    CPU_ZERO(&cpuset);
    CPU_SET(index, &cpuset);
    assert(pthread_setaffinity_np(pthread_self(), sizeof(cpu_set_t), &cpuset) == 0);

    threadState[index] = Initialized;

    for (repetition = 0; repetition < repetitionCount; repetition += 1) {

        /* *** prepare the cache *** */
        if (index > 0) {
            while(threadState[index-1] != CachePrepared) {}

            if (index <= invalidatedThreadCount /* 1 to last */) {
                dummy = (void*) date;
                __sync_synchronize();

                (void) dummy;
            }

            threadState[index] = CachePrepared;

        } else { /* index == 0 */
            while(threadState[threadCount-1] != Initialized) {}

            *date = 0; /* write */
            dummy = (void*)(long int) __sync_fetch_and_add(date, 1); /* write/read + full memory barrier */

            threadState[index] = CachePrepared;
        }

        /* *** trigger the cache invalidation *** */

        if (index > 0) {
            while(threadState[index-1] != Done) {}
            /* do something with date, just to make sure the invalidation of the cacheline is useful
               in everyone's (the cpu's?!) perception */
            dummy = (void*)(long int)*date;
            threadState[index] = Done;

        } else { /* index == 0 */
            while(threadState[threadCount-1] != CachePrepared) {}

            asm volatile("rdtsc" : "=a" (beforeLower), "=d" (beforeUpper));

            dummy = (void*)(long int) __sync_fetch_and_add(date, 1); /* write/read + full memory barrier */

            asm volatile("rdtsc" : "=a" (afterLower), "=d" (afterUpper));

            before = (((uint64_t)beforeLower) | (((uint64_t)beforeUpper) << 32));
            after = (((uint64_t)afterLower) | (((uint64_t)afterUpper) << 32));

            g_cycles += after - before;

            threadState[index] = Done;
        }

        /* *** reset *** */
        if (index > 0) {
            while(threadState[index-1] != Initialized) {}
            threadState[index] = Initialized;
        } else { /* index == 0 */
            while(threadState[threadCount-1] != Done) {}
            threadState[index] = Initialized;
        }

        (void) dummy;

    }

    return NULL;
}

int main(int argc, char **args) {

    int i;
    pthread_t *t;

    if (argc < 4) {
        printf("  cache-test <threadcount> <invalidatethreadcount> <repetitions>\n");
        exit(0);
    }

    g_date = (uint8_t*)((uint64_t)(&(g_data[64])) - (((uint64_t)(&(g_data[64]))%64)));

    assert(g_date >= g_data); /* make sure g_date is calculated correctly */
    assert(&(g_date[63]) <= &(g_data[127]));
    assert(((long int) g_date % 64) == 0);

    g_threadCount = atoi(args[1]);
    g_invalidatedThreadCount = atoi(args[2]);
    g_repetitionCount = atoll(args[3]);

    assert(g_threadCount > 0);
    assert(g_invalidatedThreadCount > 0);
    assert(g_invalidatedThreadCount < g_threadCount);
    assert(g_repetitionCount > 0);

    g_threadState = (ThreadState*)malloc(g_threadCount * sizeof(ThreadState));
    for (i = 0; i < g_threadCount; i += 1) { g_threadState[i] = Start; }


    t = (pthread_t*) malloc(g_threadCount * sizeof(pthread_t));

    /* start all threads */
    for (i = 0; i < g_threadCount; ++i) {
        if(pthread_create( &t[i], NULL, Thread, (void *)(long int)i)){ perror("pthread_create"); exit(-1); }
    }

    /* join all threads */
    for (i = 0; i < g_threadCount; ++i){
        if(pthread_join(t[i], NULL)){ perror("pthread_join"); exit(-1); }
    }

    printf("threads: %li ,invalid: %li ,repetitions: %li ,cycles: %li\n", g_threadCount, g_invalidatedThreadCount, g_repetitionCount, g_cycles);

    free(t);
    free((ThreadState*) g_threadState);

    return 0;
}

