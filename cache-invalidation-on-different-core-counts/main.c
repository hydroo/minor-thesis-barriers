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

int g_invalidatedThreadCount;
int g_threadCount;
volatile ThreadState *g_threadState;
int g_repetitionCount;
uint64_t *g_cycles;

uint8_t g_data[128] = {
         0,    1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14,  15,

        16,    9, 9, 9, 9, 9, 9, 9, 9, 9,  9,  9,  9,  9,  9,   9,
        32,    9, 9, 9, 9, 9, 9, 9, 9, 9,  9,  9,  9,  9,  9,   9,
        48,    9, 9, 9, 9, 9, 9, 9, 9, 9,  9,  9,  9,  9,  9,   9,
        64,    9, 9, 9, 9, 9, 9, 9, 9, 9,  9,  9,  9,  9,  9,   9,
        80,    9, 9, 9, 9, 9, 9, 9, 9, 9,  9,  9,  9,  9,  9,   9,
        96,    9, 9, 9, 9, 9, 9, 9, 9, 9,  9,  9,  9,  9,  9,   9,
        112,   9, 9, 9, 9, 9, 9, 9, 9, 9,  9,  9,  9,  9,  9, 127 };
volatile uint8_t *g_date;

void* Thread(void*);

uint64_t mytime() {
    static struct timespec t;
    clock_gettime(CLOCK_REALTIME, &t);
    return 1000 * 1000 * t.tv_sec + t.tv_nsec;
}

void* Thread(void *userData) {

    int threadIndex = (int)(long int)userData;
    uint8_t dummy;

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
    if (threadIndex > 0) {
        while(g_threadState[threadIndex-1] != Initialized) {}
    }


    /* set thread affinity */
    CPU_ZERO(&cpuset);
    CPU_SET(threadIndex, &cpuset);
    assert(pthread_setaffinity_np(pthread_self(), sizeof(cpu_set_t), &cpuset) == 0);

    g_threadState[threadIndex] = Initialized;


    for (repetition = 0; repetition < g_repetitionCount; repetition += 1) {

        /* *** prepare the cache *** */
        if (threadIndex > 0) {
            while(g_threadState[threadIndex-1] != CachePrepared) {}

            if (threadIndex <= g_invalidatedThreadCount /* 1 to last */) {
                dummy = *g_date;
                __sync_synchronize();

                (void) dummy;
            }

            g_threadState[threadIndex] = CachePrepared;

        } else { /* threadIndex == 0 */
            while(g_threadState[g_threadCount-1] != Initialized) {}

            *g_date = 0; /* write */
            dummy = __sync_fetch_and_add(g_date, 1); /* write/read + full memory barrier */

            g_threadState[threadIndex] = CachePrepared;
        }


        /* *** trigger the cache invalidation *** */
        if (threadIndex > 0) {
            while(g_threadState[threadIndex-1] != Done) {}
            /* do something with g_date, just to make sure the invalidation of the cacheline is useful
               in everyone's (the cpu's?!) perception */
            /*dummy = *g_date;*/
            g_threadState[threadIndex] = Done;

        } else { /* threadIndex == 0 */
            while(g_threadState[g_threadCount-1] != CachePrepared) {}

            asm volatile("rdtsc" : "=a" (beforeLower), "=d" (beforeUpper));

            *g_date = 0;
            dummy = __sync_fetch_and_add(g_date, 1); /* write/read + full memory barrier */

            asm volatile("rdtsc" : "=a" (afterLower), "=d" (afterUpper));

            before = (((uint64_t)beforeLower) | (((uint64_t)beforeUpper) << 32));
            after = (((uint64_t)afterLower) | (((uint64_t)afterUpper) << 32));

            g_cycles[repetition] = after - before;

            g_threadState[threadIndex] = Done;
        }

        /* *** reset *** */
        if (threadIndex > 0) {
            while(g_threadState[threadIndex-1] != Initialized) {}
            g_threadState[threadIndex] = Initialized;
        } else { /* threadIndex == 0 */
            while(g_threadState[g_threadCount-1] != Done) {}
            g_threadState[threadIndex] = Initialized;
        }

        (void) dummy;

    }

    return NULL;
}

int main(int argc, char **args) {

    int i;
    pthread_t *t;

    uint64_t minCycles = -1;
    uint64_t avgCycles;
    uint64_t maxCycles = 0;
    uint64_t sumOfCycles = 0;
    int shortRunaways = 0;
    int longRunaways = 0;

    uint64_t shortRunawaysCycles = 0; /*35 on my notebook, 45 on erwin is perfect*/
    uint64_t longRunawaysCycles = 1000;

    if (argc < 4) {
        printf("  cache-test <threadcount> <invalidatethreadcount> <repetitions> <too short cyclecount> <too long cyclecount>\n");
        exit(0);
    }

    if (argc > 4) {
        shortRunawaysCycles = atoi(args[4]);
        assert(atoi(args[4]) >= 0);
    }
    if (argc > 5) {
        longRunawaysCycles = atoi(args[5]);
        assert(atoi(args[5]) > 0);
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

    g_cycles = (uint64_t*) malloc(sizeof(uint64_t)*g_repetitionCount);


    t = (pthread_t*) malloc(g_threadCount * sizeof(pthread_t));

    /* start all threads */
    for (i = 0; i < g_threadCount; ++i) {
        if(pthread_create( &t[i], NULL, Thread, (void *)(long int)i)){ perror("pthread_create"); exit(-1); }
    }

    /* join all threads */
    for (i = 0; i < g_threadCount; ++i){
        if(pthread_join(t[i], NULL)){ perror("pthread_join"); exit(-1); }
    }


    /* *** analyze results *** */

    for (i=0; i<g_repetitionCount; i += 1) {

        if (g_cycles[i] >= longRunawaysCycles) {
            longRunaways += 1;
            continue;
        } else if (g_cycles[i] <= shortRunawaysCycles) {
            shortRunaways += 1;
            continue;
        }

        /*printf("%li\n", g_cycles[i]);*/
        sumOfCycles += g_cycles[i];
        if (g_cycles[i] < minCycles) {
            minCycles = g_cycles[i];
        }
        if (g_cycles[i] > maxCycles) {
            maxCycles = g_cycles[i];
        }
    }

    avgCycles = sumOfCycles / g_repetitionCount;


    printf("threads: %i ,invalid: %i ,repetitions: %i, minCycles: %li, avgCycles: %li, maxCycles: %li, shortRunaways: %i, longRunaways: %i\n", g_threadCount, g_invalidatedThreadCount, g_repetitionCount, minCycles, avgCycles, maxCycles, shortRunaways, longRunaways);

    free(t);
    free((ThreadState*)g_threadState);

    return 0;
}

