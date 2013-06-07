#define _GNU_SOURCE
#include <assert.h>
#include <pthread.h>
#include <sched.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#define ARRAY_64

#if defined(ARRAY_64)
    #define ARRAY_BITS 64
    typedef uint64_t arrayElement;
#elif defined(ARRAY_32)
    #define ARRAY_BITS 32
    typedef uint32_t arrayElement;
#elif defined(ARRAY_16)
    #define ARRAY_BITS 16
    typedef uint16_t arrayElement;
#elif defined(ARRAY_8)
    #define ARRAY_BITS 8
    typedef uint8_t arrayElement;
#endif


void* Thread(void*);

typedef struct {
    int threadCount;
    int entryExitLength;
    int maxWallSeconds;
    int64_t repetitionCount;
    arrayElement *entry; //volatile arrayElement *entry;
    int left; //volatile int left;
    arrayElement *exit; //volatile arrayElement *exit;
    int sleepMicroSeconds;
    pthread_barrier_t pthreadBarrier;
    int barrier1;
    int barrier2;
    int barrier3;
    uint64_t *nanoSeconds;
#ifdef DEBUG
    volatile int64_t *successfulBarrierVisitsCount;
    int outOfSyncCount;  /* imprecise */
#endif
} Context;

typedef struct {
    int index;
    Context *c;
} ThreadInfo;


Context* newContext(int threadCount, int maxWallSeconds, int sleepMicroSeconds) {

    long cpuCount = sysconf(_SC_NPROCESSORS_ONLN);
    if (threadCount > cpuCount) {
        printf("threadcount: %i > cpucount: %li. threads will be pinned round robin.\n", threadCount, cpuCount);
    }

    Context *ret = (Context*) malloc(sizeof(Context));
    assert(ret != NULL);

    ret->threadCount = threadCount;
    ret->entryExitLength = ((threadCount-1)/ARRAY_BITS)+1;
    ret->maxWallSeconds = maxWallSeconds;

    ret->entry = (arrayElement*) malloc(sizeof(arrayElement) * ret->entryExitLength);
    memset((arrayElement*) ret->entry, 0, ret->entryExitLength);
    ret->left = 0;
    ret->exit = (arrayElement*) malloc(sizeof(arrayElement) * ret->entryExitLength);
    memset((arrayElement*) ret->exit, 0, ret->entryExitLength);

    ret->sleepMicroSeconds = sleepMicroSeconds;

    pthread_barrier_init(&(ret->pthreadBarrier), NULL, threadCount);

    ret->barrier1 = threadCount;
    ret->barrier2 = threadCount;
    ret->barrier3 = threadCount;

    ret->nanoSeconds = (uint64_t*) malloc(sizeof(uint64_t) * threadCount);

#ifdef DEBUG
    ret->successfulBarrierVisitsCount = (int64_t*) malloc(sizeof(int64_t) * threadCount);
    for (int i = 0; i < threadCount; ++i) {
        ret->successfulBarrierVisitsCount[i] = 0;
    }
#endif

    return ret;
}

void freeContext(Context *c) {
    free((arrayElement*) c->entry);
    free((arrayElement*) c->exit);
    free(c->nanoSeconds);
#ifdef DEBUG
    free((int64_t*) c->successfulBarrierVisitsCount);
#endif
    free(c);
}

void barrierRonny(int index, int arrayIndex, arrayElement me, arrayElement notMe, int entryExitLength, arrayElement *full, Context *c, arrayElement *copy) {

    (void) index;


    if (__atomic_load_n(&(c->left), __ATOMIC_ACQUIRE) == 0) { //if (c->left == 0) {

        do {

            copy[arrayIndex] &= notMe;
            for (int i = 0; i < entryExitLength; i += 1) {
                copy[i] |= __atomic_load_n(&(c->entry[i]), __ATOMIC_ACQUIRE); //copy[i] |= c->entry[i];
            }


            if ((copy[arrayIndex] & me) == 0) {
                copy[arrayIndex] |= me;
                __atomic_store_n(&(c->entry[arrayIndex]), copy[arrayIndex], __ATOMIC_RELEASE); //c->entry[arrayIndex] = copy[arrayIndex];
            }
        //}while (memcmp(copy, full, sizeof(arrayElement) * entryExitLength) != 0 && c->left == 0);
        }while (memcmp(copy, full, sizeof(arrayElement) * entryExitLength) != 0 && __atomic_load_n(&(c->left), __ATOMIC_ACQUIRE) == 0);

        __atomic_store_n(&(c->left), 1, __ATOMIC_RELEASE); //c->left = 1;
        memset((arrayElement*) c->exit, 0, sizeof(arrayElement) * entryExitLength);
        memset((arrayElement*) copy, 0, sizeof(arrayElement) * entryExitLength);

    } else {

#ifdef DEBUG
        for (int i = 0; i < c->threadCount - 1; ++i) {
            if (c->successfulBarrierVisitsCount[i] != c->successfulBarrierVisitsCount[i+1]) {
                printf("thread %i and %i are not equal at %lli %lli\n", i, i+1,
                        (long long)c->successfulBarrierVisitsCount[i],
                        (long long)c->successfulBarrierVisitsCount[i+1]);
                ++c->outOfSyncCount;
                assert(0);
            }
        }
#endif

        do {

            copy[arrayIndex] &= notMe;
            for (int i = 0; i < entryExitLength; i += 1) {
                copy[i] |= __atomic_load_n(&(c->exit[i]), __ATOMIC_ACQUIRE); //copy[i] |= c->exit[i];
            }

            if ((copy[arrayIndex] & me) == 0) {
                copy[arrayIndex] |= me;
                __atomic_store_n(&(c->exit[arrayIndex]), copy[arrayIndex], __ATOMIC_RELEASE); //c->exit[arrayIndex] = copy[arrayIndex];
            }
        //}while (memcmp(copy, full, sizeof(arrayElement) * entryExitLength) != 0 && c->left == 1);
        }while (memcmp(copy, full, sizeof(arrayElement) * entryExitLength) != 0 && __atomic_load_n(&(c->left), __ATOMIC_ACQUIRE) == 1);

        __atomic_store_n(&(c->left), 0, __ATOMIC_RELEASE); //c->left = 0;
        memset((arrayElement*) c->entry, 0, sizeof(arrayElement) * entryExitLength);
        memset((arrayElement*) copy, 0, sizeof(arrayElement) * entryExitLength);

#ifdef DEBUG
        ++(c->successfulBarrierVisitsCount[index]);
#endif

    }
}

void barrierAddFetch1(Context *c, int threadCount) {
    if (__atomic_add_fetch(&(c->barrier1), -1, __ATOMIC_ACQ_REL) != 0) {
        while (__atomic_load_n (&c->barrier1, __ATOMIC_ACQUIRE) != 0) {
        }
    }
    c->barrier3 = threadCount;
}
void barrierAddFetch2(Context *c, int threadCount) {
    if (__atomic_add_fetch(&(c->barrier2), -1, __ATOMIC_ACQ_REL) != 0) {
        while (__atomic_load_n (&c->barrier2, __ATOMIC_ACQUIRE) != 0) {
        }
    }
    c->barrier1 = threadCount;
}
void barrierAddFetch3(Context *c, int threadCount) {
    c->barrier1 = threadCount;
    if (__atomic_add_fetch(&(c->barrier3), -1, __ATOMIC_ACQ_REL) != 0) {
        while (__atomic_load_n (&c->barrier3, __ATOMIC_ACQUIRE) != 0) {
        }
    }
    c->barrier2 = threadCount;
}


void* Thread(void *userData) {

    ThreadInfo *info = (ThreadInfo*) userData;
    Context *c = info->c;

    int index = info->index;
    int arrayIndex = index/ARRAY_BITS;
    int threadCount = c->threadCount;
    int maxWallSeconds = c->maxWallSeconds;
    int sleepMicroSeconds = c->sleepMicroSeconds;

    arrayElement me = ((arrayElement)0x1) << (index % ARRAY_BITS);
    arrayElement notMe = ~me;
    arrayElement *full = (arrayElement*) malloc(sizeof(arrayElement) * c->entryExitLength);
    memset(full, 0, sizeof(arrayElement) * c->entryExitLength);
    for (int i = 0; i < threadCount; i += 1) {
        full[i/ARRAY_BITS] |= (((arrayElement)0x1) << (i % ARRAY_BITS));
    }

    struct timespec begin, end;
    int64_t repetitions;

    (void) arrayIndex;
    (void) me;
    (void) notMe;

    arrayElement *copy = (arrayElement*) malloc(sizeof(arrayElement) * c->entryExitLength);

    // set thread affinity
    cpu_set_t cpuset;
    CPU_ZERO(&cpuset);
    CPU_SET(index % sysconf(_SC_NPROCESSORS_ONLN), &cpuset);
    assert(pthread_setaffinity_np(pthread_self(), sizeof(cpu_set_t), &cpuset) == 0);

    clock_gettime(CLOCK_REALTIME, &begin);

    time_t supposedEnd = begin.tv_sec + maxWallSeconds;

    for(repetitions = 0;; repetitions+=3){
#if defined(USE_ADD_FETCH)
        /* tripple barrier makes the resetting safe */
        barrierAddFetch1(c, threadCount);
        barrierAddFetch2(c, threadCount);
        barrierAddFetch3(c, threadCount);
#elif defined(USE_RONNY)
        barrierRonny(index, arrayIndex, me, notMe, c->entryExitLength, full, c, copy);
        barrierRonny(index, arrayIndex, me, notMe, c->entryExitLength, full, c, copy);
        barrierRonny(index, arrayIndex, me, notMe, c->entryExitLength, full, c, copy);
#endif

        if (repetitions % 300 == 0) {
            clock_gettime(CLOCK_REALTIME, &end);
            if (end.tv_sec > supposedEnd) {
                break;
            }
        }

        if (sleepMicroSeconds > 0) {
            usleep(sleepMicroSeconds);
        }
    }

    c->repetitionCount = repetitions;
    c->nanoSeconds[index] = (end.tv_sec * 1000000000 + end.tv_nsec) - (begin.tv_sec * 1000000000 + begin.tv_nsec);

    free(copy);

    return NULL;
}

void printResults(Context *c, float clockTicksPerNanoSecond) {

    double meanSeconds = 0.0;

#if defined(USE_ADD_FETCH)
    const char *barrierType = "add-fetch";
#elif defined(USE_RONNY)
    const char *barrierType = "ronny    ";
#endif

    for (int i = 0; i < c->threadCount; i += 1) {
        meanSeconds += c->nanoSeconds[i] / 1000000000.0;
    }
    meanSeconds /= c->threadCount;

    printf("%s threads: %2d, reps: %7lli, sleepMySecs: %3d, wallSecs: %.2lf, ticksPerBarrier: %8.0lf ticksPerBarrierDivByThreads: %8.0lf\n", barrierType, c->threadCount, (long long int) c->repetitionCount, c->sleepMicroSeconds, meanSeconds, (meanSeconds * 1000000000 * clockTicksPerNanoSecond) / c->repetitionCount, ((meanSeconds * 1000000000 * clockTicksPerNanoSecond) / c->repetitionCount) / c->threadCount);
}


int main(int argc, char **args) {

    if (argc < 3) {
        printf("  barrier <threadcount> <maxwallseconds> <clockTicksPerNanoSecond (default: 1)> <sleepmicroseconds>\n");
        exit(0);
    }

    int threadCount = atoi(args[1]);
    int maxWallSeconds = atoll(args[2]);
    float clockTicksPerNanoSecond = argc > 3 ? (float )atof(args[3]) : 1.0f;
    int sleepMicroSeconds = argc > 4 ? atoll(args[4]) : 0;

    assert(threadCount > 0);
    assert(maxWallSeconds > 0);
    assert(sleepMicroSeconds >= 0);

    Context *context = newContext(threadCount, maxWallSeconds, sleepMicroSeconds);
    ThreadInfo infos[threadCount];

    pthread_t t[threadCount];

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
    for (int i = 0; i < threadCount; ++i) {
        if(pthread_join(t[i], NULL)){
            perror("pthread_join");
            exit(-1);
        }
    }

    printResults(context, clockTicksPerNanoSecond);

    freeContext(context);

    return 0;
}
