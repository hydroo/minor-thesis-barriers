#define _GNU_SOURCE
#include <assert.h>
#include <omp.h>
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
    volatile uint64_t entry;
    volatile int left;
    volatile uint64_t exit;
    int sleepMicroSeconds;
    pthread_barrier_t pthreadBarrier;
} Context;

typedef struct {
    int index;
    Context *c;
} ThreadInfo;

Context * newContext(int threadCount, int64_t repetitionCount, int sleepMicroSeconds) {

    assert(threadCount <= 64);
    assert(threadCount <= sysconf( _SC_NPROCESSORS_ONLN ));

    Context *ret = (Context*) malloc(sizeof(Context));
    assert(ret != NULL);

    ret->threadCount = threadCount;
    ret->repetitionCount = repetitionCount;

    ret->entry = 0x0000000000000000;
    ret->left = 0;
    ret->exit = 0x0000000000000000;

    ret->sleepMicroSeconds = sleepMicroSeconds;

    pthread_barrier_init(&(ret->pthreadBarrier), NULL, threadCount);

    return ret;
}

void finishContext(Context *c) {
    free(c);
}

void barrier(int me, uint64_t full, Context *c) {
    uint64_t copy;

    if (c->left == 0) {

        do {
            copy = c->entry;
            if ((copy & me) == 0) {
                copy |= me;
                c->entry = copy;
            }
        }while (copy != full && c->left == 0);

        c->left = 1;
        c->exit = 0x0000000000000000;

    } else {

        do {
            copy = c->exit;
            if ((copy & me) == 0) {
                copy |= me;
                c->exit = copy;
            }
        }while (copy != full && c->left == 1);

        c->left = 0;
        c->entry = 0x0000000000000000;
    }
}

void* Thread(void *userData) {

    ThreadInfo *info = (ThreadInfo*) userData;
    Context *c = info->c;

    int index = info->index;
    int threadCount = c->threadCount;
    int64_t repetitionCount = c->repetitionCount;
    int sleepMicroSeconds = c->sleepMicroSeconds;

    uint64_t me = 0x1 << index;
    uint64_t full = 0x0000000000000000;

    (void) me;

    for (int i = 0; i < threadCount; ++i) {
        full |= 0x1 << i;
    }

    // set thread affinity
    cpu_set_t cpuset;
    CPU_ZERO(&cpuset);
    CPU_SET(index, &cpuset);
    assert(pthread_setaffinity_np(pthread_self(), sizeof(cpu_set_t), &cpuset) == 0);

    for(int64_t repetition = 0; repetition < repetitionCount; repetition++){
#if defined(USE_PTHREADS)
        pthread_barrier_wait(&(c->pthreadBarrier));
#elif defined(USE_RONNY)
        barrier(me, full, c);
#elif defined(USE_OPENMP)
        #pragma omp barrier
#endif
        if (sleepMicroSeconds > 0) {
            usleep(sleepMicroSeconds);
        }
    }

    return NULL;
}


int main(int argc, char **args) {

    if (argc < 4) {
        printf("  barrier <threadcount> <repetitions> <sleepmicroseconds>\n");
        exit(0);
    }

    int threadCount = atoi(args[1]);
    int repetitionCount = atoll(args[2]);
    int sleepMicroSeconds = atoll(args[3]);

    assert(threadCount > 0);
    assert(repetitionCount > 0);
    assert(sleepMicroSeconds >= 0);

    Context *context = newContext(threadCount, repetitionCount, sleepMicroSeconds);
    ThreadInfo infos[threadCount];

#ifdef USE_OPENMP
    #pragma omp parallel num_threads(threadCount)
    {
        int i = omp_get_thread_num();
        infos[i].index = i;
        infos[i].c = context;
        Thread((void *)&(infos[i]));
    }
#else
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
    for (int i = 0; i < threadCount; ++i){
        if(pthread_join(t[i], NULL)){
            perror("pthread_join");
            exit(-1);
        }
    }
#endif

    finishContext(context);

    return 0;
}
