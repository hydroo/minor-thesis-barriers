#define _GNU_SOURCE
#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <math.h>
#include <sched.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#include <pthread.h>


typedef enum {
    False = 0,
    True = 1
} Bool;

typedef struct {
    int threadCount;
    double minWallSecondsPerMeasurement;
    double clockTicksPerNanoSecond;
    Bool avoidHt;
    int msrFile;
    double raplEnergyMultiplier;
    double sleepPowerConsumption; //Watt
    double uncorePowerConsumption; //Watt
}Context;

typedef struct {
    int index;
    const Context * c;
    double elapsedSeconds;
    double usedJoule;
} ThreadInfo;

typedef struct {
    double elapsedSeconds;
    double powerConsumption; // watt
} MeasurementResult;


static int openMsrFile() {
    int fd = open("/dev/cpu/0/msr",O_RDONLY);
    if (fd == -1) {
        printf("failed opening msr file: \"%s\". no rapl measurements will be done.\n", strerror(errno));
    }
    return fd;
}
static inline uint64_t msr(int msrFile, uint32_t offset) {
    uint64_t value;
    if (pread(msrFile, &value, sizeof(uint64_t), offset) != sizeof(uint64_t)) {
        return 0;
    }
    return value;
}
static void closeMsrFile(int fd) {
    close(fd);
}
static inline uint64_t packageEnergy(int msrFile) {
    return msr(msrFile, 0x611);
}
static inline uint64_t pp0Energy(int msrFile) {
    return msr(msrFile, 0x639);
}
static inline uint64_t energy(int msrFile) {
    return packageEnergy(msrFile);
}

static double energyToJoule(uint64_t energy, double raplEnergyMultiplier) {
    return energy * raplEnergyMultiplier;
}

// thread unsafe
static void initBarrier(int *barrier, int threadCount) {
    *barrier = threadCount;
}
static inline void waitBarrier(int *barrier) {
    if (__atomic_add_fetch(barrier, -1, __ATOMIC_ACQ_REL) != 0) {
        while (__atomic_load_n (barrier, __ATOMIC_ACQUIRE) != 0) {
        }
    }
}

static void setThreadAffinity(int threadIndex_, Bool avoidHt) {
    if (avoidHt == True) threadIndex_ *= 2;

    cpu_set_t get;
    assert(pthread_getaffinity_np(pthread_self(), sizeof(cpu_set_t), &get) == 0);

    int cpuCount = CPU_COUNT(&get);
    int threadIndex = threadIndex_ % cpuCount;
    int setIndex = -1;
    for (int i = 0; i < (int)sizeof(cpu_set_t)*8; i += 1) {
        if (CPU_ISSET(i, &get)) {
            if (threadIndex == 0) {
                setIndex = i;
                break;
            } else if (threadIndex > 0) {
                threadIndex -= 1;
            }
        }
    }
    assert(setIndex >= 0);

    cpu_set_t set;
    CPU_ZERO(&set);
    CPU_SET(setIndex, &set);
    assert(pthread_setaffinity_np(pthread_self(), sizeof(cpu_set_t), &set) == 0);
}

static inline double seconds(struct timespec t) {
    return t.tv_sec + (t.tv_nsec / 1000000000.0);
}
static inline uint64_t nanoSeconds(struct timespec t) {
    return ((uint64_t)t.tv_sec * 1000000000 + (uint64_t)t.tv_nsec);
}
//static inline uint64_t cycles(struct timespec t, double clockTicksPerNanoSecond) {
//    return (uint64_t)(nanoSeconds(t) * clockTicksPerNanoSecond);
//}


static void threadListFromArguments(char **args, int argc, int startIndex, int **threadList, int *threadListLen, int minimum, int maximum) {

    *threadListLen = 0;

    for (int i = startIndex; i < argc; i += 1) {
        if (args[i][0] >= '0' && args[i][0] <= '9') *threadListLen += 1;
        else break;
    }

    *threadList = (int*) malloc(sizeof(int) * (*threadListLen));
    for (int i = 0; i < *threadListLen; i += 1) {
        (*threadList)[i] = (int) atol(args[startIndex+i]);
        if ((*threadList)[i] < minimum) {
            fprintf(stderr, "no less than %i threads allowed for benchmarking. (you tried %i)\n", minimum, (*threadList)[i]);
            exit(-1);
        }
        if ((*threadList)[i] > maximum) {
            fprintf(stderr, "no more than %i threads allowed for benchmarking. (you tried %i)\n", maximum, (*threadList) [i]);
            exit(-1);
        }
    }
}


#define REPEAT01(x) x;x;
#define REPEAT02(x) REPEAT01(x)REPEAT01(x)
#define REPEAT04(x) REPEAT02(x)REPEAT02(x)REPEAT02(x)REPEAT02(x)
#define REPEAT06(x) REPEAT04(x)REPEAT04(x)REPEAT04(x)REPEAT04(x)
#define REPEAT08(x) REPEAT06(x)REPEAT06(x)REPEAT06(x)REPEAT06(x)
#define REPEAT10(x) REPEAT08(x)REPEAT08(x)REPEAT08(x)REPEAT08(x)
#define REPEAT12(x) REPEAT10(x)REPEAT10(x)REPEAT10(x)REPEAT10(x)
#define REPEAT14(x) REPEAT12(x)REPEAT12(x)REPEAT12(x)REPEAT12(x)
#define REPEAT(n, x) REPEAT##n(x)


//static double mean(double *s, int l) {
//    double sum = 0.0;
//    for (int i = 0; i < l; i += 1) {
//        sum += s[i];
//    }
//    return sum / l;
//}
//static double maximumDeviation(double *s, double mean, int l) {
//    double deviation = 0.0;
//    for (int i = 0; i < l; i += 1) {
//        if ( abs(s[i] - mean) > deviation) {
//            deviation = abs(s[i] - mean);
//        }
//    }
//    return deviation;
//}
//static double meanDeviation(double *s, double mean, int l) {
//    double sum = 0.0;
//    for (int i = 0; i < l; i += 1) {
//        sum += abs(s[i] - mean);
//    }
//    return sum / l;
//}


// if the rapl register (detectably) overflows the measurement will be repeated
static inline MeasurementResult measurePowerConsumptionOfFunction(void prepare(int threadIndex, int threadCount), void f(int threadIndex, int threadCount), void finalize(int threadIndex, int threadCount), int threadCount, Context *c, Bool autoPrint) {

    int startBarrier;
    int stopBarrier;
    ThreadInfo *infos = NULL;
    pthread_t *threads = NULL;
    double usedJoule;
    MeasurementResult m;

    void* threadFunction(void *userData) {
        uint64_t beginEnergy;
        uint64_t endEnergy;
        struct timespec beginTime;
        struct timespec endTime;

        ThreadInfo *info = (ThreadInfo*) userData;
        const Context * const c = info->c;
        const int msrFile = c->msrFile;
        const int index = info->index;

        setThreadAffinity(index, c->avoidHt);

        prepare(index, threadCount);

        beginEnergy = energy(msrFile);
        clock_gettime(CLOCK_REALTIME, &beginTime);

        waitBarrier(&startBarrier);
        f(index, threadCount);
        waitBarrier(&stopBarrier);

        endEnergy = energy(msrFile);
        clock_gettime(CLOCK_REALTIME, &endTime);

        finalize(index, threadCount);

        info->elapsedSeconds = seconds(endTime) - seconds(beginTime);
        info->usedJoule = energyToJoule(endEnergy - beginEnergy, c->raplEnergyMultiplier);

        return NULL;
    }

    do {
        initBarrier(&startBarrier, threadCount);
        initBarrier(&stopBarrier, threadCount);

        infos = (ThreadInfo*) malloc(sizeof(ThreadInfo) * threadCount);
        threads = (pthread_t*) malloc(sizeof(pthread_t) * threadCount);

        /* start all threadCount */
        for (int i = 0; i < threadCount; i += 1) {
            infos[i].index = i;
            infos[i].c = c;
            infos[i].elapsedSeconds = 0.0;
            infos[i].usedJoule = 0.0;
            if(pthread_create(&threads[i], NULL, threadFunction, (void *)&(infos[i]))){
                perror("pthread_create");
                exit(-1);
            }
        }

        /* join all threads */
        for (int i = 0; i < threadCount; i += 1) {
            if(pthread_join(threads[i], NULL)){
                perror("pthread_join");
                exit(-1);
            }
        }

        // use results of thread zero only, deviation due to the barriers is ~10^-6 seconds
        // and since rapl has a 10*-3 seconds resolution no difference can be seen.
        //
        // we still keep the data/code on all threads since we have only one struct ThreadInfo,
        // and would need an extra if (index == 0) {}
        usedJoule = infos[0].usedJoule;
        m.elapsedSeconds = infos[0].elapsedSeconds;
        m.powerConsumption = usedJoule / m.elapsedSeconds;

        free(infos);
        free(threads);

    } while(usedJoule < 0.0); // repeat incase of wrap around in the energy counter register


    if (autoPrint == True) {
        printf("# measurement t %3d wallSecs %.3lf, totalPower %3.3lf W\n", threadCount, m.elapsedSeconds, m.powerConsumption);
    }

    if (m.elapsedSeconds < c->minWallSecondsPerMeasurement) {
        printf("#    %lf s < %.0lf s : less benchmarking time than desired\n", m.elapsedSeconds, c->minWallSecondsPerMeasurement);
    }

    return m;
}

static Context* newContext(int threadCount, int minWallSecondsPerMeasurement, double clockTicksPerNanoSecond, Bool avoidHt, double sleepPowerConsumption, double uncorePowerConsumption) {

    cpu_set_t get;
    assert(pthread_getaffinity_np(pthread_self(), sizeof(cpu_set_t), &get) == 0);
    int cpuCount = CPU_COUNT(&get);
    if (threadCount > cpuCount) {
        printf("threadcount: %i > cpucount: %i. threads will be pinned round robin.\n", threadCount, cpuCount);
    }
    if (avoidHt == True && threadCount*2 > cpuCount) {
        printf("threadcount: %i > cpucount: %i (avoid-ht). threads will be pinned round robin.\n", threadCount, cpuCount/2);
    }

    Context *ret = (Context*) malloc(sizeof(Context));
    assert(ret != NULL);

    ret->threadCount = threadCount;
    ret->minWallSecondsPerMeasurement = minWallSecondsPerMeasurement;
    ret->clockTicksPerNanoSecond = clockTicksPerNanoSecond;
    ret->avoidHt = avoidHt;

    ret->msrFile = openMsrFile();

    ret->raplEnergyMultiplier = pow(0.5,(msr(ret->msrFile, 0x606)>>8) & 0x1F);

    ret->sleepPowerConsumption = sleepPowerConsumption;
    ret->uncorePowerConsumption = uncorePowerConsumption;

    return ret;
}
static void freeContext(Context *c) {
    closeMsrFile(c->msrFile);
    free(c);
}


static void printContext(Context *c) {
    printf("# context t %3d, sleepPower %lf W, uncorePower %lf W\n", c->threadCount, c->sleepPowerConsumption, c->uncorePowerConsumption);
}


static void measureSleepPowerConsumption(Context *c, Bool autoPrint) {
    if (autoPrint == True) printf("# %s:\n",__func__);

    void prepare(int threadIndex, int threadCount) {(void) threadIndex; (void) threadCount;}
    void finalize(int threadIndex, int threadCount) {(void) threadIndex; (void) threadCount;}
    void f(int threadIndex, int threadCount) {
        (void) threadIndex;
        (void) threadCount;
        sleep(c->minWallSecondsPerMeasurement);
    }
    MeasurementResult m = measurePowerConsumptionOfFunction(prepare, f, finalize, 1, c, autoPrint);
    c->sleepPowerConsumption = m.powerConsumption;
}


// does not include sleep power consumption
#define repetitionsPerLoop "10 * 1000" // has to fit into the l1 instruction cache
#define loopCount "1000 * 1000"
static void measureUncorePowerConsumption(Context *c, Bool autoPrint) {
    if (autoPrint == True) printf("# %s:\n",__func__);

    assert(c->sleepPowerConsumption > 0.0);

    double powerConsumption;
    double previousPowerConsumption = c->sleepPowerConsumption;

    double firstCorePowerConsumption = 0.0;
    double addedDifferences = 0.0;

    void prepare(int threadIndex, int threadCount) {(void) threadIndex; (void) threadCount;}
    void finalize(int threadIndex, int threadCount) {(void) threadIndex; (void) threadCount;}
    void f(int threadIndex, int threadCount) {
        (void) threadIndex;
        (void) threadCount;

        struct timespec begin, end;

        clock_gettime(CLOCK_REALTIME, &begin);
        const time_t supposedEnd = begin.tv_sec + c->minWallSecondsPerMeasurement;

        for(int64_t repetitions = 0;; repetitions += 1) {

            __asm__ __volatile__ (
                "\t"    "mov $" loopCount ",%%rcx;\n"
                "\t"    "sub $1, %%rcx;\n"
                "\t"    "1:\n"
                "\t"    ".rept (" repetitionsPerLoop ");\n"
                "\t\t"      "xor %%rax,%%rax;\n"
                "\t"    ".endr;\n"
                "\t"    "sub $1,%%rcx;\n"
                "\t"    "jnc 1b\n"
                : : : "rcx", "rax");

            clock_gettime(CLOCK_REALTIME, &end);
            if (end.tv_sec > supposedEnd) {
                break;
            }
        }
    }

    for (int threads = 1; threads <= c->threadCount; threads += 1, previousPowerConsumption = powerConsumption) {

        MeasurementResult m = measurePowerConsumptionOfFunction(prepare, f, finalize, threads, c, autoPrint);
        powerConsumption = m.powerConsumption;

        if (threads == 1) {
            firstCorePowerConsumption = powerConsumption - c->sleepPowerConsumption;
        } else {
            addedDifferences += powerConsumption - previousPowerConsumption;
        }
    }

    c->uncorePowerConsumption = firstCorePowerConsumption - (addedDifferences / (c->threadCount-1));
}
#undef repetitionsPerLoop
#undef loopCount


/* *** add fetch barrier { ************************************************* */
static inline void addFetchBarrier1(int * const barrier1, int * const barrier2, int * const barrier3, int threadCount) {
    (void) barrier2;
    if (__atomic_add_fetch(barrier1, -1, __ATOMIC_ACQ_REL) != 0) {
        while (__atomic_load_n(barrier1, __ATOMIC_ACQUIRE) != 0) {
        }
    }
    *barrier3 = threadCount;
}
static inline void addFetchBarrier2(int * const barrier1, int * const barrier2, int * const barrier3, int threadCount) {
    (void) barrier3;
    if (__atomic_add_fetch(barrier2, -1, __ATOMIC_ACQ_REL) != 0) {
        while (__atomic_load_n(barrier2, __ATOMIC_ACQUIRE) != 0) {
        }
    }
    *barrier1 = threadCount;
}
static inline void addFetchBarrier3(int * const barrier1, int * const barrier2, int * const barrier3, int threadCount) {
    (void) barrier1;
    if (__atomic_add_fetch(barrier3, -1, __ATOMIC_ACQ_REL) != 0) {
        while (__atomic_load_n(barrier3, __ATOMIC_ACQUIRE) != 0) {
        }
    }
    *barrier2 = threadCount;
}

static void measureAddFetchBarrier(Context *c, int *threadCounts, int threadCountsLen) {
    //printf("# %s:\n",__func__);

    volatile int barrier1; // volatile necessary for prepare() to not screw up
    volatile int barrier2;
    volatile int barrier3;
    int64_t repetitions_;

    void prepare(int threadIndex, int threadCount) {
        if (threadIndex == 0) {
            barrier1 = threadCount;
            barrier2 = threadCount;
            barrier3 = threadCount;
        }
    }
    void finalize(int threadIndex, int threadCount) {(void) threadIndex; (void) threadCount;}
    void f(int threadIndex, int threadCount) {
        (void) threadIndex;

        int * const barrier1_ = (int*) &barrier1;
        int * const barrier2_ = (int*) &barrier2;
        int * const barrier3_ = (int*) &barrier3;

        struct timespec begin, end;
        int64_t repetitions = 0;

        clock_gettime(CLOCK_REALTIME, &begin);
        time_t supposedEnd = begin.tv_sec + c->minWallSecondsPerMeasurement;

        for(repetitions = 0;; repetitions += 3){

            addFetchBarrier1(barrier1_, barrier2_, barrier3_, threadCount);
            addFetchBarrier2(barrier1_, barrier2_, barrier3_, threadCount);
            addFetchBarrier3(barrier1_, barrier2_, barrier3_, threadCount);

            if (repetitions % (3 * 1000) == 0) {
                clock_gettime(CLOCK_REALTIME, &end);
                if (end.tv_sec > supposedEnd) {
                    repetitions_ = repetitions;
                    break;
                }
            }
        }
    }

    for (int i = 0; i < threadCountsLen; i += 1) {
        MeasurementResult m = measurePowerConsumptionOfFunction(prepare, f, finalize, threadCounts[i], c, False);

        double totalCycles = m.elapsedSeconds * 1000 * 1000 * 1000 * c->clockTicksPerNanoSecond;
        double cyclesPerRepetition = totalCycles / repetitions_;
        double joule = m.powerConsumption * m.elapsedSeconds;
        double nanoJoulePerRepetition = joule * 1000 * 1000 * 1000 / repetitions_;

        printf("add-fetch-barrier     t %3d, reps %10lli, wallSecs %.3lf sec, totalPower %3.3lf W, cycles/reps %.3lf, nJ/reps %.3lf\n", threadCounts[i], (long long int)repetitions_, m.elapsedSeconds, m.powerConsumption, cyclesPerRepetition, nanoJoulePerRepetition);
    }
}
/* *** } add fetch barrier ************************************************* */

/* *** add fetch wait spinning { ******************************************* */
void barrierAddFetch(int * const bar) {
    if (__atomic_add_fetch(bar, -1, __ATOMIC_ACQ_REL) != 0) {
        while (__atomic_load_n(bar, __ATOMIC_ACQUIRE) != 0) {
        }
    }
}

static void measureAddFetchWaitSpinning(Context *c, int *threadCounts, int threadCountsLen) {
    //printf("# %s:\n",__func__);

    volatile int barrier; // volatile necessary for prepare() to not screw up

    void prepare(int threadIndex, int threadCount) {
        if (threadIndex == 0) {
            barrier = threadCount;
        }
    }
    void finalize(int threadIndex, int threadCount) {(void) threadIndex; (void) threadCount;}
    void f(int threadIndex, int threadCount) {
        (void) threadIndex;
        (void) threadCount;
        int * const barrier_ = (int*) &barrier;

        if (threadIndex == 0) {
            sleep(c->minWallSecondsPerMeasurement);
        }

        barrierAddFetch(barrier_);
    }

    for (int i = 0; i < threadCountsLen; i += 1) {
        MeasurementResult m = measurePowerConsumptionOfFunction(prepare, f, finalize, threadCounts[i], c, False);
        printf("add-fetch-wait-spin   t %3d, wallSecs %.3lf sec, totalPower %3.3lf W\n", threadCounts[i]-1, m.elapsedSeconds, m.powerConsumption);
    }
}
/* *** } add fetch wait spinning ******************************************* */

/* *** add fetch uncontested { ******************************************* */
static void measureAddFetchUncontested(Context *c, int *threadCounts, int threadCountsLen) {
    //printf("# %s:\n",__func__);

    int64_t repetitions_;

    void prepare(int threadIndex, int threadCount) {(void) threadIndex; (void) threadCount;}
    void finalize(int threadIndex, int threadCount) {(void) threadIndex; (void) threadCount;}
    void f(int threadIndex, int threadCount) {
        (void) threadIndex;
        (void) threadCount;
        struct timespec begin, end;
        int barrier = 0;
        int * const barrierPointer = &barrier;

        clock_gettime(CLOCK_REALTIME, &begin);
        const time_t supposedEnd = begin.tv_sec + c->minWallSecondsPerMeasurement;

        for(int64_t repetitions = 0;; repetitions += 1) {

            REPEAT12(__atomic_add_fetch(barrierPointer, -1, __ATOMIC_ACQ_REL);)

            if (repetitions % (1 * 3000) == 0) {
                clock_gettime(CLOCK_REALTIME, &end);
                if (end.tv_sec > supposedEnd) {
                    repetitions_ = repetitions;
                    break;
                }
            }
        }
    }


    for (int i = 0; i < threadCountsLen; i += 1) {
        MeasurementResult m = measurePowerConsumptionOfFunction(prepare, f, finalize, threadCounts[i], c, False);

        repetitions_ *= pow(2,12);

        double totalCycles = m.elapsedSeconds * 1000 * 1000 * 1000 * c->clockTicksPerNanoSecond;
        double cyclesPerRepetition = totalCycles / repetitions_;
        double joule = m.powerConsumption * m.elapsedSeconds;
        double nanoJoulePerRepetition = joule * 1000 * 1000 * 1000 / repetitions_;

        printf("add-fetch-uncontested t %3d, reps %10lli, wallSecs %.3lf sec, totalPower %3.3lf W, cycles/reps %.3lf, nJ/reps %.3lf\n", threadCounts[i], (long long int)repetitions_, m.elapsedSeconds, m.powerConsumption, cyclesPerRepetition, nanoJoulePerRepetition);
    }
}
/* *** } add fetch uncontested ******************************************* */

/* *** ronny array barrier { *********************************************** */
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

#ifdef DEBUG
static inline void barrierRonnyArray(int index, int arrayIndex, arrayElement me, arrayElement notMe, const arrayElement * const full, int *left, arrayElement * const entry, arrayElement * const exit, arrayElement * const copy, int entryExitLength, volatile int64_t *successfulBarrierVisitsCount, int threadCount) {
#else
static inline void barrierRonnyArray(int arrayIndex, arrayElement me, arrayElement notMe, const arrayElement * const full, int * const left, arrayElement * const entry, arrayElement * const exit, arrayElement * const copy, int entryExitLength) {
#endif

    if (__atomic_load_n(left, __ATOMIC_ACQUIRE) == 0) {

        do {
            copy[arrayIndex] &= notMe;
            for (int i = 0; i < entryExitLength; i += 1) {
                copy[i] |= __atomic_load_n(&(entry[i]), __ATOMIC_ACQUIRE);
            }

            if ((copy[arrayIndex] & me) == 0) {
                copy[arrayIndex] |= me;
                __atomic_store_n(&(entry[arrayIndex]), copy[arrayIndex], __ATOMIC_RELEASE);
            }
        }while (memcmp(copy, full, sizeof(arrayElement) * entryExitLength) != 0 && __atomic_load_n(left, __ATOMIC_ACQUIRE) == 0);

        __atomic_store_n(left, 1, __ATOMIC_RELEASE);
        memset(exit, 0, sizeof(arrayElement) * entryExitLength);
        memset(copy, 0, sizeof(arrayElement) * entryExitLength);

    } else {

#ifdef DEBUG
        for (int i = 0; i < threadCount - 1; ++i) {
            if (successfulBarrierVisitsCount[i] != successfulBarrierVisitsCount[i+1]) {
                printf("thread %i and %i are not equal at %lli %lli\n", i, i+1, (long long)successfulBarrierVisitsCount[i], (long long)successfulBarrierVisitsCount[i+1]);
                assert(0);
            }
        }
#endif

        do {
            copy[arrayIndex] &= notMe;
            for (int i = 0; i < entryExitLength; i += 1) {
                copy[i] |= __atomic_load_n(&(exit[i]), __ATOMIC_ACQUIRE);
            }

            if ((copy[arrayIndex] & me) == 0) {
                copy[arrayIndex] |= me;
                __atomic_store_n(&(exit[arrayIndex]), copy[arrayIndex], __ATOMIC_RELEASE);
            }
        }while (memcmp(copy, full, sizeof(arrayElement) * entryExitLength) != 0 && __atomic_load_n(left, __ATOMIC_ACQUIRE) == 1);

        __atomic_store_n(left, 0, __ATOMIC_RELEASE);
        memset(entry, 0, sizeof(arrayElement) * entryExitLength);
        memset(copy, 0, sizeof(arrayElement) * entryExitLength);

#ifdef DEBUG
        successfulBarrierVisitsCount[index] += 1;
#endif
    }
}

static void measureRonnyArrayBarrier(Context *c, int *threadCounts, int threadCountsLen) {
    //printf("# %s:\n",__func__);

    int *left;
    arrayElement *entry;
    arrayElement *exit;

    int64_t repetitions_;

#ifdef DEBUG
    volatile int64_t *successfulBarrierVisitsCount;
#endif

    void prepare(int threadIndex, int threadCount) {
        const int entryExitLength = ((threadCount - 1)/ARRAY_BITS) + 1;

        if (threadIndex == 0) {
            left = (int*) malloc(sizeof(int));
            entry = (arrayElement*) malloc(sizeof(arrayElement) * entryExitLength);
            exit = (arrayElement*) malloc(sizeof(arrayElement) * entryExitLength);
            *left = 0;
            memset(entry, 0, sizeof(arrayElement) * entryExitLength);
            memset(exit, 0, sizeof(arrayElement) * entryExitLength);

#ifdef DEBUG
            successfulBarrierVisitsCount = (int64_t*) malloc(sizeof(int64_t) * threadCount);
            for (int i = 0; i < threadCount; ++i) {
                successfulBarrierVisitsCount[i] = 0;
            }
#endif
        }
    }
    void finalize(int threadIndex, int threadCount) {
        (void) threadCount;
        if (threadIndex == 0) {
            free(left); left = NULL;
            free(entry); entry = NULL;
            free(exit); exit = NULL;
#ifdef DEBUG
            free((int64_t*) successfulBarrierVisitsCount);
#endif
        }
    }
    void f(int threadIndex, int threadCount) {
        int * const left_ = left;
        arrayElement * const entry_ = entry;
        arrayElement * const exit_ = exit;

        const int arrayIndex = threadIndex/ARRAY_BITS;
        const int entryExitLength = ((threadCount - 1)/ARRAY_BITS) + 1;

        const arrayElement me = ((arrayElement)0x1) << (threadIndex % ARRAY_BITS);
        const arrayElement notMe = ~me;
        arrayElement * const full = (arrayElement*) malloc(sizeof(arrayElement) * entryExitLength);
        memset(full, 0, sizeof(arrayElement) * entryExitLength);
        for (int i = 0; i < threadCount; i += 1) {
            full[i/ARRAY_BITS] |= (((arrayElement)0x1) << (i % ARRAY_BITS));
        }

        arrayElement * const copy = (arrayElement *) malloc(sizeof(arrayElement) * entryExitLength);
        memset(copy, 0, sizeof(arrayElement) * entryExitLength);

        struct timespec begin, end;

        clock_gettime(CLOCK_REALTIME, &begin);
        const time_t supposedEnd = begin.tv_sec + c->minWallSecondsPerMeasurement;

        for(int64_t repetitions = 0;; repetitions += 3) {

#ifdef DEBUG
            barrierRonnyArray(threadIndex, arrayIndex, me, notMe, full, left_, entry_, exit_, copy, entryExitLength, successfulBarrierVisitsCount, threadCount);
            barrierRonnyArray(threadIndex, arrayIndex, me, notMe, full, left_, entry_, exit_, copy, entryExitLength, successfulBarrierVisitsCount, threadCount);
            barrierRonnyArray(threadIndex, arrayIndex, me, notMe, full, left_, entry_, exit_, copy, entryExitLength, successfulBarrierVisitsCount, threadCount);
#else
            barrierRonnyArray(arrayIndex, me, notMe, full, left_, entry_, exit_, copy, entryExitLength);
            barrierRonnyArray(arrayIndex, me, notMe, full, left_, entry_, exit_, copy, entryExitLength);
            barrierRonnyArray(arrayIndex, me, notMe, full, left_, entry_, exit_, copy, entryExitLength);
#endif

            if (repetitions % (3 * 1000) == 0) {
                clock_gettime(CLOCK_REALTIME, &end);
                if (end.tv_sec > supposedEnd) {
                    repetitions_ = repetitions;
                    break;
                }
            }
        }


        free(full);
        free(copy);
    }

    for (int i = 0; i < threadCountsLen; i += 1) {
        MeasurementResult m = measurePowerConsumptionOfFunction(prepare, f, finalize, threadCounts[i], c, False);

        double totalCycles = m.elapsedSeconds * 1000 * 1000 * 1000 * c->clockTicksPerNanoSecond;
        double cyclesPerRepetition = totalCycles / repetitions_;
        double joule = m.powerConsumption * m.elapsedSeconds;
        double nanoJoulePerRepetition = joule * 1000 * 1000 * 1000 / repetitions_;

        printf("ronny-array           t %3d, reps %10lli, wallSecs %.3lf sec, totalPower %3.3lf W, cycles/reps %.3lf, nJ/reps %.3lf\n", threadCounts[i], (long long int)repetitions_, m.elapsedSeconds, m.powerConsumption, cyclesPerRepetition, nanoJoulePerRepetition);
    }
}
/* *** } ronny array barrier *********************************************** */

/* *** ronny no array barrier { ******************************************** */
#ifdef DEBUG
static inline void barrierNoArrayRonny(int index, uint64_t me, uint64_t notMe, const uint64_t * const full, int * const left, uint64_t * const entry, uint64_t * const exit, uint64_t * const copy, volatile int64_t *successfulBarrierVisitsCount, int threadCount) {
#else
static inline void barrierNoArrayRonny(uint64_t me, uint64_t notMe, const uint64_t * const full, int * const left, uint64_t * const entry, uint64_t * const exit, uint64_t * const copy) {
#endif

    if (__atomic_load_n(left, __ATOMIC_ACQUIRE) == 0) {

        do {
            *copy = ((*copy)&notMe)|__atomic_load_n(entry, __ATOMIC_ACQUIRE);

            if (((*copy) & me) == 0) {
                *copy |= me;
                __atomic_store_n(entry, *copy, __ATOMIC_RELEASE);
            }
        }while ((*copy) != (*full) && __atomic_load_n(left, __ATOMIC_ACQUIRE) == 0);

        __atomic_store_n(left, 1, __ATOMIC_RELEASE);
        __atomic_store_n(exit, 0, __ATOMIC_RELEASE);
        __atomic_store_n(copy, 0, __ATOMIC_RELEASE);

    } else {

#ifdef DEBUG
        for (int i = 0; i < threadCount - 1; ++i) {
            if (successfulBarrierVisitsCount[i] != successfulBarrierVisitsCount[i+1]) {
                printf("thread %i and %i are not equal at %lli %lli\n", i, i+1, (long long)successfulBarrierVisitsCount[i], (long long)successfulBarrierVisitsCount[i+1]);
                assert(0);
            }
        }
#endif

        do {
            *copy = ((*copy)&notMe)|__atomic_load_n(exit, __ATOMIC_ACQUIRE);

            if (((*copy) & me) == 0) {
                (*copy) |= me;
                __atomic_store_n(exit, *copy, __ATOMIC_RELEASE);
            }
        }while ((*copy) != (*full) && __atomic_load_n(left, __ATOMIC_ACQUIRE) == 1);

        __atomic_store_n(left, 0, __ATOMIC_RELEASE);
        __atomic_store_n(entry, 0, __ATOMIC_RELEASE);
        __atomic_store_n(copy, 0, __ATOMIC_RELEASE);

#ifdef DEBUG
        successfulBarrierVisitsCount[index] += 1;
#endif
    }
}

static void measureRonnyNoArrayBarrier(Context *c, int *threadCounts, int threadCountsLen) {
    //printf("# %s:\n",__func__);

    int *left;
    uint64_t *entry;
    uint64_t *exit;

    int64_t repetitions_;

#ifdef DEBUG
    volatile int64_t *successfulBarrierVisitsCount;
#endif

    void prepare(int threadIndex, int threadCount) {
        (void) threadCount;
        if (threadIndex == 0) {
            left = (int*) malloc(sizeof(int));
            entry = (uint64_t*) malloc(sizeof(uint64_t));
            exit = (uint64_t*) malloc(sizeof(uint64_t));
            *left = 0;
            *entry = 0;
            *exit = 0;
#ifdef DEBUG
            successfulBarrierVisitsCount = (int64_t*) malloc(sizeof(int64_t) * threadCount);
            for (int i = 0; i < threadCount; ++i) {
                successfulBarrierVisitsCount[i] = 0;
            }
#endif
        }
    }
    void finalize(int threadIndex, int threadCount) {
        (void) threadCount;
        if (threadIndex == 0) {
            free(left); left = NULL;
            free(entry); entry = NULL;
            free(exit); exit = NULL;
#ifdef DEBUG
            free((int64_t*) successfulBarrierVisitsCount);
#endif
        }
    }
    void f(int threadIndex, int threadCount) {
        int * const left_ = left;
        uint64_t * const entry_ = entry;
        uint64_t * const exit_ = exit;

        const uint64_t me = ((uint64_t)0x1) << threadIndex;
        const uint64_t notMe = ~me;
        uint64_t * const full = (uint64_t*) malloc(sizeof(uint64_t));
        *full = 0;
        for (int i = 0; i < threadCount; i += 1) {
            *full |= (((uint64_t)0x1) << i);
        }
        uint64_t * const copy = (uint64_t*) malloc(sizeof(uint64_t));
        *copy = 0;

        struct timespec begin, end;

        clock_gettime(CLOCK_REALTIME, &begin);
        const time_t supposedEnd = begin.tv_sec + c->minWallSecondsPerMeasurement;

        for(int64_t repetitions = 0;; repetitions += 3) {

#ifdef DEBUG
            barrierNoArrayRonny(threadIndex, me, notMe, full, left_, entry_, exit_, copy, successfulBarrierVisitsCount, threadCount);
            barrierNoArrayRonny(threadIndex, me, notMe, full, left_, entry_, exit_, copy, successfulBarrierVisitsCount, threadCount);
            barrierNoArrayRonny(threadIndex, me, notMe, full, left_, entry_, exit_, copy, successfulBarrierVisitsCount, threadCount);
#else
            barrierNoArrayRonny(me, notMe, full, left_, entry_, exit_, copy);
            barrierNoArrayRonny(me, notMe, full, left_, entry_, exit_, copy);
            barrierNoArrayRonny(me, notMe, full, left_, entry_, exit_, copy);
#endif

            if (repetitions % (3 *1000) == 0) {
                clock_gettime(CLOCK_REALTIME, &end);
                if (end.tv_sec > supposedEnd) {
                    repetitions_ = repetitions;
                    break;
                }
            }
        }

        free(full);
        free(copy);
    }

    for (int i = 0; i < threadCountsLen; i += 1) {
        MeasurementResult m = measurePowerConsumptionOfFunction(prepare, f, finalize, threadCounts[i], c, False);

        double totalCycles = m.elapsedSeconds * 1000 * 1000 * 1000 * c->clockTicksPerNanoSecond;
        double cyclesPerRepetition = totalCycles / repetitions_;
        double joule = m.powerConsumption * m.elapsedSeconds;
        double nanoJoulePerRepetition = joule * 1000 * 1000 * 1000 / repetitions_;

        printf("ronny-no-array        t %3d, reps %10lli, wallSecs %.3lf sec, totalPower %3.3lf W, cycles/reps %.3lf, nJ/reps %.3lf\n", threadCounts[i], (long long int)repetitions_, m.elapsedSeconds, m.powerConsumption,  cyclesPerRepetition, nanoJoulePerRepetition);
    }
}
/* *** } ronny no array barrier ******************************************** */

/* *** super wasteful 1 barrier { ****************************************** */
typedef union {
    uint8_t v;
    uint8_t dontAccess[64];
} Sw1Element __attribute__ ((aligned (64)));

static inline void barrierSuperWasteful1(int threadIndex, int threadCount, Sw1Element *barrier, Sw1Element *barrierDel) {
    __atomic_store_n(&(barrier[threadIndex].v), 1, __ATOMIC_RELEASE);

    for(int i = 0; i < threadCount; i += 1) {
        if (__atomic_load_n(&(barrier[i].v), __ATOMIC_ACQUIRE) == 0) {
            i = - 1;
            continue;
        }
    }

    __atomic_store_n(&(barrierDel[threadIndex].v), 0, __ATOMIC_RELEASE);
}

static void measureSuperWastefulBarrier1(Context *c, int *threadCounts, int threadCountsLen) {
    //printf("# %s:\n",__func__);

    Sw1Element *barrier1;
    Sw1Element *barrier2;
    Sw1Element *barrier3;

    int64_t repetitions_;

    void prepare(int threadIndex, int threadCount) {
        (void) threadCount;
        if (threadIndex == 0) {
            barrier1 = (Sw1Element*) malloc(sizeof(Sw1Element) * threadCount);
            barrier2 = (Sw1Element*) malloc(sizeof(Sw1Element) * threadCount);
            barrier3 = (Sw1Element*) malloc(sizeof(Sw1Element) * threadCount);

            for (int i = 0; i < threadCount; i += 1) {
                barrier1[i].v = 0;
                barrier2[i].v = 0;
                barrier3[i].v = 0;
            }
        }
    }
    void finalize(int threadIndex, int threadCount) {
        (void) threadCount;
        if (threadIndex == 0) {
            free((void*)barrier1); barrier1 = NULL;
            free((void*)barrier2); barrier2 = NULL;
            free((void*)barrier3); barrier3 = NULL;
        }
    }
    void f(int threadIndex, int threadCount) {
        struct timespec begin, end;

        clock_gettime(CLOCK_REALTIME, &begin);
        const time_t supposedEnd = begin.tv_sec + c->minWallSecondsPerMeasurement;

        for(int64_t repetitions = 0;; repetitions += 3) {

            barrierSuperWasteful1(threadIndex, threadCount, barrier1, barrier3);
            barrierSuperWasteful1(threadIndex, threadCount, barrier2, barrier1);
            barrierSuperWasteful1(threadIndex, threadCount, barrier3, barrier2);

            if (repetitions % (3 * 1000) == 0) {
                clock_gettime(CLOCK_REALTIME, &end);
                if (end.tv_sec > supposedEnd) {
                    repetitions_ = repetitions;
                    break;
                }
            }
        }
    }

    for (int i = 0; i < threadCountsLen; i += 1) {
        MeasurementResult m = measurePowerConsumptionOfFunction(prepare, f, finalize, threadCounts[i], c, False);

        double totalCycles = m.elapsedSeconds * 1000 * 1000 * 1000 * c->clockTicksPerNanoSecond;
        double cyclesPerRepetition = totalCycles / repetitions_;
        double joule = m.powerConsumption * m.elapsedSeconds;
        double nanoJoulePerRepetition = joule * 1000 * 1000 * 1000 / repetitions_;

        printf("super-wasteful-1      t %3d, reps %10lli, wallSecs %.3lf sec, totalPower %3.3lf W, cycles/reps %.3lf, nJ/reps %.3lf\n", threadCounts[i], (long long int)repetitions_, m.elapsedSeconds, m.powerConsumption,  cyclesPerRepetition, nanoJoulePerRepetition);
    }
}
/* *** } super wasteful 1 barrier ****************************************** */

/* *** super wasteful 2 barrier { ****************************************** */
/* if this int64_t counter overflows the algorithm breaks
   it is just a quick and dirty way to avoid a proper reset implementation */
typedef union {
    int64_t c;
    uint8_t dontAccess[64];
} Sw2Element __attribute__ ((aligned (64)));

static inline void barrierSuperWasteful2(int threadIndex, int threadCount, Sw2Element *barrier, int64_t counter) {
    __atomic_add_fetch(&(barrier[threadIndex].c), 1, __ATOMIC_RELEASE);

    for(int i = 0; i < threadCount; i += 1) {
        if (__atomic_load_n(&(barrier[i].c), __ATOMIC_ACQUIRE) == counter) {
            i = - 1;
            continue;
        }
    }
}

static void measureSuperWastefulBarrier2(Context *c, int *threadCounts, int threadCountsLen) {
    //printf("# %s:\n",__func__);

    Sw2Element *barrier;

    int64_t repetitions_;

    void prepare(int threadIndex, int threadCount) {
        (void) threadCount;
        if (threadIndex == 0) {
            barrier = (Sw2Element*) malloc(sizeof(Sw2Element) * threadCount);
            for (int i = 0; i < threadCount; i += 1) { barrier[i].c = 0; }
        }
    }
    void finalize(int threadIndex, int threadCount) {
        (void) threadCount;
        if (threadIndex == 0) {
            free((void*)barrier); barrier = NULL;
        }
    }
    void f(int threadIndex, int threadCount) {
        struct timespec begin, end;

        clock_gettime(CLOCK_REALTIME, &begin);
        const time_t supposedEnd = begin.tv_sec + c->minWallSecondsPerMeasurement;

        for(int64_t repetitions = 0;; repetitions += 3) {

            barrierSuperWasteful2(threadIndex, threadCount, barrier, repetitions);

            if (repetitions % (3 * 1000) == 0) {
                clock_gettime(CLOCK_REALTIME, &end);
                if (end.tv_sec > supposedEnd) {
                    repetitions_ = repetitions;
                    break;
                }
            }
        }
    }

    for (int i = 0; i < threadCountsLen; i += 1) {
        MeasurementResult m = measurePowerConsumptionOfFunction(prepare, f, finalize, threadCounts[i], c, False);

        double totalCycles = m.elapsedSeconds * 1000 * 1000 * 1000 * c->clockTicksPerNanoSecond;
        double cyclesPerRepetition = totalCycles / repetitions_;
        double joule = m.powerConsumption * m.elapsedSeconds;
        double nanoJoulePerRepetition = joule * 1000 * 1000 * 1000 / repetitions_;

        printf("super-wasteful-2      t %3d, reps %10lli, wallSecs %.3lf sec, totalPower %3.3lf W, cycles/reps %.3lf, nJ/reps %.3lf\n", threadCounts[i], (long long int)repetitions_, m.elapsedSeconds, m.powerConsumption,  cyclesPerRepetition, nanoJoulePerRepetition);
    }
}
/* *** } super wasteful 2 barrier ****************************************** */

/* *** super wasteful 3 barrier { ****************************************** */
/* if this int64_t counter overflows the algorithm breaks
   it is just a quick and dirty way to avoid a proper reset implementation */
typedef union {
    int64_t c;
    uint8_t dontAccess[64];
} Sw3Element __attribute__ ((aligned (64)));

static inline void barrierSuperWasteful3(int threadIndex, int threadCount, Sw3Element *barrier, int64_t counter) {
    __atomic_add_fetch(&(barrier[threadIndex].c), 1, __ATOMIC_RELEASE);

    int first = 0;
    for(int i = 0; i < threadCount; i += 1) {
        if (__atomic_load_n(&(barrier[i].c), __ATOMIC_ACQUIRE) == counter) {
            i = first-1;
            continue;
        }
        first = i;
    }
}

static void measureSuperWastefulBarrier3(Context *c, int *threadCounts, int threadCountsLen) {
    //printf("# %s:\n",__func__);

    Sw3Element *barrier;

    int64_t repetitions_;

    void prepare(int threadIndex, int threadCount) {
        (void) threadCount;
        if (threadIndex == 0) {
            barrier = (Sw3Element*) malloc(sizeof(Sw3Element) * threadCount);
            for (int i = 0; i < threadCount; i += 1) { barrier[i].c = 0; }
        }
    }
    void finalize(int threadIndex, int threadCount) {
        (void) threadCount;
        if (threadIndex == 0) {
            free((void*)barrier); barrier = NULL;
        }
    }
    void f(int threadIndex, int threadCount) {
        struct timespec begin, end;

        clock_gettime(CLOCK_REALTIME, &begin);
        const time_t supposedEnd = begin.tv_sec + c->minWallSecondsPerMeasurement;

        for(int64_t repetitions = 0;; repetitions += 3) {

            barrierSuperWasteful3(threadIndex, threadCount, barrier, repetitions);

            if (repetitions % (3 * 1000) == 0) {
                clock_gettime(CLOCK_REALTIME, &end);
                if (end.tv_sec > supposedEnd) {
                    repetitions_ = repetitions;
                    break;
                }
            }
        }
    }

    for (int i = 0; i < threadCountsLen; i += 1) {
        MeasurementResult m = measurePowerConsumptionOfFunction(prepare, f, finalize, threadCounts[i], c, False);

        double totalCycles = m.elapsedSeconds * 1000 * 1000 * 1000 * c->clockTicksPerNanoSecond;
        double cyclesPerRepetition = totalCycles / repetitions_;
        double joule = m.powerConsumption * m.elapsedSeconds;
        double nanoJoulePerRepetition = joule * 1000 * 1000 * 1000 / repetitions_;

        printf("super-wasteful-3      t %3d, reps %10lli, wallSecs %.3lf sec, totalPower %3.3lf W, cycles/reps %.3lf, nJ/reps %.3lf\n", threadCounts[i], (long long int)repetitions_, m.elapsedSeconds, m.powerConsumption,  cyclesPerRepetition, nanoJoulePerRepetition);
    }
}
/* *** } super wasteful 3 barrier ****************************************** */

/* *** n times add fetch barrier { ***************************************** */
/* same as add-fetch barrier but every thread maintains its own counter */
typedef union {
    int c;
    uint8_t dontAccess[64];
} NtafElement __attribute__ ((aligned (64)));

static inline void barrierNtimesAddFetch(int threadIndex, int threadCount, NtafElement *barrier, NtafElement *barrierDel) {
    for (int i = 0; i < threadCount; i += 1) {
        __atomic_add_fetch(&(barrier[i].c), 1, __ATOMIC_RELEASE);
    }

    while (__atomic_load_n(&(barrier[threadIndex].c), __ATOMIC_ACQUIRE) < threadCount) {}

    __atomic_store_n(&(barrierDel[threadIndex].c), 0, __ATOMIC_RELEASE);
}

static void measureNtimesAddFetchBarrier(Context *c, int *threadCounts, int threadCountsLen) {
    //printf("# %s:\n",__func__);

    NtafElement *barrier1;
    NtafElement *barrier2;
    NtafElement *barrier3;

    int64_t repetitions_;

    void prepare(int threadIndex, int threadCount) {
        (void) threadCount;
        if (threadIndex == 0) {
            barrier1 = (NtafElement*) malloc(sizeof(NtafElement) * threadCount);
            barrier2 = (NtafElement*) malloc(sizeof(NtafElement) * threadCount);
            barrier3 = (NtafElement*) malloc(sizeof(NtafElement) * threadCount);
            for (int i = 0; i < threadCount; i += 1) {
                barrier1[i].c = 0;
                barrier2[i].c = 0;
                barrier3[i].c = 0;
            }
        }
    }
    void finalize(int threadIndex, int threadCount) {
        (void) threadCount;
        if (threadIndex == 0) {
            free((void*)barrier1); barrier1 = NULL;
            free((void*)barrier2); barrier2 = NULL;
            free((void*)barrier3); barrier3 = NULL;
        }
    }
    void f(int threadIndex, int threadCount) {
        struct timespec begin, end;

        clock_gettime(CLOCK_REALTIME, &begin);
        const time_t supposedEnd = begin.tv_sec + c->minWallSecondsPerMeasurement;

        for(int64_t repetitions = 0;; repetitions += 3) {

            barrierNtimesAddFetch(threadIndex, threadCount, barrier1, barrier3);
            barrierNtimesAddFetch(threadIndex, threadCount, barrier2, barrier1);
            barrierNtimesAddFetch(threadIndex, threadCount, barrier3, barrier2);

            if (repetitions % (3 * 1000) == 0) {
                clock_gettime(CLOCK_REALTIME, &end);
                if (end.tv_sec > supposedEnd) {
                    repetitions_ = repetitions;
                    break;
                }
            }
        }
    }

    for (int i = 0; i < threadCountsLen; i += 1) {
        MeasurementResult m = measurePowerConsumptionOfFunction(prepare, f, finalize, threadCounts[i], c, False);

        double totalCycles = m.elapsedSeconds * 1000 * 1000 * 1000 * c->clockTicksPerNanoSecond;
        double cyclesPerRepetition = totalCycles / repetitions_;
        double joule = m.powerConsumption * m.elapsedSeconds;
        double nanoJoulePerRepetition = joule * 1000 * 1000 * 1000 / repetitions_;

        printf("n-times-add-fetch     t %3d, reps %10lli, wallSecs %.3lf sec, totalPower %3.3lf W, cycles/reps %.3lf, nJ/reps %.3lf\n", threadCounts[i], (long long int)repetitions_, m.elapsedSeconds, m.powerConsumption,  cyclesPerRepetition, nanoJoulePerRepetition);
    }
}
/* *** } n times add fetch barrier ***************************************** */

/* *** dissemination barrier 1 { ******************************************* */
typedef union {
    int c;
    uint8_t dontAccess[64];
} D1Element __attribute__ ((aligned (64)));

static inline void barrierDissemination1(int threadIndex, int threadCount, D1Element *barrier, D1Element *delBarrier) {
    for (int distance = 1, round = 0; distance < threadCount; distance *= 2, round += 1) {
        __atomic_add_fetch(&(barrier[(threadIndex + distance) % threadCount].c), 1, __ATOMIC_RELEASE);

        while(__atomic_load_n(&(barrier[threadIndex].c), __ATOMIC_ACQUIRE) <= round) {}
    }
    __atomic_store_n(&(delBarrier[threadIndex].c), 0, __ATOMIC_RELEASE);
}

static void measureDisseminationBarrier1(Context *c, int *threadCounts, int threadCountsLen) {
    //printf("# %s:\n",__func__);

    D1Element *barrier1;
    D1Element *barrier2;
    D1Element *barrier3;
    D1Element *barrier4;

    int64_t repetitions_;
#ifdef DEBUG
    int64_t *repetitions2_;
#endif

    void prepare(int threadIndex, int threadCount) {
        (void) threadCount;
        if (threadIndex == 0) {
            barrier1 = (D1Element*) malloc(sizeof(D1Element) * threadCount);
            barrier2 = (D1Element*) malloc(sizeof(D1Element) * threadCount);
            barrier3 = (D1Element*) malloc(sizeof(D1Element) * threadCount);
            barrier4 = (D1Element*) malloc(sizeof(D1Element) * threadCount);
            for (int i = 0; i < threadCount; i += 1) {
                barrier1[i].c = 0;
                barrier2[i].c = 0;
                barrier3[i].c = 0;
                barrier4[i].c = 0;
            }
#ifdef DEBUG
            repetitions2_ = (int64_t*) malloc(sizeof(int64_t) * threadCount);
            for (int i = 0; i < threadCount; i += 1) { repetitions2_[i] = 0; }
#endif
        }
    }
    void finalize(int threadIndex, int threadCount) {
        (void) threadCount;
        if (threadIndex == 0) {
            free(barrier1); barrier1 = NULL;
            free(barrier2); barrier2 = NULL;
            free(barrier3); barrier3 = NULL;
            free(barrier4); barrier4 = NULL;
#ifdef DEBUG
            free(repetitions2_); repetitions2_ = NULL;
#endif
        }
    }
    void f(int threadIndex, int threadCount) {
        struct timespec begin, end;

        clock_gettime(CLOCK_REALTIME, &begin);
        const time_t supposedEnd = begin.tv_sec + c->minWallSecondsPerMeasurement;

        for(int64_t repetitions = 0;; repetitions += 4) {
#ifdef DEBUG
            repetitions2_[threadIndex] += 1;
#endif


            barrierDissemination1(threadIndex, threadCount, barrier1, barrier1);
            barrierDissemination1(threadIndex, threadCount, barrier2, barrier2);
            barrierDissemination1(threadIndex, threadCount, barrier3, barrier3);
            barrierDissemination1(threadIndex, threadCount, barrier4, barrier4);


            if (repetitions % (4 * 1000) == 0) {

                // incorrect but works since we are constantly syncronizing threads
                // normally some kind of communication between threads needs to happen
                // to consistently exit this loop together
                clock_gettime(CLOCK_REALTIME, &end);

#ifdef DEBUG
                for (int i = 0; i < threadCount; i += 1) {
                    for (int j = i+1; j < threadCount; j += 1) {
                        if (abs(repetitions2_[i] - repetitions2_[j]) > 1) {
                            fprintf(stderr, "repetition counts differ too much. reps[%i] = %li, reps[%i] = %li. aborting\n", i, repetitions2_[i], j, repetitions2_[j]);
                            assert(0);
                        }
                    }
                }
#endif

                if (end.tv_sec > supposedEnd) {
                    repetitions_ = repetitions;
                    break;
                }
            }
        }
    }

    for (int i = 0; i < threadCountsLen; i += 1) {
        MeasurementResult m = measurePowerConsumptionOfFunction(prepare, f, finalize, threadCounts[i], c, False);

        double totalCycles = m.elapsedSeconds * 1000 * 1000 * 1000 * c->clockTicksPerNanoSecond;
        double cyclesPerRepetition = totalCycles / repetitions_;
        double joule = m.powerConsumption * m.elapsedSeconds;
        double nanoJoulePerRepetition = joule * 1000 * 1000 * 1000 / repetitions_;

        printf("dissemination-1       t %3d, reps %10lli, wallSecs %.3lf sec, totalPower %3.3lf W, cycles/reps %.3lf, nJ/reps %.3lf\n", threadCounts[i], (long long int)repetitions_, m.elapsedSeconds, m.powerConsumption,  cyclesPerRepetition, nanoJoulePerRepetition);
    }
}
/* *** } dissemination barrier 1 ******************************************* */

/* *** dissemination barrier 2 { ******************************************* */
/* if this int64_t counter overflows the algorithm breaks
   it is just a quick and dirty way to avoid a proper reset implementation */
typedef union {
    int64_t c;
    uint8_t dontAccess[64];
} D2Element __attribute__ ((aligned (64)));

static inline void barrierDissemination2(int threadIndex, int threadCount, D2Element **barrier, int64_t counter) {
    int to, from;
    for (int distance = 1; distance < threadCount; distance *= 2) {
        to = (threadIndex + distance) % threadCount;
        from = (threadIndex - distance + threadCount) % threadCount;
        __atomic_add_fetch(&(barrier[to][threadIndex].c), 1, __ATOMIC_RELEASE);

        while(__atomic_load_n(&(barrier[threadIndex][from].c), __ATOMIC_ACQUIRE) == counter) {}
    }
}

static void measureDisseminationBarrier2(Context *c, int *threadCounts, int threadCountsLen) {
    //printf("# %s:\n",__func__);

    D2Element **barrier;

    int64_t repetitions_;
#ifdef DEBUG
    int64_t *repetitions2_;
#endif

    void prepare(int threadIndex, int threadCount) {
        (void) threadCount;
        if (threadIndex == 0) {
            barrier = (D2Element**) malloc(sizeof(D2Element*) * threadCount);
            for (int i = 0; i < threadCount; i += 1) {
                barrier[i] = (D2Element*) malloc(sizeof(D2Element) * threadCount);
                for (int j = 0; j < threadCount; j += 1) {
                    barrier[i][j].c = 0;
                }
            }
#ifdef DEBUG
            repetitions2_ = (int64_t*) malloc(sizeof(int64_t) * threadCount);
            for (int i = 0; i < threadCount; i += 1) { repetitions2_[i] = 0; }
#endif
        }
    }
    void finalize(int threadIndex, int threadCount) {
        (void) threadCount;
        if (threadIndex == 0) {
            for (int i = 0; i < threadCount; i += 1) {
                free(barrier[i]); barrier[i] = NULL;
            }
            free(barrier); barrier = NULL;
#ifdef DEBUG
            free(repetitions2_); repetitions2_ = NULL;
#endif
        }
    }
    void f(int threadIndex, int threadCount) {
        struct timespec begin, end;

        clock_gettime(CLOCK_REALTIME, &begin);
        const time_t supposedEnd = begin.tv_sec + c->minWallSecondsPerMeasurement;

        for(int64_t repetitions = 0;; repetitions += 1) {
#ifdef DEBUG
            repetitions2_[threadIndex] += 1;
#endif

            barrierDissemination2(threadIndex, threadCount, barrier, repetitions);

            if (repetitions % (1 * 3000) == 0) {

                // incorrect but works since we are constantly syncronizing threads
                // normally some kind of communication between threads needs to happen
                // to consistently exit this loop together
                clock_gettime(CLOCK_REALTIME, &end);

#ifdef DEBUG
                for (int i = 0; i < threadCount; i += 1) {
                    for (int j = i+1; j < threadCount; j += 1) {
                        if (abs(repetitions2_[i] - repetitions2_[j]) > 1) {
                            fprintf(stderr, "repetition counts differ too much. reps[%i] = %li, reps[%i] = %li. aborting\n", i, repetitions2_[i], j, repetitions2_[j]);
                            assert(0);
                        }
                    }
                }
#endif

                if (end.tv_sec > supposedEnd) {
                    repetitions_ = repetitions;
                    break;
                }
            }
        }
    }

    for (int i = 0; i < threadCountsLen; i += 1) {
        MeasurementResult m = measurePowerConsumptionOfFunction(prepare, f, finalize, threadCounts[i], c, False);

        double totalCycles = m.elapsedSeconds * 1000 * 1000 * 1000 * c->clockTicksPerNanoSecond;
        double cyclesPerRepetition = totalCycles / repetitions_;
        double joule = m.powerConsumption * m.elapsedSeconds;
        double nanoJoulePerRepetition = joule * 1000 * 1000 * 1000 / repetitions_;

        printf("dissemination-2       t %3d, reps %10lli, wallSecs %.3lf sec, totalPower %3.3lf W, cycles/reps %.3lf, nJ/reps %.3lf\n", threadCounts[i], (long long int)repetitions_, m.elapsedSeconds, m.powerConsumption,  cyclesPerRepetition, nanoJoulePerRepetition);
    }
}
/* *** } dissemination barrier 2 ******************************************* */

int main(int argc, char **args) {

    if (argc < 3) {
        printf(
            "  rapl-benchmark <thread-count> <min-wall-seconds-per-measurement> [options]>\n"
            "\n"
            "    --ghz <Ghz>                                 set processor clock, for correct cycle times in measurements (default: 1.0)\n"
            "\n"
            "    --avoid-ht                                  pins each threads to cores 0,2,4... instead of 0,1,2,...\n"
            "\n"
            "    --sleep-power <watt>                        set sleep power and don't measure anew\n"
            "    --uncore-power <watt>                       set uncore power and don't measure anew\n"
            "\n"
            "    --add-fetch-barrier <thread-count-list>     measure add-fetch barrier with threads according to the space delimited list\n"
            "    --add-fetch-wait-spinning <thread-count-list>\n"
            "    --add-fetch-uncontested <thread-count-list>\n"
            "    --ronny-array <thread-count-list>\n"
            "    --ronny-no-array <thread-count-list>\n"
            "    --super-wasteful-1 <thread-count-list>\n"
            "    --super-wasteful-2 <thread-count-list>\n"
            "    --super-wasteful-3 <thread-count-list>\n"
            "    --local-counter <thread-count-list>\n"
            "    --dissemination-1 <thread-count-list>\n"
            "    --dissemination-2 <thread-count-list>\n"
            );

        exit(0);
    }

    int threadCount = atoi(args[1]);
    int minWallSecondsPerMeasurement = atoll(args[2]);
    Bool avoidHt = False;
    double clockTicksPerNanoSecond = 1.0;
    double sleepPowerConsumption = 0.0;
    double uncorePowerConsumption = 0.0;

    Bool measureAddFetchBarrier_ = False;
    int *addFetchThreadCountList = NULL;
    int addFetchThreadCountListLen = 0;

    Bool measureAddFetchWaitSpinning_ = False;
    int *addFetchWaitSpinningThreadCountList = NULL;
    int addFetchWaitSpinningThreadCountListLen = 0;

    Bool measureAddFetchUncontested_ = False;
    int *addFetchUncontestedThreadCountList = NULL;
    int addFetchUncontestedThreadCountListLen = 0;

    Bool measureRonnyArrayBarrier_ = False;
    int *ronnyArrayThreadCountList = NULL;
    int ronnyArrayThreadCountListLen = 0;

    Bool measureRonnyNoArrayBarrier_ = False;
    int *ronnyNoArrayThreadCountList = NULL;
    int ronnyNoArrayThreadCountListLen = 0;

    Bool measureSuperWastefulBarrier1_ = False;
    int *superWasteful1ThreadCountList = NULL;
    int superWasteful1ThreadCountListLen = 0;

    Bool measureSuperWastefulBarrier2_ = False;
    int *superWasteful2ThreadCountList = NULL;
    int superWasteful2ThreadCountListLen = 0;

    Bool measureSuperWastefulBarrier3_ = False;
    int *superWasteful3ThreadCountList = NULL;
    int superWasteful3ThreadCountListLen = 0;

    Bool measureNtimesAddFetchBarrier_ = False;
    int *ntimesAddFetchThreadCountList = NULL;
    int ntimesAddFetchThreadCountListLen = 0;

    Bool measureDisseminationBarrier1_ = False;
    int *dissemination1ThreadCountList = NULL;
    int dissemination1ThreadCountListLen = 0;

    Bool measureDisseminationBarrier2_ = False;
    int *dissemination2ThreadCountList = NULL;
    int dissemination2ThreadCountListLen = 0;

    for (int i = 3; i < argc; i += 1) {
        if (strcmp("--avoid-ht", args[i]) == 0) {
            avoidHt = True;
        } else if (strcmp("--ghz", args[i]) == 0) {
            assert(i + 1 < argc);
            clockTicksPerNanoSecond = atof(args[i+1]);
            i += 1;
        } else if (strcmp("--add-fetch-barrier", args[i]) == 0) {
            measureAddFetchBarrier_ = True;
            threadListFromArguments(args, argc, i+1, &addFetchThreadCountList, &addFetchThreadCountListLen, 2, threadCount);
            i += addFetchThreadCountListLen;
        } else if (strcmp("--add-fetch-wait-spinning", args[i]) == 0) {
            measureAddFetchWaitSpinning_ = True;
            threadListFromArguments(args, argc, i+1, &addFetchWaitSpinningThreadCountList, &addFetchWaitSpinningThreadCountListLen, 2, threadCount);
            i += addFetchWaitSpinningThreadCountListLen;
        } else if (strcmp("--add-fetch-uncontested", args[i]) == 0) {
            measureAddFetchUncontested_ = True;
            threadListFromArguments(args, argc, i+1, &addFetchUncontestedThreadCountList, &addFetchUncontestedThreadCountListLen, 1, threadCount);
            i += addFetchUncontestedThreadCountListLen;
        } else if (strcmp("--ronny-array", args[i]) == 0) {
            measureRonnyArrayBarrier_ = True;
            threadListFromArguments(args, argc, i+1, &ronnyArrayThreadCountList, &ronnyArrayThreadCountListLen, 2, threadCount);
            i += ronnyArrayThreadCountListLen;
        } else if (strcmp("--ronny-no-array", args[i]) == 0) {
            measureRonnyNoArrayBarrier_ = True;
            threadListFromArguments(args, argc, i+1, &ronnyNoArrayThreadCountList, &ronnyNoArrayThreadCountListLen, 2, threadCount);
            i += ronnyNoArrayThreadCountListLen;
        } else if (strcmp("--super-wasteful-1", args[i]) == 0) {
            measureSuperWastefulBarrier1_ = True;
            threadListFromArguments(args, argc, i+1, &superWasteful1ThreadCountList, &superWasteful1ThreadCountListLen, 2, threadCount);
            i += superWasteful1ThreadCountListLen;
        } else if (strcmp("--super-wasteful-2", args[i]) == 0) {
            measureSuperWastefulBarrier2_ = True;
            threadListFromArguments(args, argc, i+1, &superWasteful2ThreadCountList, &superWasteful2ThreadCountListLen, 2, threadCount);
            i += superWasteful2ThreadCountListLen;
        } else if (strcmp("--super-wasteful-3", args[i]) == 0) {
            measureSuperWastefulBarrier3_ = True;
            threadListFromArguments(args, argc, i+1, &superWasteful3ThreadCountList, &superWasteful3ThreadCountListLen, 2, threadCount);
            i += superWasteful3ThreadCountListLen;
        } else if (strcmp("--n-times-add-fetch", args[i]) == 0) {
            measureNtimesAddFetchBarrier_ = True;
            threadListFromArguments(args, argc, i+1, &ntimesAddFetchThreadCountList, &ntimesAddFetchThreadCountListLen, 2, threadCount);
            i += ntimesAddFetchThreadCountListLen;
        } else if (strcmp("--dissemination-1", args[i]) == 0) {
            measureDisseminationBarrier1_ = True;
            threadListFromArguments(args, argc, i+1, &dissemination1ThreadCountList, &dissemination1ThreadCountListLen, 2, threadCount);
            i += dissemination1ThreadCountListLen;
        } else if (strcmp("--dissemination-2", args[i]) == 0) {
            measureDisseminationBarrier2_ = True;
            threadListFromArguments(args, argc, i+1, &dissemination2ThreadCountList, &dissemination2ThreadCountListLen, 2, threadCount);
            i += dissemination2ThreadCountListLen;
        } else if (strcmp("--sleep-power", args[i]) == 0) {
            i += 1;
            sleepPowerConsumption = atof(args[i]);
        } else if (strcmp("--uncore-power", args[i]) == 0) {
            i += 1;
            uncorePowerConsumption = atof(args[i]);
        } else {
            printf("unknown argument: \"%s\"\n", args[i]);
            exit(-1);
        }
    }

    assert(threadCount > 0);
    assert(minWallSecondsPerMeasurement > 0);
    assert(clockTicksPerNanoSecond > 0.0);

    Context *context = newContext(threadCount, minWallSecondsPerMeasurement, clockTicksPerNanoSecond, avoidHt, sleepPowerConsumption, uncorePowerConsumption);

    if (context->sleepPowerConsumption == 0.0) measureSleepPowerConsumption(context, True);
    if (context->uncorePowerConsumption == 0.0) measureUncorePowerConsumption(context, True);

    if (measureAddFetchBarrier_ == True) {
        measureAddFetchBarrier(context, addFetchThreadCountList, addFetchThreadCountListLen);
        free(addFetchThreadCountList);
    }

    if (measureAddFetchWaitSpinning_ == True) {
        measureAddFetchWaitSpinning(context, addFetchWaitSpinningThreadCountList, addFetchWaitSpinningThreadCountListLen);
        free(addFetchWaitSpinningThreadCountList);
    }

    if (measureAddFetchUncontested_ == True) {
        measureAddFetchUncontested(context, addFetchUncontestedThreadCountList, addFetchUncontestedThreadCountListLen);
        free(addFetchUncontestedThreadCountList);
    }

    if (measureRonnyArrayBarrier_ == True) {
        measureRonnyArrayBarrier(context, ronnyArrayThreadCountList, ronnyArrayThreadCountListLen);
        free(ronnyArrayThreadCountList);
    }

    if (measureRonnyNoArrayBarrier_ == True) {
        measureRonnyNoArrayBarrier(context, ronnyNoArrayThreadCountList, ronnyNoArrayThreadCountListLen);
        free(ronnyNoArrayThreadCountList);
    }

    if (measureSuperWastefulBarrier1_ == True) {
        measureSuperWastefulBarrier1(context, superWasteful1ThreadCountList, superWasteful1ThreadCountListLen);
        free(superWasteful1ThreadCountList);
    }

    if (measureSuperWastefulBarrier2_ == True) {
        measureSuperWastefulBarrier2(context, superWasteful2ThreadCountList, superWasteful2ThreadCountListLen);
        free(superWasteful2ThreadCountList);
    }

    if (measureSuperWastefulBarrier3_ == True) {
        measureSuperWastefulBarrier3(context, superWasteful3ThreadCountList, superWasteful3ThreadCountListLen);
        free(superWasteful3ThreadCountList);
    }

    if (measureNtimesAddFetchBarrier_ == True) {
        measureNtimesAddFetchBarrier(context, ntimesAddFetchThreadCountList, ntimesAddFetchThreadCountListLen);
        free(ntimesAddFetchThreadCountList);
    }

    if (measureDisseminationBarrier1_ == True) {
        measureDisseminationBarrier1(context, dissemination1ThreadCountList, dissemination1ThreadCountListLen);
        free(dissemination1ThreadCountList);
    }

    if (measureDisseminationBarrier2_ == True) {
        measureDisseminationBarrier2(context, dissemination2ThreadCountList, dissemination2ThreadCountListLen);
        free(dissemination2ThreadCountList);
    }

    printContext(context);

    freeContext(context);

    return 0;


    //setupWorkload(threadCount);

    //cout << "MOV %%RCX,(%0) (Store)" << runWorkload(threadCount,[]{ ASM_CODE("MOV %%RCX,(%0)",1000000) },1000000, clockTicksPerNanoSecond) << endl;
    //cout << "XCHG %%R8,(%0)" << runWorkload(threadCount,[]{ ASM_CODE("XCHG %%R8,(%0)",100000) }, 100000, clockTicksPerNanoSecond) << endl;
    //cout << "MOV (%0),%%R8 (Load)" << runWorkload(threadCount,[]{ ASM_CODE("MOV (%0),%%R8",1000000) },1000000, clockTicksPerNanoSecond) << endl;

    //cout << "L_MOV %%RCX,(%0) (Store)" << runWorkload(threadCount,[]{ ASM_CODE("MOV %%RCX,(%1)",1000000) },1000000, clockTicksPerNanoSecond) << endl;
    //cout << "L_XCHG %%R8,(%0)" << runWorkload(threadCount,[]{ ASM_CODE("XCHG %%R8,(%1)",100000) }, 100000, clockTicksPerNanoSecond) << endl;
    //cout << "L_MOV (%0),%%R8 (Load)" << runWorkload(threadCount,[]{ ASM_CODE("MOV (%1),%%R8",1000000) },1000000, clockTicksPerNanoSecond) << endl;

    return 0;
}
