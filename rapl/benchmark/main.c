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


typedef struct {
    int threadCount;
    double minWallSecondsPerMeasurement;
    int msrFile;
    double raplEnergyMultiplier;
    double sleepPowerConsumption; //Watt
    double uncorePowerConsumption; //Watt
}Context;

typedef struct {
    int index;
    Context *c;
    double elapsedSeconds;
    double usedJoule;
} ThreadInfo;


static int openMsrFile() {
    int fd = open("/dev/cpu/0/msr",O_RDONLY);
    if (fd == -1) {
        fprintf(stderr, "failed opening msr file: \"%s\"\n", strerror(errno));
        assert(0);
    }
    return fd;
    return 0;
}
static inline uint64_t msr(int msrFile, uint32_t offset) {
    uint64_t value;
    if (pread(msrFile, &value, sizeof(uint64_t), offset) != sizeof(uint64_t)) {
        fprintf(stderr, "failed seeking %lu bytes from offset %x in msr\n", sizeof(uint64_t), offset);
        assert(0);
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

void setThreadAffinity(int threadIndex) {
    cpu_set_t cpuset;
    CPU_ZERO(&cpuset);
    CPU_SET(threadIndex % sysconf(_SC_NPROCESSORS_ONLN), &cpuset);
    assert(pthread_setaffinity_np(pthread_self(), sizeof(cpu_set_t), &cpuset) == 0);
}

static inline double seconds(struct timespec t) {
    return t.tv_sec + (t.tv_nsec / 1000000000.0);
}
static inline uint64_t nanoSeconds(struct timespec t) {
    return ((uint64_t)t.tv_sec * 1000000000 + (uint64_t)t.tv_nsec);
}
static inline uint64_t cycles(struct timespec t, double clockTicksPerNanoSecond) {
    return (uint64_t)(nanoSeconds(t) * clockTicksPerNanoSecond);
}


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


static inline double measurePowerConsumptionOfFunction(void prepare(), void f(), void finalize(), int threads, Context *c) {

    int startBarrier;
    int stopBarrier;
    ThreadInfo *infos = NULL;
    pthread_t *t = NULL;

    void* threadFunction(void *userData) {
        uint64_t beginEnergy;
        uint64_t endEnergy;
        struct timespec beginTime;
        struct timespec endTime;

        ThreadInfo *info = (ThreadInfo*) userData;
        const Context *c = info->c;

        const int index = info->index;

        setThreadAffinity(index);

        prepare();

        beginEnergy = energy(c->msrFile);
        clock_gettime(CLOCK_REALTIME, &beginTime);

        waitBarrier(&startBarrier);
        f();
        waitBarrier(&stopBarrier);

        endEnergy = energy(c->msrFile);
        clock_gettime(CLOCK_REALTIME, &endTime);

        finalize();

        info->elapsedSeconds = seconds(endTime) - seconds(beginTime);
        info->usedJoule = energyToJoule(endEnergy - beginEnergy, c->raplEnergyMultiplier);

        return NULL;
    }


    do {
        initBarrier(&startBarrier, threads);
        initBarrier(&stopBarrier, threads);

        free(infos);
        free(t);

        infos = (ThreadInfo*) malloc(sizeof(ThreadInfo) * threads);
        t = (pthread_t*) malloc(sizeof(pthread_t) * threads);

        /* start all threads */
        for (int i = 0; i < threads; i += 1) {
            infos[i].index = i;
            infos[i].c = c;
            infos[i].elapsedSeconds = 0.0;
            infos[i].usedJoule = 0.0;
            if(pthread_create(&t[i], NULL, threadFunction, (void *)&(infos[i]))){
                perror("pthread_create");
                exit(-1);
            }
        }

        /* join all threads */
        for (int i = 0; i < threads; i += 1) {
            if(pthread_join(t[i], NULL)){
                perror("pthread_join");
                exit(-1);
            }
        }

    } while(infos[0].usedJoule < 0.0); // repeat incase of wrap around in the energy counter register

    // use results of thread zero only, deviation due to the barriers is ~10^-6 seconds
    // and since rapl has a 10*-3 seconds resolution no difference can be seen.
    //
    // we still keep the data/code on all threads since we have only one struct ThreadInfo,
    // and would need an extra if (index == 0) {}

    double elapsedSeconds = infos[0].elapsedSeconds;
    double powerConsumption = infos[0].usedJoule / elapsedSeconds;

    printf("# measurement: %2d threads, time %lf sec, power %lf W\n", threads, elapsedSeconds, powerConsumption);

    if (elapsedSeconds < c->minWallSecondsPerMeasurement) {
        printf("#    %lf s < %.0lf s : less benchmarking time than desired\n", elapsedSeconds, c->minWallSecondsPerMeasurement);
    }

    return powerConsumption;
}

Context* newContext(int threadCount, int minWallSecondsPerMeasurement) {

    long cpuCount = sysconf(_SC_NPROCESSORS_ONLN);
    if (threadCount > cpuCount) {
        printf("threadcount: %i > cpucount: %li. threads will be pinned round robin.\n", threadCount, cpuCount);
    }

    Context *ret = (Context*) malloc(sizeof(Context));
    assert(ret != NULL);

    ret->threadCount = threadCount;
    ret->minWallSecondsPerMeasurement = minWallSecondsPerMeasurement;

    ret->msrFile = openMsrFile();

    ret->raplEnergyMultiplier = pow(0.5,(msr(ret->msrFile, 0x606)>>8) & 0x1F);

    ret->sleepPowerConsumption = 0.0;
    ret->uncorePowerConsumption = 0.0;

    return ret;
}
void freeContext(Context *c) {
    closeMsrFile(c->msrFile);
    free(c);
}


void printContext(Context *c) {
    printf("threads %2d, sleepPower %lf W, uncorePower %lf W\n", c->threadCount, c->sleepPowerConsumption, c->uncorePowerConsumption);
}


void measureSleepPowerConsumption(Context *c) {
    void prepare() {}
    void finalize() {}
    void f() {
        sleep(c->minWallSecondsPerMeasurement);
    }
    c->sleepPowerConsumption = measurePowerConsumptionOfFunction(prepare, f, finalize, 1, c);
}


// does not include sleep power consumption
#define repetitionsPerLoop "20 * 1000"
#define loopCount "1000 * 1000"
void measureUncorePowerConsumption(Context *c) {
    assert(c->sleepPowerConsumption > 0.0);

    double powerConsumption;
    double previousPowerConsumption = c->sleepPowerConsumption;

    double firstCorePowerConsumption;
    double addedDifferences = 0.0;

    void prepare() {}
    void finalize() {}
    void f() {
        __asm__ __volatile__ (
            "\t"    "mov $" loopCount ",%%rcx;\n"
            "\t"    "1:\n"
            "\t"    ".rept (" repetitionsPerLoop ");\n"
            "\t\t"      "xor %%rax,%%rax;\n"
            "\t"    ".endr;\n"
            "\t"    "sub $1,%%rcx;\n"
            "\t"    "jnc 1b\n"
            : : : "rcx", "rax");
    }

    for (int threads = 1; threads <= c->threadCount; threads += 1, previousPowerConsumption = powerConsumption) {

        powerConsumption = measurePowerConsumptionOfFunction(prepare, f, finalize, threads, c);

        if (threads == 1) {
            firstCorePowerConsumption = powerConsumption - c->sleepPowerConsumption;
        } else {
            addedDifferences += powerConsumption - previousPowerConsumption;
        }

        //printf("%d: %lf W, added diffs: %lf W\n", threads, powerConsumption, addedDifferences);
    }

    c->uncorePowerConsumption = firstCorePowerConsumption - (addedDifferences / (c->threadCount-1));
}
#undef repetitionsPerLoop
#undef loopCount


int main(int argc, char **args) {

    if (argc < 3) {
        printf(
            "  rapl-benchmark <threadcount> <minWallSecondsPerMeasurement> <clockTicksPerNanoSecond (Ghz) (default: 1)>\n"
            );

        exit(0);
    }

    int threadCount = atoi(args[1]);
    int minWallSecondsPerMeasurement = atoll(args[2]);
    float clockTicksPerNanoSecond = argc > 3 ? (float)atof(args[3]) : 1.0f;

    assert(threadCount > 0);
    assert(minWallSecondsPerMeasurement > 0);
    assert(clockTicksPerNanoSecond > 0.0);

    Context *context = newContext(threadCount, minWallSecondsPerMeasurement);

    measureSleepPowerConsumption(context);
    measureUncorePowerConsumption(context);

    //TODO real work

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
