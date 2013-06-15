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


void* Thread(void*);

typedef struct {
    int threadCount;
    double minWallSecondsPerMeasurement;
    int startBarrier;
    int stopBarrier;
    int msrFile;
    double raplEnergyMultiplier;
    double sleepPowerConsumption; //Watt
    double uncorePowerConsumption; //Watt
}Context;

typedef struct {
    int index;
    Context *c;
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
static void initBarrier(int *bar, int threadCount) {
    *bar = threadCount;
}
static inline void barrier(int *bar) {
    if (__atomic_add_fetch(bar, -1, __ATOMIC_ACQ_REL) != 0) {
        while (__atomic_load_n (bar, __ATOMIC_ACQUIRE) != 0) {
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


// needs to be done this way to get the instruction string during compile time as the inline assembler wants it
// you rather read measurePowerConsumptionOfFunction instead of this. does the same
//
// missing minimum wall time in the loop. since i don't understand the asm code, and weird shit happens
// i can't yet do it. (adapt from measurePowerConsumptionOfFunction later TODO)
#define measurePowerConsumptionOfAssembler2(functionName, instruction, loopCount, repetitionsPerLoop ) \
\
double functionName(int msrFile, double minMeasureTime, double raplEnergyMultiplier) { \
    uint64_t beginEnergy; \
    uint64_t endEnergy; \
    struct timespec beginTime; \
    struct timespec endTime; \
    double secondsElapsed; \
\
    uint64_t temp[loopCount]; \
\
    uint64_t *localTemp = malloc(sizeof(unsigned long long) * repetitionsPerLoop); \
    clock_gettime(CLOCK_REALTIME, &beginTime); \
    __asm__ __volatile__ ( \
        "MOV $" #loopCount ",%%RCX;" \
        "1:" \
        ".rept (" #repetitionsPerLoop ");" \
        instruction ";" \
        ".endr;" \
        "SUB $1,%%RCX;" \
        "JNC 1b\n" \
        : : "r" (&temp), "r"(localTemp): "rcx", "rax", "r8", "r9", "r10"); \
    clock_gettime(CLOCK_REALTIME, &endTime); \
    free(localTemp); \
\
    secondsElapsed = seconds(endTime) - seconds(beginTime); \
    if (secondsElapsed < 1.0) { \
        fprintf(stderr, "Your to-be-measured function runs %lf seconds. at least 0.1s are desired to reduce measurement side effects.\n", secondsElapsed); \
    } \
\
    do { \
        uint64_t *localTemp = malloc(sizeof(unsigned long long) * repetitionsPerLoop); \
\
        beginEnergy = energy(msrFile); \
        clock_gettime(CLOCK_REALTIME, &beginTime); \
\
        __asm__ __volatile__ ( \
            "MOV $" #loopCount ",%%RCX;" \
            "1:" \
            ".rept (" #repetitionsPerLoop ");" \
            instruction ";" \
            ".endr;" \
            "SUB $1,%%RCX;" \
            "JNC 1b\n" \
            : : "r" (&temp), "r" (localTemp): "rcx", "rax", "r8", "r9", "r10"); \
\
        endEnergy = energy(msrFile); \
        clock_gettime(CLOCK_REALTIME, &endTime); \
\
        free(localTemp); \
    } while (endEnergy <= beginEnergy); \
\
    printf("measurement took %lf seconds\n", seconds(endTime) - seconds(beginTime));\
\
    return energyToJoule((endEnergy - beginEnergy) / (seconds(endTime) - seconds(beginTime)), raplEnergyMultiplier); \
}

#define measurePowerConsumptionOfAssembler(functionName, instruction) \
    measurePowerConsumptionOfAssembler2(functionName, instruction, 1000*1000, 20*1000)


static inline double measurePowerConsumptionOfFunction(void f(void), int msrFile, double minWallSeconds, double raplEnergyMultiplier) {
    uint64_t beginEnergy;
    uint64_t endEnergy;
    struct timespec beginTime;
    struct timespec endTime;
    double secondsElapsed;

    // do one test run
    clock_gettime(CLOCK_REALTIME, &beginTime);
    f();
    clock_gettime(CLOCK_REALTIME, &endTime);

    secondsElapsed = seconds(endTime) - seconds(beginTime);
    if (secondsElapsed < 0.1) {
        printf("Your to-be-measured function runs %lf seconds. at least 0.1s are desired to reduce measurement side effects.\n", secondsElapsed);
        assert(0);
    }


    do {
        beginEnergy = energy(msrFile);
        clock_gettime(CLOCK_REALTIME, &beginTime);

        do {
            f();

            endEnergy = energy(msrFile);
            clock_gettime(CLOCK_REALTIME, &endTime);

        } while ((seconds(endTime) - seconds(beginTime)) < minWallSeconds);

    } while (endEnergy <= beginEnergy); // in case wrap around

    printf("measurement took %lf seconds\n", seconds(endTime) - seconds(beginTime));

    return energyToJoule((endEnergy - beginEnergy) / (seconds(endTime) - seconds(beginTime)), raplEnergyMultiplier);
}

double sleepPowerConsumption(int msrFile, double minWallSeconds, double raplEnergyMultiplier) {
    void x() {
        sleep(minWallSeconds);
    }
    return measurePowerConsumptionOfFunction(x, msrFile, 0.0, raplEnergyMultiplier);
}


double uncorePowerConsumption(int threadCount, int msrFile, double minWallSeconds, double sleepPowerConsumption, double raplEnergyMultiplier) {
    double powerConsumption;
    double previousPowerConsumption = sleepPowerConsumption;

    double firstCorePowerConsumption;
    double addedDifferences = 0.0;

    measurePowerConsumptionOfAssembler(bench, "XOR %%RAX,%%RAX");

    for (int threads = 1; threads <= threadCount; threads += 1, previousPowerConsumption = powerConsumption) {

        powerConsumption = bench(msrFile, minWallSeconds, raplEnergyMultiplier);

        if (threads == 1) {
            firstCorePowerConsumption = powerConsumption - sleepPowerConsumption;
        } else {
            addedDifferences += powerConsumption - previousPowerConsumption;
        }

        printf("%d: %lf W, added diffs: %lf W\n", threads, powerConsumption, addedDifferences);
    }
    return firstCorePowerConsumption - (addedDifferences / (threadCount-1));
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
    initBarrier(&(ret->startBarrier), threadCount);
    initBarrier(&(ret->stopBarrier), threadCount);

    ret->msrFile = openMsrFile();

    ret->raplEnergyMultiplier = pow(0.5,(msr(ret->msrFile, 0x606)>>8) & 0x1F);

    ret->sleepPowerConsumption = sleepPowerConsumption(ret->msrFile, ret->minWallSecondsPerMeasurement, ret->raplEnergyMultiplier);
    ret->uncorePowerConsumption = uncorePowerConsumption(threadCount, ret->msrFile, ret->minWallSecondsPerMeasurement, ret->sleepPowerConsumption, ret->raplEnergyMultiplier);

    return ret;
}
void freeContext(Context *c) {
    closeMsrFile(c->msrFile);
    free(c);
}

void printResults(Context *c) {
    printf("threads: %2d, sleepPower %lf W, uncorePower %lf W\n", c->threadCount, c->sleepPowerConsumption, c->uncorePowerConsumption);
}


void* Thread(void *userData) {

    ThreadInfo *info = (ThreadInfo*) userData;
    Context *c = info->c;

    int index = info->index;
    int threadCount = c->threadCount;
    int minWallSecondsPerMeasurement = c->minWallSecondsPerMeasurement;

    (void) threadCount;
    (void) minWallSecondsPerMeasurement;

    setThreadAffinity(index);


    barrier(&(c->startBarrier));

    //func();

    barrier(&(c->stopBarrier));

    return NULL;
}


//inline void runAndJoin(int threadCount, std::function<void (void)> func) {
//    startBarrier = threadCount;
//    stopBarrier = threadCount;
//
//    for (intptr_t c = 0; c < threadCount; c++) {
//        threads[c] = new std::thread(worker,c,func);
//    }
//
//    for (unsigned int i = 0; i < threadCount; i++) {
//        threads[i]->join();
//    } 
//}


//Result runWorkload(int cpus, std::function<void (void)> func, int iterations, float clockTicksPerNanoSecond) {
//    Result res;
//
//    double totE  = getEnergy();
//    uint64_t totT = gtod();
//
//    runAndJoin(cpus,func);
//
//    totE = getEnergy() - totE;
//    totT = gtod() - totT;
//
//    //Todo:: Remove uncore base power and static power!!;
//    res.energy = totE;
//    res.time = totT/1000000.0;
//    res.energyPerBlock = (totE)/(iterations*4096.0*cpus);
//    res.timePerBlock = (res.time)/(iterations*4096.0*cpus); 
//    res.cyclesPerBlock = res.timePerBlock*CPU_FREQ;
//    res.power = (totE/res.time-pUncore-pStatic)/cpus; //clear instruction power ... w/o uncore/static
//
//    return  res;
//}


int main(int argc, char **args) {

    if (argc < 3) {
        printf(
            "  energy-benchmark <threadcount> <minWallSecondsPerMeasurement> <clockTicksPerNanoSecond (Ghz) (default: 1)>\n"
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
    ThreadInfo infos[threadCount];
    pthread_t t[threadCount];

    /* start all threads */
    for (int i = 0; i < threadCount; i += 1) {
        infos[i].index = i;
        infos[i].c = context;
        if(pthread_create(&t[i], NULL, Thread, (void *)&(infos[i]))){
            perror("pthread_create");
            exit(-1);
        }
    }

    /* join all threads */
    for (int i = 0; i < threadCount; i += 1) {
        if(pthread_join(t[i], NULL)){
            perror("pthread_join");
            exit(-1);
        }
    }


    printResults(context);

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
