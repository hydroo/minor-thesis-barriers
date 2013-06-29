#define _GNU_SOURCE
#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <math.h>
#include <stdarg.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#include <mpi.h>


typedef enum {
    False = 0,
    True = 1
} Bool;


typedef struct {
    int processIndex;
    int processCount;
    double minWallSecondsPerMeasurement;
    double clockTicksPerNanoSecond;
    int msrFile;
    double raplEnergyMultiplier;
}Context;

typedef struct {
    double elapsedSeconds;
    double powerConsumption; // watt
} MeasurementResult;

/* *** helper { ************************************************************ */
static int openMsrFile() {
    int fd = open("/dev/cpu/0/msr",O_RDONLY);
    if (fd == -1) {
        fprintf(stderr, "failed opening msr file: \"%s\"\n", strerror(errno));
        assert(0);
    }
    return fd;
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
static inline double seconds(struct timespec t) {
    return t.tv_sec + (t.tv_nsec / 1000000000.0);
}
static inline uint64_t nanoSeconds(struct timespec t) {
    return ((uint64_t)t.tv_sec * 1000000000 + (uint64_t)t.tv_nsec);
}

// print only on process 0
static inline void printf0(const char* fmt, ...) {
    int rank;
    MPI_Comm_rank(MPI_COMM_WORLD, &rank);
    if (rank == 0) {
        va_list args;
        va_start(args, fmt);
        vprintf(fmt, args);
        va_end(args);
    }
}
/* *** } helper ************************************************************ */
static Context* newContext(int minWallSecondsPerMeasurement, double clockTicksPerNanoSecond) {


    Context *ret = (Context*) malloc(sizeof(Context));
    assert(ret != NULL);

    MPI_Comm_rank(MPI_COMM_WORLD, &(ret->processIndex));
    MPI_Comm_size(MPI_COMM_WORLD, &(ret->processCount));
    ret->minWallSecondsPerMeasurement = minWallSecondsPerMeasurement;
    ret->clockTicksPerNanoSecond = clockTicksPerNanoSecond;

    ret->msrFile = openMsrFile();

    ret->raplEnergyMultiplier = pow(0.5,(msr(ret->msrFile, 0x606)>>8) & 0x1F);

    return ret;
}
static void freeContext(Context *c) {
    closeMsrFile(c->msrFile);
    free(c);
}
static void printContext(Context *c) {
    printf0("# context p %3d, \n", c->processCount);
}


static inline MeasurementResult measurePowerConsumptionOfFunction(void prepare(int processIndex, int processCount), void f(int processIndex, int processCount), void finalize(int processIndex, int processCount), Context *c, Bool autoPrint) {

    uint64_t beginEnergy;
    uint64_t endEnergy;
    struct timespec beginTime;
    struct timespec endTime;
    const int msrFile = c->msrFile;
    int processIndex = c->processIndex;
    int processCount = c->processCount;

    int raplOverflowSend;
    int raplOverflowReceive;

    do {
        prepare(processIndex, processCount);

        beginEnergy = energy(msrFile);
        clock_gettime(CLOCK_REALTIME, &beginTime);

        MPI_Barrier(MPI_COMM_WORLD);
        f(processIndex, processCount);
        MPI_Barrier(MPI_COMM_WORLD);

        endEnergy = energy(msrFile);
        clock_gettime(CLOCK_REALTIME, &endTime);

        finalize(processIndex, processCount);


        raplOverflowSend = (int64_t)endEnergy - (int64_t)beginEnergy < 0 ? 1 : 0;

        MPI_Allreduce(&raplOverflowSend, &raplOverflowReceive, 1, MPI_INT, MPI_MAX, MPI_COMM_WORLD);

        if (c->processIndex == 0 && raplOverflowReceive == True) {
            printf("# %i rapl overflow. redo measurement.", c->processIndex);
        }

    } while(raplOverflowReceive == True);


    MeasurementResult m;
    m.elapsedSeconds = seconds(endTime) - seconds(beginTime);
    m.powerConsumption = energyToJoule(endEnergy - beginEnergy, c->raplEnergyMultiplier) / m.elapsedSeconds;

    if (autoPrint == True) {
        printf("# %i measurement p %3d wallSecs %.3lf, totalPower %3.3lf W\n", processIndex, processCount, m.elapsedSeconds, m.powerConsumption);
    }

    if (m.elapsedSeconds < c->minWallSecondsPerMeasurement) {
        printf("# %i   %lf s < %.0lf s : less benchmarking time than desired\n", processIndex, m.elapsedSeconds, c->minWallSecondsPerMeasurement);
    }

    return m;
}

/* *** dissemination barrier { ********************************************* */
static void measureDisseminationBarrier(Context *c, Bool autoPrint) {
    if (autoPrint == True) printf("# %i %s:\n", c->processIndex, __func__);

    int repetitions_;

    void prepare(int processIndex, int processCount) {(void) processIndex; (void) processCount;}
    void finalize(int processIndex, int processCount) {(void) processIndex; (void) processCount;}
    void f(int processIndex, int processCount) {
        (void) processIndex;
        (void) processCount;

        struct timespec begin, end;

        clock_gettime(CLOCK_REALTIME, &begin);
        const time_t supposedEnd = begin.tv_sec + c->minWallSecondsPerMeasurement;

        for(int64_t repetitions = 0;; repetitions += 1) {

            MPI_Barrier(MPI_COMM_WORLD);

            if (repetitions % 10000 == 0) {

                // if supposedEnd is not reached , continue measurements
                if (processIndex == 0) {
                    clock_gettime(CLOCK_REALTIME, &end);
                    if (end.tv_sec > supposedEnd) {
                        Bool b = False;
                        MPI_Bcast(&b, 1, MPI_INT, 0, MPI_COMM_WORLD);
                        repetitions_ = repetitions;
                        break;
                    } else {
                        Bool b = True;
                        MPI_Bcast(&b, 1, MPI_INT, 0, MPI_COMM_WORLD);
                    }
                } else {
                    Bool b;
                    MPI_Bcast(&b, 1, MPI_INT, 0, MPI_COMM_WORLD);
                    if (b == False) {
                        repetitions_ = repetitions;
                        break;
                    }
                }
            }
        }
    }


    MeasurementResult m = measurePowerConsumptionOfFunction(prepare, f, finalize, c, autoPrint);

    double totalCycles = m.elapsedSeconds * 1000 * 1000 * 1000 * c->clockTicksPerNanoSecond;
    double cyclesPerRepetition = totalCycles / repetitions_;
    double joule = m.powerConsumption * m.elapsedSeconds;
    double nanoJoulePerRepetition = joule * 1000 * 1000 * 1000 / repetitions_;

    printf0("%i dissemination t %3d, reps %10lli, wallSecs %.3lf sec, totalPower %3.3lf W, cycles/reps %.3lf, nJ/reps %.3lf\n", c->processIndex, c->processCount, (long long int)repetitions_, m.elapsedSeconds, m.powerConsumption, cyclesPerRepetition, nanoJoulePerRepetition);
}
/* *** } dissemination barrier ********************************************* */


int main(int argc, char **args) {

    MPI_Init(&argc, &args);

    if (argc < 2) {
        printf0(
            "  mpirun -np <n> ./distributed <min-wall-seconds-per-measurement> [options]>\n"
            "\n"
            "    --ghz <Ghz>           set processor clock, for correct cycle times in measurements (default: 1.0)\n"
            "\n"
            "    --dissemination       measure dissemination barrier using <n> processes\n"
            );

        exit(0);
    }

    int processCount; MPI_Comm_size(MPI_COMM_WORLD, &processCount);
    int minWallSecondsPerMeasurement = atoll(args[1]);
    double clockTicksPerNanoSecond = 1.0;

    Bool measureDisseminationBarrier_ = False;

    for (int i = 2; i < argc; i += 1) {
        if (strcmp("--ghz", args[i]) == 0) {
            assert(i + 1 < argc);
            clockTicksPerNanoSecond = atof(args[i+1]);
            i += 1;
        } else if (strcmp("--dissemination", args[i]) == 0) {
            measureDisseminationBarrier_ = True;
        } else {
            printf0("unknown argument: \"%s\"\n", args[i]);
            exit(-1);
        }
    }

    assert(processCount > 1);
    assert(minWallSecondsPerMeasurement > 0);
    assert(clockTicksPerNanoSecond > 0.0);

    Context *context = newContext(minWallSecondsPerMeasurement, clockTicksPerNanoSecond);

    if (measureDisseminationBarrier_ == True) {
        measureDisseminationBarrier(context, True);
    }

    printContext(context);

    freeContext(context);

    MPI_Finalize();

    return 0;
}

