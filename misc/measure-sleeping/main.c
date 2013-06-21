#define _GNU_SOURCE
#include <assert.h>
#include <float.h>
#include <limits.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>


static void setThreadAffinity(int threadIndex) {
    cpu_set_t cpuset;
    CPU_ZERO(&cpuset);
    CPU_SET(threadIndex % sysconf(_SC_NPROCESSORS_ONLN), &cpuset);
    assert(pthread_setaffinity_np(pthread_self(), sizeof(cpu_set_t), &cpuset) == 0);
}


static double measureClockGetTime() {
    struct timespec begin, end;
    clock_gettime(CLOCK_REALTIME, &begin);
    clock_gettime(CLOCK_REALTIME, &end);
    return ((end.tv_sec * 1000000000 + end.tv_nsec) - (begin.tv_sec * 1000000000 + begin.tv_nsec));
}

static double measureUsleep(int microSeconds) {
    struct timespec begin, end;
    clock_gettime(CLOCK_REALTIME, &begin);
    usleep((useconds_t)microSeconds);
    clock_gettime(CLOCK_REALTIME, &end);
    return ((end.tv_sec * 1000000 + end.tv_nsec / 1000.0) - (begin.tv_sec * 1000000 + begin.tv_nsec / 1000.0));
}

static double measureNanoSleep(int microSeconds) {
    struct timespec sleepTime;
    sleepTime.tv_sec = microSeconds / 1000000;
    sleepTime.tv_nsec = microSeconds * 1000;
    struct timespec begin, end;
    clock_gettime(CLOCK_REALTIME, &begin);
    nanosleep(&sleepTime, NULL);
    clock_gettime(CLOCK_REALTIME, &end);
    return ((end.tv_sec * 1000000 + end.tv_nsec / 1000.0) - (begin.tv_sec * 1000000 + begin.tv_nsec / 1000.0));
}


int main(int argc, char **args) {

    if (argc < 2) {
        printf(
            "  measure-sleeping [options]\n"
            "\n"
            "    --clock-get-time  measure timing overhead\n"
            "    --usleep\n"
            "    --nanosleep\n"
            );

        exit(0);
    }

    int measureClockGetTime_ = 0;
    int measureUsleep_ = 0;
    int measureNanoSleep_ = 0;

    for (int i = 1; i < argc; i += 1) {
        if (strcmp("--clock-get-time", args[i]) == 0) {
            assert(measureUsleep_ == 0 && measureNanoSleep_ == 0);
            measureClockGetTime_ = 1;
        } else if (strcmp("--usleep", args[i]) == 0) {
            assert(measureClockGetTime_ == 0 && measureNanoSleep_ == 0);
            measureUsleep_ = 1;
        } else if (strcmp("--nano-sleep", args[i]) == 0) {
            assert(measureClockGetTime_ == 0 && measureUsleep_ == 0);
            measureNanoSleep_ = 1;
        } else {
            printf("unknown argument: \"%s\"\n", args[i]);
            exit(-1);
        }
    }

    setThreadAffinity(0);

    if (measureClockGetTime_ == 1) {
        double min = DBL_MAX;
        double max = 0.0;
        double mean = 0.0;
        const int iterationCount = 10 * 1000 * 1000;

        for (int i = 0; i < 10000000; i += 1) {
            double measured = measureClockGetTime();

            if (measured < min) min = measured;
            if (measured > max) max = measured;
            mean += measured;
        }
        mean /= iterationCount;

        struct timespec res_;
        clock_getres(CLOCK_REALTIME, &res_);
        double res = res_.tv_sec * 1000000000 + res_.tv_nsec;

        printf("clock-get-time res: %lf nanosecs, min: %.3lf, max: %.3lf, mean: %.3lf\n", res, min, max, mean);
    } else if (measureUsleep_ == 1) {
        for (double supposed = 1.0;; supposed += 1.0) {
            double measured = measureUsleep((int) supposed);
            printf("usleep supposed mysecs: %6.0lf, measured: %6.3lf, diff: %6.3lf\n", supposed, measured, measured - supposed);
        }
    } else if (measureNanoSleep_ == 1) {
        for (double supposed = 1.0;; supposed += 1.0) {
            double measured = measureNanoSleep((int) supposed);
            printf("nanosleep supposed mysecs: %6.0lf, measured: %6.3lf, diff: %6.3lf\n", supposed, measured, measured - supposed);
        }
    } else {
        assert(0);
    }



    return 0;
}
