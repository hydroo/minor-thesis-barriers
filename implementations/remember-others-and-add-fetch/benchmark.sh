#! /usr/bin/env bash

# bsub -x -q short -n 64 -oo out -eo error -R "span[hosts=1]" ./benchmark.sh

#set -x

clockTicksPerNanoSecond=2.2 #atlas
#clockTicksPerNanoSecond=2.6 #taurus
#clockTicksPerNanoSecond=2.5 #vt
secondsPerBenchmark=2
scale=1024 #aids calculating since no floating point

for barrier in ./add-fetch ./ronny
do
	for sleepMicroSeconds in 0 1 100
	do
		for threadCount in 2 4 8 16 24 32 48 64
#		for threadCount in 2 3 4 5 6 7 8 12 16 20 24 28 32 36 40 44 48 52 56 60 64
#		for threadCount in 2 3 4 5 6 7 8 10 12 14 16 18 20 22 24 26 28 30 32
		do
			$barrier $threadCount $secondsPerBenchmark $clockTicksPerNanoSecond $sleepMicroSeconds
		done

		echo ""
	done
done

