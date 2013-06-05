#! /usr/bin/env bash

# bsub -x -q short -n 64 -oo out -eo error -R "span[hosts=1]" ./benchmark.sh

#set -x

secondsPerBenchmark=2
scale=1024 #aids calculating since no floating point

for barrier in ./add-fetch ./ronny
do
	for sleepMicroSeconds in 0 1 100
	do
		for threadCount in 2 4 8 16 24 32 48 64
		do
			$barrier $threadCount $secondsPerBenchmark $sleepMicroSeconds
		done

		echo ""
	done
done

