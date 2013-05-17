#! /usr/bin/env bash

#set -x

maxthreads=64
baserepetitions=100000 #repetition count on max threads
scale=1024 #aids calculating since no floating point

for barrier in ./add-fetch ./ronny
do
	for sleepMicroSeconds in 0 1 100
	do
		if [ $sleepMicroSeconds = 0 ]
		then
			divideby=1
		elif [ $sleepMicroSeconds = 1 ]
		then
			divideby=10
		elif [ $sleepMicroSeconds = 100 ]
		then
			divideby=30
		fi

		for threadCount in 2 4 8 16 24 32 48 64
		do
			repetitions=$(expr \( $scale \* $maxthreads / $threadCount \* $baserepetitions / $divideby \) / $scale)

			$barrier $threadCount $repetitions $sleepMicroSeconds
		done

		echo ""
	done
done

