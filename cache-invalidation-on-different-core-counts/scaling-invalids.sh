#! /usr/bin/env bash

CORE_COUNT=4

REPETITIONS=100000

# warm up
./cache-test $CORE_COUNT $(($CORE_COUNT - 1)) $REPETITIONS > /dev/null

for invalid in $(seq 1 $(($CORE_COUNT-1)))
do
	./cache-test $(($invalid+1)) $invalid $REPETITIONS
done

