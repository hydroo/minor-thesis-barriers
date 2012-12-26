#! /usr/bin/env bash

CORE_COUNT=4

REPETITIONS=1000000

SHORTRUNAWAYSCYCLES=0
LONGRUNAWAYSCYCLES=1000

# warm up
./cache-test $CORE_COUNT $(($CORE_COUNT - 1)) $REPETITIONS > /dev/null

for invalid in $(seq 1 $CORE_COUNT)
do
	for threads in $(seq $(($invalid+1)) $CORE_COUNT)
	do
		./cache-test $threads $invalid $REPETITIONS $SHORTRUNAWAYSCYCLES $LONGRUNAWAYSCYCLES
	done
	echo ""
done

