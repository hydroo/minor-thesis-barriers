#!/bin/bash
#BSUB -x
#BSUB -J "venus-128-1"
#BSUB -q short
#BSUB -W 2:00
#BSUB -R "span[hosts=1]"
#BSUB -n 128
#BSUB -o out.%J
#BSUB -e err.%J
#BSUB -u ronny.brendel@tu-dresden.de

taskset -p $$

./benchmark.sh

