#!/bin/bash
#SBATCH -p smp
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --tasks-per-node=1
#SBATCH --cpus-per-task=32
#SBATCH --mail-type=end
#SBATCH --mail-user=ronny.brendel@tu-dresden.de
#SBATCH --time=04:00:00

srun --cpu-freq 2600000 ./benchmark.sh
