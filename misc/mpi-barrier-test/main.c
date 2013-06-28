// mpirun -np 2 xterm -e gdb ./mpi-barrier-test

#include<mpi.h>


int main(int argc, char **args) {

    MPI_Init(&argc, &args);

    MPI_Barrier(MPI_COMM_WORLD);

    MPI_Finalize();

    return 0;
}

