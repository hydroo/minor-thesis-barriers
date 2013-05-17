#define bits 3

// one bit per element in the array
bit entry[bits];
bit exit[bits];
bit full_[bits];
bool left = false;

init {

    // initialize full, entry, exit
    int i = 0;
    do
    :: i < bits -> full_[i] = 1; entry[i] = 0; exit[i] = 0; i = i + 1;
    :: else -> break;
    od;

    // start processes
    i = 0;
    do
    :: i < bits -> run p(i); i = i + 1;
    :: else -> break;
    od
}

proctype p(int index) {

    bit copy[bits];
    int i = 0;
    bool isFull = 0;

    do
        ::

        if
        :: left == false ->

            do
                ::

                // copy = (copy &~me)|entry
                copy[index] = 0;
                i = 0;
                do
                    :: i < bits -> copy[i] = copy[i] | entry[i]; i = i + 1;
                    :: else -> break;
                od;

                // if copy&me == 0 { entry = copy = copy|me }
                if
                    :: (copy[index] == 0) -> copy[index] = 1; entry[index] = copy[index];
                    :: else -> skip
                fi;

                // while(copy !=full && left==false)
                isFull = 1;
                i = 0;
                do
                    :: i < bits ->
                        if
                            :: copy[i] == full_[i] -> i = i + 1; skip
                            :: else isFull = 0; break
                        fi
                    :: else -> break
                od;

                if
                    :: isFull == 0 && left == false -> skip
                    :: else -> break
                fi
            od;

            between:

            left = true;
            // set exit = copy = 0
            i = 0;
            do
                :: i < bits -> exit[i] = 0; copy[i] = 0; i = i + 1;
                :: else -> break;
            od;

        :: left == true ->

            do
                ::

                copy[index] = 0;
                i = 0;
                do
                    :: i < bits -> copy[i] = copy[i] | exit[i]; i = i + 1;
                    :: else -> break;
                od;

                if
                    :: (copy[index] == 0) -> copy[index] = 1; exit[index] = copy[index];
                    :: else -> skip
                fi;

                isFull = 1;
                i = 0;
                do
                    :: i < bits ->
                        if
                            :: copy[i] == full_[i] -> i = i + 1; skip
                            :: else isFull = 0;break
                        fi
                    :: else -> break
                od;

                if
                    :: isFull == 0 && left == true -> skip
                    :: else -> break
                fi
            od;

            left = false;
            i = 0;
            do
                :: i < bits -> entry[i] = 0; copy[i] = 0; i = i + 1;
                :: else -> break;
            od;

            progress:

        fi
    od
}


ltl liveness_0 {([]<>(left==true)) && ([]<>(left==false))}
//ltl consistency_0 {[](!(p[1]@between && p[2]@progress))}

