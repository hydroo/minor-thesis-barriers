int entry = 0;
int exit = 0;
bool left = false;

init {
	run p(1, 7);
	run p(2, 7);
	run p(4, 7);
}

proctype p(int me, full_) {

    int copy = 0;

    do
        ::

        if
        :: left == false ->

            do
            :: copy = (copy&(~me)) | entry;
               if
               :: ((copy & me) == 0) -> copy = copy + me; entry = copy
               :: else -> skip
               fi;
               if
               :: !(copy != full_ && left == false) -> break
               :: else -> skip
               fi
            od;

            between:

            left = true;
            exit = 0;
            copy = 0;

        :: left == true ->

            do
            :: copy = (copy&(~me)) | exit;
               if
               :: ((copy & me) == 0) -> copy = copy + me; exit = copy
               :: else -> skip
               fi;
               if
               :: !(copy != full_ && left == true) -> break
               :: else -> skip
               fi
            od;

            left = false;
            entry = 0;
            copy = 0;

            progress:

        fi
    od
}


ltl liveness_0 {([]<>(left==true)) && ([]<>(left==false))}
//ltl consistency_0 {[](!(p[1]@between && p[2]@progress))}

