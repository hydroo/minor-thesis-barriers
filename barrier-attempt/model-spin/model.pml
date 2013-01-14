int entry = 0;
int exit = 0;
bool left = false;

active proctype p1() {

    int copy = 0;

    do
        ::

        do
        :: copy = entry;
           if
           :: ((copy & 1) == 0) -> copy = copy + 1; entry = copy
           :: else -> skip
           fi;
           if
           :: !(copy != 7 && left == 0) -> break
           :: else -> skip
           fi
        od;

        between:

        left = true;
        exit = 0;

        do
        :: copy = exit;
           if
           :: ((copy & 1) == 0) -> copy = copy + 1; exit = copy
           :: else -> skip
           fi;
           if
           :: !(copy != 7 && left == 1) -> break
           :: else -> skip
           fi
        od;

        left = false;
        entry = 0;

        progress:
    od
}


active proctype p2() {

    int copy = 0;

    do
        ::

        do
        :: copy = entry;
           if
           :: ((copy & 2) == 0) -> copy = copy + 2; entry = copy
           :: else -> skip
           fi;
           if
           :: !(copy != 7 && left == 0) -> break
           :: else -> skip
           fi
        od;

        between:

        left = true;
        exit = 0;

        do
        :: copy = exit;
           if
           :: ((copy & 2) == 0) -> copy = copy + 2; exit = copy
           :: else -> skip
           fi;
           if
           :: !(copy != 7 && left == 1) -> break
           :: else -> skip
           fi
        od;

        left = false;
        entry = 0;

        progress:
    od
}


active proctype p3() {

    int copy = 0;

    do
        ::

        do
        :: copy = entry;
           if
           :: ((copy & 4) == 0) -> copy = copy + 4; entry = copy
           :: else -> skip
           fi;
           if
           :: !(copy != 7 && left == 0) -> break
           :: else -> skip
           fi
        od;

        between:

        left = true;
        exit = 0;

        do
        :: copy = exit;
           if
           :: ((copy & 4) == 0) -> copy = copy + 4; exit = copy
           :: else -> skip
           fi;
           if
           :: !(copy != 7 && left == 1) -> break
           :: else -> skip
           fi
        od;

        left = false;
        entry = 0;

        progress:
    od
}

//ltl never_01 {[](!(p1@between && p2@progress))}

//ltl prop0 {[]<>((left==true) && X (left==false))}
//ltl prop1 {[]<>(left==true) && []<>(left==false)}
//ltl prop_wrong {<>(left==true)}

