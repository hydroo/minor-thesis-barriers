// different barriers are need in order to make the resetting of the barrier variable(s) safe!

int threadCount = 3;

int barrier1 = threadCount;
int barrier2 = threadCount;
int barrier3 = threadCount;

init {

    int i = 0;

    do
        :: i < threadCount -> i = i + 1; run p();
        :: else -> skip
    od
}

proctype p() {

    do
        ::

        atomic{barrier1 = barrier1 - 1;} //would be atomic without the statement as well
        do
            :: barrier1 == 0 -> break
        od;
        barrier3 = threadCount;

        between12:

        atomic{barrier2 = barrier2 - 1;}
        do
            :: barrier2 == 0 -> break
        od;
        barrier1 = threadCount;

        between23:

        atomic{barrier3 = barrier3 - 1;}
        do
            :: barrier3 == 0 -> break
        od;
        barrier2 = threadCount;

        between31:

    od
}


ltl correct1 {[]((p[1]@between12 -> !(p[2]@between23||p[2]@between31||p[3]@between23||p[3]@between31)) &&
                 (p[1]@between23 -> !(p[2]@between12||p[2]@between31||p[3]@between12||p[3]@between31)) &&
                 (p[1]@between31 -> !(p[2]@between23||p[2]@between12||p[3]@between23||p[3]@between12)))}

ltl correct2 {[]((p[2]@between12 -> !(p[1]@between23||p[1]@between31||p[3]@between23||p[3]@between31)) &&
                 (p[2]@between23 -> !(p[1]@between12||p[1]@between31||p[3]@between12||p[3]@between31)) &&
                 (p[2]@between31 -> !(p[1]@between23||p[1]@between12||p[3]@between23||p[3]@between12)))}

ltl correct3 {[]((p[3]@between12 -> !(p[1]@between23||p[1]@between31||p[2]@between23||p[2]@between31)) &&
                 (p[3]@between23 -> !(p[1]@between12||p[1]@between31||p[2]@between12||p[2]@between31)) &&
                 (p[3]@between31 -> !(p[1]@between23||p[1]@between12||p[2]@between23||p[2]@between12)))}

ltl alive1 {([]<>p[1]@between12) && ([]<>p[1]@between23) && ([]<>p[1]@between31)}
ltl alive2 {([]<>p[2]@between12) && ([]<>p[2]@between23) && ([]<>p[2]@between31)}
ltl alive3 {([]<>p[3]@between12) && ([]<>p[3]@between23) && ([]<>p[3]@between31)}

