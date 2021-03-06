#define threadCount 3

int bar[threadCount];

init {
    int i = 0;
    do :: i < threadCount-> bar[i] = 0; i = i + 1;
       :: else -> break
    od;

    i = 0;
    do :: i < threadCount -> i = i + 1; run p(i-1);
    od
}


// inserted the loop twice to be able to distinguish between work period one and two.
// if I would not do this. I dont know how to properly check for correctness

proctype p(int threadIndex) {
    int i;
    int rep;

    do ::

       one:

       rep = bar[threadIndex] + 1;
       bar[threadIndex] = rep;

       i = 0;
       do :: i < threadCount -> if :: bar[i] < rep -> i = 0
                                   :: else -> i = i + 1
                                fi
          :: else -> break
       od;

       two:

       rep = bar[threadIndex] + 1;
       bar[threadIndex] = rep;

       i = 0;
       do :: i < threadCount -> if :: bar[i] < rep -> i = 0
                                   :: else -> i = i + 1
                                fi
          :: else -> break
       od

    od
}

ltl correct1 {[]((p[1]@one   -> !(p[2]@two || p[3]@two)) &&
                 (p[1]@two   -> !(p[2]@one || p[3]@one)))}
ltl correct2 {[]((p[2]@one   -> !(p[1]@two || p[3]@two)) &&
                 (p[2]@two   -> !(p[1]@one || p[3]@one)))}
ltl correct3 {[]((p[3]@one   -> !(p[1]@two || p[2]@two)) &&
                 (p[3]@two   -> !(p[1]@one || p[2]@one)))}

ltl alive1 {([]<>p[1]@one) && ([]<>p[1]@two)}
ltl alive2 {([]<>p[2]@one) && ([]<>p[2]@two)}
ltl alive3 {([]<>p[3]@one) && ([]<>p[3]@two)}

//ltl alive {<>(bar[0] == 1000) && <>(bar[1] == 1000) && <>(bar[2] == 1000)}

