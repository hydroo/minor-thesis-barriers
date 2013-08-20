#define threadCount 3
#define threadCountSquared 9

int bar[threadCountSquared];

init {
    int i = 0;
    do :: i < threadCountSquared -> bar[i] = 0; i = i + 1;
       :: else -> break
    od;

    i = 0;
    do :: i < threadCount -> i = i + 1; run p(i-1);
    od
}


// inserted the loop twice to be able to distinguish between work period one and two.
// if I would not do this. I dont know how to properly check for correctness

proctype p(int threadIndex) {
    int distance;
    int to;
    int from;
    int rep;

    do ::

       one:

       rep = bar[threadCount*threadIndex+threadIndex] + 1;
       bar[threadCount*threadIndex+threadIndex] = rep;

       distance = 1;
       do :: distance < threadCount -> to   = (threadIndex + distance              ) % threadCount;
                                       from = (threadIndex - distance + threadCount) % threadCount;

                                       bar[threadCount*to+threadIndex] = rep; // manual index calculation [to][threadIndex]

                                       if :: bar[threadCount*threadIndex+from] == rep // same as "while (!cond) {}"
                                       fi;

                                       distance = distance * 2;
          :: else -> break
       od;

       two:

       rep = bar[threadCount*threadIndex+threadIndex] + 1;
       bar[threadCount*threadIndex+threadIndex] = rep;

       distance = 1;
       do :: distance < threadCount -> to   = (threadIndex + distance              ) % threadCount;
                                       from = (threadIndex - distance + threadCount) % threadCount;

                                       bar[threadCount*to+threadIndex] = rep; // manual index calculation [to][threadIndex]

                                       if :: bar[threadCount*threadIndex+from] == rep // same as "while (!cond) {}"
                                       fi;

                                       distance = distance * 2;
          :: else -> break
       od;
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

//ltl alive {<>(rep[0] == 1000) && <>(rep[1] == 1000) && <>(rep[2] == 1000)}
