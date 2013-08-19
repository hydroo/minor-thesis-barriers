#define threadCount 3
#define threadCountSquared 9

int bar[threadCountSquared];
int rep[threadCount];

init {
    int i = 0;
    do
        :: i < threadCountSquared -> bar[i] = 0; i = i + 1;
        :: else -> break
    od;

    i = 0;
    do
        :: i < threadCount -> rep[i] = 0; i = i + 1;
        :: else -> break
    od;

    i = 0;
    do
        :: i < threadCount -> i = i + 1; run p(i-1);
    od
}

proctype p(int threadIndex) {
    int distance;
    int to;
    int from;

    do ::
       rep[threadIndex] = rep[threadIndex] + 1;

       distance = 1;
       do :: distance < threadCount -> to   = (threadIndex + distance              ) % threadCount;
                                       from = (threadIndex - distance + threadCount) % threadCount;

                                       bar[threadCount*to+threadIndex] = rep[threadIndex];

                                       if
                                           :: bar[threadCount*threadIndex+from] >= rep[threadIndex] // same as "while (!cond) {}"
                                       fi;

                                       distance = distance * 2;
          :: else -> break
       od;
    od
}

ltl correct {[]((rep[0] == rep[1] || rep[0] == rep[1]+1 || rep[0] == rep[1]-1) &&
                (rep[0] == rep[2] || rep[0] == rep[2]+1 || rep[0] == rep[2]-1) &&
                (rep[1] == rep[2] || rep[1] == rep[2]+1 || rep[1] == rep[2]-1))}

ltl alive {<>(rep[0] == 1000) && <>(rep[1] == 1000) && <>(rep[2] == 1000)}

