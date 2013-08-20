#define threadCount 3
#define full        7 //1+2+4
#define empty       0

int bar1[threadCount];
int bar2[threadCount];
int bar3[threadCount];

init {
    int i = 0;
    do :: i < threadCount-> bar1[i] = full; bar2[i] = full; bar3[i] = empty; i = i + 1;
       :: else -> break
    od;

    i = 0;
    do :: i < threadCount -> i = i + 1; run p(i-1);
    od
}


proctype p(int threadIndex) {
    int i;
    int me = 1<<threadIndex;

    do ::

       if :: bar3[threadIndex] == empty ->

             bar1[threadIndex] = full & ~me;
             i = 0;
             do :: bar1[threadIndex] != empty ->
                   do :: i < threadCount ->
                         if :: (bar1[threadIndex]&(1<<i)) != 0 -> break
                            :: else -> i = i + 1
                         fi
                      :: else -> break
                   od;

                   if :: i < threadCount -> bar1[threadIndex] = bar1[threadIndex] & bar1[i]
                      :: else -> i = 0
                   fi
                :: else -> break
             od;
             bar3[threadIndex] = full;

             one:

          :: bar1[threadIndex] == empty ->

             bar2[threadIndex] = full & ~me;
             i = 0;
             do :: bar2[threadIndex] != empty ->
                   do :: i < threadCount ->
                         if :: (bar2[threadIndex]&(1<<i)) != 0 -> break
                            :: else -> i = i + 1
                         fi
                      :: else -> break
                   od;

                   if :: i < threadCount -> bar2[threadIndex] = bar2[threadIndex] & bar2[i]
                      :: else -> i = 0
                   fi
                :: else -> break
             od;
             bar1[threadIndex] = full;

             two:

          :: bar2[threadIndex] == empty ->

             bar3[threadIndex] = full & ~me;
             i = 0;
             do :: bar3[threadIndex] != empty ->
                   do :: i < threadCount ->
                         if :: (bar3[threadIndex]&(1<<i)) != 0 -> break
                            :: else -> i = i + 1
                         fi
                      :: else -> break
                   od;

                   if :: i < threadCount -> bar3[threadIndex] = bar3[threadIndex] & bar3[i]
                      :: else -> i = 0
                   fi
                :: else -> break
             od;
             bar2[threadIndex] = full;

             three:
        fi

    od
}

ltl correct1 {[]((p[1]@one   -> !(p[2]@two || p[2]@three || p[3]@two || p[3]@three)) &&
                 (p[1]@two   -> !(p[2]@one || p[2]@three || p[3]@one || p[3]@three)) &&
                 (p[1]@three -> !(p[2]@two || p[2]@one   || p[3]@two || p[3]@one)))}

ltl correct2 {[]((p[2]@one   -> !(p[1]@two || p[1]@three || p[3]@two || p[3]@three)) &&
                 (p[2]@two   -> !(p[1]@one || p[1]@three || p[3]@one || p[3]@three)) &&
                 (p[2]@three -> !(p[1]@two || p[1]@one   || p[3]@two || p[3]@one)))}

ltl correct3 {[]((p[3]@one   -> !(p[1]@two || p[1]@three || p[2]@two || p[2]@three)) &&
                 (p[3]@two   -> !(p[1]@one || p[1]@three || p[2]@one || p[2]@three)) &&
                 (p[3]@three -> !(p[1]@two || p[1]@one   || p[2]@two || p[2]@one)))}

ltl alive1 {([]<>p[1]@one) && ([]<>p[1]@two) && ([]<>p[1]@three)}
ltl alive2 {([]<>p[2]@one) && ([]<>p[2]@two) && ([]<>p[2]@three)}
ltl alive3 {([]<>p[3]@one) && ([]<>p[3]@two) && ([]<>p[3]@three)}

