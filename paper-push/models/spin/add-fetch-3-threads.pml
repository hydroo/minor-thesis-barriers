#define threadCount 3

int bar1 = threadCount;
int bar2 = threadCount;
int bar3 = threadCount;

init {
    int i = 0;

    do
        :: i < threadCount -> i = i + 1; run p();
    od
}

proctype p() {

    do
        ::

        atomic{bar1 = bar1 - 1;} //would be atomic without the statement as well
        do
            :: bar1 == 0 -> break
        od;
        bar3 = threadCount;

        one:

        atomic{bar2 = bar2 - 1;}
        do
            :: bar2 == 0 -> break
        od;
        bar1 = threadCount;

        two:

        atomic{bar3 = bar3 - 1;}
        do
            :: bar3 == 0 -> break
        od;
        bar2 = threadCount;

        three:
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

