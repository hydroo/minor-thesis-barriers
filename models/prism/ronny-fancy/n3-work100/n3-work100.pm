ctmc

const process_count = 3;

const int me_0 = 0;
const int me_1 = 1;
const int me_2 = 2;

const int me_bit_0 = 1;
const int me_bit_1 = 2;
const int me_bit_2 = 4;

const int empty = 0;
const int full  = me_bit_0 + me_bit_1 + me_bit_2 + 0;

const work_ticks  = 100;
const read_ticks  = 1;
const write_ticks = 1;
const get_ticks   = 100;
const put_ticks   = 100;

// rates
const double base_rate = 1000.0;
const double tick      = base_rate / 1.0;
const double work      = tick / work_ticks;
const double read      = tick / read_ticks;
const double write     = tick / write_ticks;
const double get       = tick / get_ticks;
const double put       = tick / put_ticks;

// process locations
// all names describe the behaviour of the next transition
const l_init   = 0;
const l_work   = l_init;
const l_write  = 1;
const l_search = 2;
const l_test   = 3;
const l_done   = 4;

// *** main process begin ***

// * last _# at labels and variables is always the id of the "owning" process //

// * no label is for sync. all are for easyier debugging in the simulator

// * changing read and write rates does not work anymore because we collapsed some of those transitions (optimization)

module process_0
    l_0   : [l_init..l_done]     init l_init;
    bar_0 : [0..full]            init 0;
    i_0   : [0..process_count-1] init me_0;

    [work_0]     l_0=l_work  -> work  : (l_0'=l_write);

    [write_0]    l_0=l_write -> write : (l_0'=l_search) & (bar_0'=me_bit_0);

    // bar_0 = bar_0 | bar_x. all combinations for all i's
    // emulates a foot controlled loop by clevery using +1 and i increment
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 1                        ->  read  : (l_0'=l_search) & (i_0'=mod(i_0+1, process_count));
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 0 & bar_1= 0  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=0);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 0 & bar_1= 1  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=1);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 0 & bar_1= 2  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=2);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 0 & bar_1= 3  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=3);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 0 & bar_1= 4  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=4);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 0 & bar_1= 5  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=5);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 0 & bar_1= 6  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=6);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 0 & bar_1= 7  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 1 & bar_1= 0  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=1);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 1 & bar_1= 1  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=1);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 1 & bar_1= 2  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=3);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 1 & bar_1= 3  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=3);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 1 & bar_1= 4  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=5);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 1 & bar_1= 5  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=5);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 1 & bar_1= 6  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 1 & bar_1= 7  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 2 & bar_1= 0  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=2);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 2 & bar_1= 1  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=3);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 2 & bar_1= 2  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=2);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 2 & bar_1= 3  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=3);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 2 & bar_1= 4  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=6);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 2 & bar_1= 5  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 2 & bar_1= 6  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=6);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 2 & bar_1= 7  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 3 & bar_1= 0  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=3);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 3 & bar_1= 1  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=3);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 3 & bar_1= 2  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=3);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 3 & bar_1= 3  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=3);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 3 & bar_1= 4  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 3 & bar_1= 5  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 3 & bar_1= 6  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 3 & bar_1= 7  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 4 & bar_1= 0  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=4);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 4 & bar_1= 1  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=5);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 4 & bar_1= 2  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=6);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 4 & bar_1= 3  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 4 & bar_1= 4  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=4);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 4 & bar_1= 5  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=5);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 4 & bar_1= 6  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=6);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 4 & bar_1= 7  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 5 & bar_1= 0  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=5);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 5 & bar_1= 1  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=5);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 5 & bar_1= 2  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 5 & bar_1= 3  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 5 & bar_1= 4  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=5);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 5 & bar_1= 5  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=5);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 5 & bar_1= 6  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 5 & bar_1= 7  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 6 & bar_1= 0  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=6);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 6 & bar_1= 1  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 6 & bar_1= 2  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=6);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 6 & bar_1= 3  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 6 & bar_1= 4  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=6);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 6 & bar_1= 5  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 6 & bar_1= 6  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=6);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 6 & bar_1= 7  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 7 & bar_1= 0  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 7 & bar_1= 1  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 7 & bar_1= 2  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 7 & bar_1= 3  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 7 & bar_1= 4  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 7 & bar_1= 5  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 7 & bar_1= 6  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=0 & mod(floor(bar_0/me_bit_1),2) = 0 & bar_0= 7 & bar_1= 7  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 1                        ->  read  : (l_0'=l_search) & (i_0'=mod(i_0+1, process_count));
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 0 & bar_2= 0  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=0);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 0 & bar_2= 1  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=1);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 0 & bar_2= 2  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=2);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 0 & bar_2= 3  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=3);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 0 & bar_2= 4  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=4);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 0 & bar_2= 5  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=5);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 0 & bar_2= 6  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=6);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 0 & bar_2= 7  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 1 & bar_2= 0  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=1);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 1 & bar_2= 1  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=1);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 1 & bar_2= 2  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=3);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 1 & bar_2= 3  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=3);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 1 & bar_2= 4  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=5);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 1 & bar_2= 5  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=5);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 1 & bar_2= 6  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 1 & bar_2= 7  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 2 & bar_2= 0  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=2);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 2 & bar_2= 1  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=3);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 2 & bar_2= 2  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=2);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 2 & bar_2= 3  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=3);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 2 & bar_2= 4  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=6);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 2 & bar_2= 5  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 2 & bar_2= 6  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=6);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 2 & bar_2= 7  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 3 & bar_2= 0  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=3);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 3 & bar_2= 1  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=3);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 3 & bar_2= 2  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=3);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 3 & bar_2= 3  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=3);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 3 & bar_2= 4  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 3 & bar_2= 5  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 3 & bar_2= 6  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 3 & bar_2= 7  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 4 & bar_2= 0  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=4);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 4 & bar_2= 1  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=5);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 4 & bar_2= 2  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=6);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 4 & bar_2= 3  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 4 & bar_2= 4  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=4);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 4 & bar_2= 5  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=5);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 4 & bar_2= 6  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=6);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 4 & bar_2= 7  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 5 & bar_2= 0  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=5);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 5 & bar_2= 1  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=5);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 5 & bar_2= 2  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 5 & bar_2= 3  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 5 & bar_2= 4  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=5);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 5 & bar_2= 5  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=5);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 5 & bar_2= 6  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 5 & bar_2= 7  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 6 & bar_2= 0  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=6);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 6 & bar_2= 1  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 6 & bar_2= 2  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=6);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 6 & bar_2= 3  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 6 & bar_2= 4  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=6);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 6 & bar_2= 5  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 6 & bar_2= 6  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=6);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 6 & bar_2= 7  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 7 & bar_2= 0  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 7 & bar_2= 1  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 7 & bar_2= 2  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 7 & bar_2= 3  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 7 & bar_2= 4  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 7 & bar_2= 5  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 7 & bar_2= 6  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=1 & mod(floor(bar_0/me_bit_2),2) = 0 & bar_0= 7 & bar_2= 7  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 1                        ->  read  : (l_0'=l_search) & (i_0'=mod(i_0+1, process_count));
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 0 & bar_0= 0  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=0);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 0 & bar_0= 1  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=1);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 0 & bar_0= 2  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=2);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 0 & bar_0= 3  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=3);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 0 & bar_0= 4  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=4);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 0 & bar_0= 5  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=5);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 0 & bar_0= 6  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=6);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 0 & bar_0= 7  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 1 & bar_0= 0  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=1);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 1 & bar_0= 1  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=1);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 1 & bar_0= 2  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=3);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 1 & bar_0= 3  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=3);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 1 & bar_0= 4  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=5);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 1 & bar_0= 5  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=5);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 1 & bar_0= 6  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 1 & bar_0= 7  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 2 & bar_0= 0  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=2);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 2 & bar_0= 1  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=3);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 2 & bar_0= 2  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=2);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 2 & bar_0= 3  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=3);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 2 & bar_0= 4  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=6);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 2 & bar_0= 5  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 2 & bar_0= 6  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=6);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 2 & bar_0= 7  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 3 & bar_0= 0  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=3);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 3 & bar_0= 1  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=3);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 3 & bar_0= 2  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=3);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 3 & bar_0= 3  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=3);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 3 & bar_0= 4  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 3 & bar_0= 5  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 3 & bar_0= 6  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 3 & bar_0= 7  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 4 & bar_0= 0  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=4);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 4 & bar_0= 1  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=5);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 4 & bar_0= 2  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=6);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 4 & bar_0= 3  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 4 & bar_0= 4  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=4);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 4 & bar_0= 5  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=5);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 4 & bar_0= 6  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=6);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 4 & bar_0= 7  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 5 & bar_0= 0  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=5);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 5 & bar_0= 1  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=5);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 5 & bar_0= 2  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 5 & bar_0= 3  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 5 & bar_0= 4  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=5);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 5 & bar_0= 5  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=5);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 5 & bar_0= 6  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 5 & bar_0= 7  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 6 & bar_0= 0  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=6);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 6 & bar_0= 1  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 6 & bar_0= 2  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=6);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 6 & bar_0= 3  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 6 & bar_0= 4  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=6);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 6 & bar_0= 5  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 6 & bar_0= 6  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=6);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 6 & bar_0= 7  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 7 & bar_0= 0  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 7 & bar_0= 1  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 7 & bar_0= 2  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 7 & bar_0= 3  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 7 & bar_0= 4  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 7 & bar_0= 5  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 7 & bar_0= 6  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);
    [search_0]   l_0=l_search & i_0=2 & mod(floor(bar_0/me_bit_0),2) = 0 & bar_0= 7 & bar_0= 7  ->  get   : (l_0'=l_test)   & (i_0'=mod(i_0+1, process_count)) & (bar_0'=7);

    [test_0]     l_0=l_test   & bar_0 =full -> read : (l_0'=l_done);
    [test_0]     l_0=l_test   & bar_0!=full -> read : (l_0'=l_search);

    [done_0]     l_0=l_done                 ->        true;
endmodule

// *** main process end ***

// *** process labels begin ***

formula one_is_done       = l_0 = l_done | l_1 = l_done | l_2 = l_done;
formula all_are_done      = l_0 = l_done & l_1 = l_done & l_2 = l_done;

formula one_is_working    = l_0 = l_work | l_1 = l_work | l_2 = l_work;
formula all_are_working   = l_0 = l_work & l_1 = l_work & l_2 = l_work;

// *** process labels end ***

// *** process copies begin ***

module process_1
    l_1   : [l_init..l_done]     init l_init;
    bar_1 : [0..full]            init 0;
    i_1   : [0..process_count-1] init me_1;

    [work_1]     l_1=l_work  -> work  : (l_1'=l_write);

    [write_1]    l_1=l_write -> write : (l_1'=l_search) & (bar_1'=me_bit_1);

    // bar_1 = bar_1 | bar_x. all combinations for all i's
    // emulates a foot controlled loop by clevery using +1 and i increment
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 1                        ->  read  : (l_1'=l_search) & (i_1'=mod(i_1+1, process_count));
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 0 & bar_1= 0  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=0);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 0 & bar_1= 1  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=1);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 0 & bar_1= 2  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=2);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 0 & bar_1= 3  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=3);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 0 & bar_1= 4  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=4);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 0 & bar_1= 5  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=5);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 0 & bar_1= 6  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=6);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 0 & bar_1= 7  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 1 & bar_1= 0  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=1);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 1 & bar_1= 1  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=1);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 1 & bar_1= 2  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=3);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 1 & bar_1= 3  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=3);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 1 & bar_1= 4  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=5);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 1 & bar_1= 5  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=5);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 1 & bar_1= 6  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 1 & bar_1= 7  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 2 & bar_1= 0  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=2);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 2 & bar_1= 1  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=3);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 2 & bar_1= 2  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=2);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 2 & bar_1= 3  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=3);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 2 & bar_1= 4  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=6);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 2 & bar_1= 5  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 2 & bar_1= 6  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=6);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 2 & bar_1= 7  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 3 & bar_1= 0  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=3);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 3 & bar_1= 1  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=3);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 3 & bar_1= 2  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=3);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 3 & bar_1= 3  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=3);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 3 & bar_1= 4  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 3 & bar_1= 5  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 3 & bar_1= 6  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 3 & bar_1= 7  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 4 & bar_1= 0  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=4);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 4 & bar_1= 1  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=5);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 4 & bar_1= 2  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=6);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 4 & bar_1= 3  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 4 & bar_1= 4  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=4);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 4 & bar_1= 5  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=5);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 4 & bar_1= 6  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=6);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 4 & bar_1= 7  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 5 & bar_1= 0  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=5);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 5 & bar_1= 1  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=5);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 5 & bar_1= 2  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 5 & bar_1= 3  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 5 & bar_1= 4  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=5);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 5 & bar_1= 5  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=5);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 5 & bar_1= 6  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 5 & bar_1= 7  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 6 & bar_1= 0  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=6);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 6 & bar_1= 1  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 6 & bar_1= 2  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=6);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 6 & bar_1= 3  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 6 & bar_1= 4  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=6);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 6 & bar_1= 5  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 6 & bar_1= 6  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=6);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 6 & bar_1= 7  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 7 & bar_1= 0  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 7 & bar_1= 1  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 7 & bar_1= 2  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 7 & bar_1= 3  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 7 & bar_1= 4  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 7 & bar_1= 5  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 7 & bar_1= 6  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=0 & mod(floor(bar_1/me_bit_1),2) = 0 & bar_1= 7 & bar_1= 7  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 1                        ->  read  : (l_1'=l_search) & (i_1'=mod(i_1+1, process_count));
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 0 & bar_2= 0  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=0);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 0 & bar_2= 1  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=1);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 0 & bar_2= 2  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=2);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 0 & bar_2= 3  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=3);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 0 & bar_2= 4  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=4);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 0 & bar_2= 5  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=5);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 0 & bar_2= 6  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=6);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 0 & bar_2= 7  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 1 & bar_2= 0  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=1);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 1 & bar_2= 1  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=1);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 1 & bar_2= 2  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=3);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 1 & bar_2= 3  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=3);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 1 & bar_2= 4  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=5);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 1 & bar_2= 5  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=5);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 1 & bar_2= 6  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 1 & bar_2= 7  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 2 & bar_2= 0  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=2);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 2 & bar_2= 1  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=3);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 2 & bar_2= 2  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=2);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 2 & bar_2= 3  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=3);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 2 & bar_2= 4  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=6);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 2 & bar_2= 5  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 2 & bar_2= 6  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=6);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 2 & bar_2= 7  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 3 & bar_2= 0  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=3);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 3 & bar_2= 1  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=3);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 3 & bar_2= 2  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=3);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 3 & bar_2= 3  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=3);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 3 & bar_2= 4  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 3 & bar_2= 5  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 3 & bar_2= 6  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 3 & bar_2= 7  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 4 & bar_2= 0  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=4);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 4 & bar_2= 1  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=5);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 4 & bar_2= 2  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=6);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 4 & bar_2= 3  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 4 & bar_2= 4  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=4);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 4 & bar_2= 5  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=5);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 4 & bar_2= 6  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=6);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 4 & bar_2= 7  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 5 & bar_2= 0  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=5);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 5 & bar_2= 1  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=5);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 5 & bar_2= 2  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 5 & bar_2= 3  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 5 & bar_2= 4  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=5);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 5 & bar_2= 5  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=5);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 5 & bar_2= 6  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 5 & bar_2= 7  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 6 & bar_2= 0  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=6);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 6 & bar_2= 1  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 6 & bar_2= 2  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=6);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 6 & bar_2= 3  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 6 & bar_2= 4  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=6);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 6 & bar_2= 5  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 6 & bar_2= 6  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=6);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 6 & bar_2= 7  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 7 & bar_2= 0  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 7 & bar_2= 1  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 7 & bar_2= 2  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 7 & bar_2= 3  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 7 & bar_2= 4  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 7 & bar_2= 5  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 7 & bar_2= 6  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=1 & mod(floor(bar_1/me_bit_2),2) = 0 & bar_1= 7 & bar_2= 7  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 1                        ->  read  : (l_1'=l_search) & (i_1'=mod(i_1+1, process_count));
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 0 & bar_0= 0  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=0);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 0 & bar_0= 1  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=1);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 0 & bar_0= 2  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=2);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 0 & bar_0= 3  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=3);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 0 & bar_0= 4  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=4);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 0 & bar_0= 5  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=5);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 0 & bar_0= 6  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=6);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 0 & bar_0= 7  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 1 & bar_0= 0  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=1);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 1 & bar_0= 1  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=1);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 1 & bar_0= 2  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=3);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 1 & bar_0= 3  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=3);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 1 & bar_0= 4  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=5);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 1 & bar_0= 5  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=5);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 1 & bar_0= 6  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 1 & bar_0= 7  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 2 & bar_0= 0  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=2);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 2 & bar_0= 1  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=3);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 2 & bar_0= 2  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=2);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 2 & bar_0= 3  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=3);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 2 & bar_0= 4  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=6);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 2 & bar_0= 5  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 2 & bar_0= 6  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=6);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 2 & bar_0= 7  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 3 & bar_0= 0  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=3);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 3 & bar_0= 1  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=3);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 3 & bar_0= 2  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=3);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 3 & bar_0= 3  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=3);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 3 & bar_0= 4  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 3 & bar_0= 5  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 3 & bar_0= 6  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 3 & bar_0= 7  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 4 & bar_0= 0  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=4);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 4 & bar_0= 1  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=5);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 4 & bar_0= 2  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=6);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 4 & bar_0= 3  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 4 & bar_0= 4  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=4);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 4 & bar_0= 5  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=5);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 4 & bar_0= 6  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=6);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 4 & bar_0= 7  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 5 & bar_0= 0  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=5);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 5 & bar_0= 1  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=5);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 5 & bar_0= 2  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 5 & bar_0= 3  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 5 & bar_0= 4  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=5);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 5 & bar_0= 5  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=5);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 5 & bar_0= 6  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 5 & bar_0= 7  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 6 & bar_0= 0  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=6);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 6 & bar_0= 1  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 6 & bar_0= 2  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=6);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 6 & bar_0= 3  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 6 & bar_0= 4  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=6);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 6 & bar_0= 5  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 6 & bar_0= 6  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=6);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 6 & bar_0= 7  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 7 & bar_0= 0  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 7 & bar_0= 1  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 7 & bar_0= 2  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 7 & bar_0= 3  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 7 & bar_0= 4  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 7 & bar_0= 5  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 7 & bar_0= 6  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);
    [search_1]   l_1=l_search & i_1=2 & mod(floor(bar_1/me_bit_0),2) = 0 & bar_1= 7 & bar_0= 7  ->  get   : (l_1'=l_test)   & (i_1'=mod(i_1+1, process_count)) & (bar_1'=7);

    [test_1]     l_1=l_test   & bar_1 =full -> read : (l_1'=l_done);
    [test_1]     l_1=l_test   & bar_1!=full -> read : (l_1'=l_search);

    [done_1]     l_1=l_done                 ->        true;
endmodule

module process_2
    l_2   : [l_init..l_done]     init l_init;
    bar_2 : [0..full]            init 0;
    i_2   : [0..process_count-1] init me_2;

    [work_2]     l_2=l_work  -> work  : (l_2'=l_write);

    [write_2]    l_2=l_write -> write : (l_2'=l_search) & (bar_2'=me_bit_2);

    // bar_2 = bar_2 | bar_x. all combinations for all i's
    // emulates a foot controlled loop by clevery using +1 and i increment
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 1                        ->  read  : (l_2'=l_search) & (i_2'=mod(i_2+1, process_count));
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 0 & bar_1= 0  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=0);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 0 & bar_1= 1  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=1);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 0 & bar_1= 2  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=2);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 0 & bar_1= 3  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=3);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 0 & bar_1= 4  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=4);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 0 & bar_1= 5  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=5);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 0 & bar_1= 6  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=6);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 0 & bar_1= 7  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 1 & bar_1= 0  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=1);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 1 & bar_1= 1  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=1);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 1 & bar_1= 2  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=3);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 1 & bar_1= 3  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=3);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 1 & bar_1= 4  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=5);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 1 & bar_1= 5  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=5);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 1 & bar_1= 6  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 1 & bar_1= 7  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 2 & bar_1= 0  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=2);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 2 & bar_1= 1  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=3);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 2 & bar_1= 2  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=2);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 2 & bar_1= 3  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=3);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 2 & bar_1= 4  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=6);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 2 & bar_1= 5  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 2 & bar_1= 6  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=6);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 2 & bar_1= 7  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 3 & bar_1= 0  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=3);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 3 & bar_1= 1  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=3);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 3 & bar_1= 2  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=3);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 3 & bar_1= 3  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=3);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 3 & bar_1= 4  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 3 & bar_1= 5  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 3 & bar_1= 6  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 3 & bar_1= 7  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 4 & bar_1= 0  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=4);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 4 & bar_1= 1  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=5);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 4 & bar_1= 2  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=6);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 4 & bar_1= 3  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 4 & bar_1= 4  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=4);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 4 & bar_1= 5  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=5);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 4 & bar_1= 6  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=6);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 4 & bar_1= 7  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 5 & bar_1= 0  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=5);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 5 & bar_1= 1  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=5);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 5 & bar_1= 2  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 5 & bar_1= 3  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 5 & bar_1= 4  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=5);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 5 & bar_1= 5  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=5);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 5 & bar_1= 6  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 5 & bar_1= 7  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 6 & bar_1= 0  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=6);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 6 & bar_1= 1  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 6 & bar_1= 2  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=6);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 6 & bar_1= 3  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 6 & bar_1= 4  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=6);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 6 & bar_1= 5  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 6 & bar_1= 6  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=6);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 6 & bar_1= 7  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 7 & bar_1= 0  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 7 & bar_1= 1  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 7 & bar_1= 2  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 7 & bar_1= 3  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 7 & bar_1= 4  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 7 & bar_1= 5  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 7 & bar_1= 6  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=0 & mod(floor(bar_2/me_bit_1),2) = 0 & bar_2= 7 & bar_1= 7  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 1                        ->  read  : (l_2'=l_search) & (i_2'=mod(i_2+1, process_count));
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 0 & bar_2= 0  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=0);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 0 & bar_2= 1  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=1);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 0 & bar_2= 2  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=2);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 0 & bar_2= 3  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=3);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 0 & bar_2= 4  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=4);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 0 & bar_2= 5  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=5);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 0 & bar_2= 6  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=6);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 0 & bar_2= 7  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 1 & bar_2= 0  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=1);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 1 & bar_2= 1  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=1);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 1 & bar_2= 2  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=3);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 1 & bar_2= 3  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=3);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 1 & bar_2= 4  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=5);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 1 & bar_2= 5  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=5);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 1 & bar_2= 6  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 1 & bar_2= 7  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 2 & bar_2= 0  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=2);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 2 & bar_2= 1  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=3);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 2 & bar_2= 2  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=2);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 2 & bar_2= 3  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=3);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 2 & bar_2= 4  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=6);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 2 & bar_2= 5  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 2 & bar_2= 6  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=6);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 2 & bar_2= 7  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 3 & bar_2= 0  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=3);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 3 & bar_2= 1  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=3);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 3 & bar_2= 2  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=3);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 3 & bar_2= 3  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=3);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 3 & bar_2= 4  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 3 & bar_2= 5  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 3 & bar_2= 6  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 3 & bar_2= 7  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 4 & bar_2= 0  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=4);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 4 & bar_2= 1  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=5);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 4 & bar_2= 2  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=6);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 4 & bar_2= 3  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 4 & bar_2= 4  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=4);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 4 & bar_2= 5  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=5);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 4 & bar_2= 6  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=6);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 4 & bar_2= 7  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 5 & bar_2= 0  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=5);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 5 & bar_2= 1  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=5);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 5 & bar_2= 2  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 5 & bar_2= 3  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 5 & bar_2= 4  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=5);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 5 & bar_2= 5  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=5);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 5 & bar_2= 6  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 5 & bar_2= 7  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 6 & bar_2= 0  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=6);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 6 & bar_2= 1  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 6 & bar_2= 2  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=6);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 6 & bar_2= 3  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 6 & bar_2= 4  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=6);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 6 & bar_2= 5  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 6 & bar_2= 6  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=6);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 6 & bar_2= 7  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 7 & bar_2= 0  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 7 & bar_2= 1  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 7 & bar_2= 2  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 7 & bar_2= 3  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 7 & bar_2= 4  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 7 & bar_2= 5  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 7 & bar_2= 6  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=1 & mod(floor(bar_2/me_bit_2),2) = 0 & bar_2= 7 & bar_2= 7  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 1                        ->  read  : (l_2'=l_search) & (i_2'=mod(i_2+1, process_count));
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 0 & bar_0= 0  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=0);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 0 & bar_0= 1  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=1);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 0 & bar_0= 2  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=2);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 0 & bar_0= 3  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=3);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 0 & bar_0= 4  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=4);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 0 & bar_0= 5  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=5);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 0 & bar_0= 6  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=6);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 0 & bar_0= 7  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 1 & bar_0= 0  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=1);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 1 & bar_0= 1  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=1);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 1 & bar_0= 2  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=3);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 1 & bar_0= 3  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=3);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 1 & bar_0= 4  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=5);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 1 & bar_0= 5  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=5);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 1 & bar_0= 6  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 1 & bar_0= 7  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 2 & bar_0= 0  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=2);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 2 & bar_0= 1  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=3);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 2 & bar_0= 2  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=2);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 2 & bar_0= 3  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=3);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 2 & bar_0= 4  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=6);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 2 & bar_0= 5  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 2 & bar_0= 6  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=6);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 2 & bar_0= 7  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 3 & bar_0= 0  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=3);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 3 & bar_0= 1  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=3);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 3 & bar_0= 2  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=3);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 3 & bar_0= 3  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=3);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 3 & bar_0= 4  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 3 & bar_0= 5  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 3 & bar_0= 6  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 3 & bar_0= 7  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 4 & bar_0= 0  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=4);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 4 & bar_0= 1  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=5);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 4 & bar_0= 2  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=6);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 4 & bar_0= 3  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 4 & bar_0= 4  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=4);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 4 & bar_0= 5  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=5);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 4 & bar_0= 6  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=6);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 4 & bar_0= 7  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 5 & bar_0= 0  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=5);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 5 & bar_0= 1  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=5);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 5 & bar_0= 2  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 5 & bar_0= 3  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 5 & bar_0= 4  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=5);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 5 & bar_0= 5  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=5);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 5 & bar_0= 6  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 5 & bar_0= 7  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 6 & bar_0= 0  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=6);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 6 & bar_0= 1  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 6 & bar_0= 2  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=6);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 6 & bar_0= 3  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 6 & bar_0= 4  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=6);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 6 & bar_0= 5  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 6 & bar_0= 6  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=6);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 6 & bar_0= 7  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 7 & bar_0= 0  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 7 & bar_0= 1  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 7 & bar_0= 2  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 7 & bar_0= 3  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 7 & bar_0= 4  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 7 & bar_0= 5  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 7 & bar_0= 6  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);
    [search_2]   l_2=l_search & i_2=2 & mod(floor(bar_2/me_bit_0),2) = 0 & bar_2= 7 & bar_0= 7  ->  get   : (l_2'=l_test)   & (i_2'=mod(i_2+1, process_count)) & (bar_2'=7);

    [test_2]     l_2=l_test   & bar_2 =full -> read : (l_2'=l_done);
    [test_2]     l_2=l_test   & bar_2!=full -> read : (l_2'=l_search);

    [done_2]     l_2=l_done                 ->        true;
endmodule

// *** process copies end ***

// *** process rewards begin ***

// state rewards
rewards "time"
    true : base_rate;
endrewards

rewards "time_all_are_working"
    all_are_working : base_rate;
endrewards

rewards "time_not_all_are_working"
    !all_are_working : base_rate;
endrewards

rewards "time_one_is_working"
    one_is_working : base_rate;
endrewards

rewards "time_not_one_is_working"
    !one_is_working : base_rate;
endrewards

rewards "time_one_is_done"
    one_is_done : base_rate;
endrewards

rewards "time_not_one_is_done"
    !one_is_done : base_rate;
endrewards

rewards "time_not_all_are_done"
    !all_are_done : base_rate;
endrewards

rewards "time_all_are_done"
    all_are_done : base_rate;
endrewards


// *** process rewards end ***

