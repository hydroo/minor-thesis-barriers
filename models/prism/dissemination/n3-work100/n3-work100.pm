ctmc

const process_count = 3;

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
const l_init = 0;
const l_work = l_init;
const l_put  = 1;
const l_wait = 2;
const l_done = 3;

// *** main process begin ***

// * last _# at labels and variables is always the id of the "owning" process //

// * not all labels are for sync. but for easier debugging in the simulator: work_*, wait_*, done_*

module process_0
    l_0      : [l_init..l_done] init l_init;
    //bar_$fromwhom$_$me$ - an array of bits from whom we will receive
    bar_2_0  : bool             init false;
    bar_1_0  : bool             init false;
    dist_0   : [1..2]           init 1; // distance

    [work_0]   l_0=l_work                                -> work : (l_0'=l_put);

    [put_0_1]  l_0=l_put  & dist_0 = 1                   -> put  : (l_0'=l_wait);
    [put_0_2]  l_0=l_put  & dist_0 = 2                   -> put  : (l_0'=l_wait);

    [wait_2_0] l_0=l_wait & dist_0 = 1 & bar_2_0  = true -> read : (l_0'=l_put) & (dist_0'=dist_0*2);
    [wait_2_0] l_0=l_wait & dist_0 = 1 & bar_2_0 != true -> read : true;
    [wait_1_0] l_0=l_wait & dist_0 = 2 & bar_1_0  = true -> read : (l_0'=l_done);
    [wait_1_0] l_0=l_wait & dist_0 = 2 & bar_1_0 != true -> read : true;

    [done_0]   l_0=l_done                                ->        true;

    // listen for remote puts
    [put_2_0] true -> (bar_2_0'=true);
    [put_1_0] true -> (bar_1_0'=true);
endmodule

// *** main process end ***

// *** process labels begin ***

formula one_is_done                  = l_0=l_done | l_1=l_done | l_2=l_done;
formula all_are_done                 = l_0=l_done & l_1=l_done & l_2=l_done;

formula one_is_working               = l_0 = l_work | l_1 = l_work | l_2 = l_work;
formula all_are_working              = l_0 = l_work & l_1 = l_work & l_2 = l_work;

formula round_0_one = !all_are_working & !one_is_done  & (dist_0  = 1 | dist_1  = 1 | dist_2  = 1) & !(round_1_one);
formula round_0_all = !one_is_working  & !all_are_done & (dist_0 >= 1 & dist_1 >= 1 & dist_2 >= 1) & !(round_1_all);

formula round_1_one = !all_are_working & !one_is_done  & (dist_0  = 2 | dist_1  = 2 | dist_2  = 2);
formula round_1_all = !one_is_working  & !all_are_done & (dist_0 >= 2 & dist_1 >= 2 & dist_2 >= 2);


// *** process labels end ***

// *** process copies begin ***

module process_1
    l_1      : [l_init..l_done] init l_init;
    //bar_$fromwhom$_$me$ - an array of bits from whom we will receive
    bar_0_1  : bool             init false;
    bar_2_1  : bool             init false;
    dist_1   : [1..2]           init 1; // distance

    [work_1]   l_1=l_work                                -> work : (l_1'=l_put);

    [put_1_2]  l_1=l_put  & dist_1 = 1                   -> put  : (l_1'=l_wait);
    [put_1_0]  l_1=l_put  & dist_1 = 2                   -> put  : (l_1'=l_wait);

    [wait_0_1] l_1=l_wait & dist_1 = 1 & bar_0_1  = true -> read : (l_1'=l_put) & (dist_1'=dist_1*2);
    [wait_0_1] l_1=l_wait & dist_1 = 1 & bar_0_1 != true -> read : true;
    [wait_2_1] l_1=l_wait & dist_1 = 2 & bar_2_1  = true -> read : (l_1'=l_done);
    [wait_2_1] l_1=l_wait & dist_1 = 2 & bar_2_1 != true -> read : true;

    [done_1]   l_1=l_done                                ->        true;

    // listen for remote puts
    [put_0_1] true -> (bar_0_1'=true);
    [put_2_1] true -> (bar_2_1'=true);
endmodule

module process_2
    l_2      : [l_init..l_done] init l_init;
    //bar_$fromwhom$_$me$ - an array of bits from whom we will receive
    bar_1_2  : bool             init false;
    bar_0_2  : bool             init false;
    dist_2   : [1..2]           init 1; // distance

    [work_2]   l_2=l_work                                -> work : (l_2'=l_put);

    [put_2_0]  l_2=l_put  & dist_2 = 1                   -> put  : (l_2'=l_wait);
    [put_2_1]  l_2=l_put  & dist_2 = 2                   -> put  : (l_2'=l_wait);

    [wait_1_2] l_2=l_wait & dist_2 = 1 & bar_1_2  = true -> read : (l_2'=l_put) & (dist_2'=dist_2*2);
    [wait_1_2] l_2=l_wait & dist_2 = 1 & bar_1_2 != true -> read : true;
    [wait_0_2] l_2=l_wait & dist_2 = 2 & bar_0_2  = true -> read : (l_2'=l_done);
    [wait_0_2] l_2=l_wait & dist_2 = 2 & bar_0_2 != true -> read : true;

    [done_2]   l_2=l_done                                ->        true;

    // listen for remote puts
    [put_1_2] true -> (bar_1_2'=true);
    [put_0_2] true -> (bar_0_2'=true);
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
    all_are_working : base_rate;
endrewards

rewards "time_one_is_working"
    one_is_working : base_rate;
endrewards

rewards "time_not_one_is_working"
    one_is_working : base_rate;
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

// round_#_one is the time from one enters a round until one enters the next round
// correctness queries show how the state space is partitioned
rewards "time_round_0_one"
    round_0_one : base_rate;
endrewards

rewards "time_round_1_one"
    round_1_one : base_rate;
endrewards

// round_#_all is the time from all entered a round until all entered the next round
// correctness queries show how the state space is partitioned
rewards "time_round_0_all"
    round_0_all : base_rate;
endrewards

rewards "time_round_1_all"
    round_1_all : base_rate;
endrewards


// *** process rewards end ***

