ctmc

const process_count = 6;

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
    bar_5_0  : bool             init false;
    bar_4_0  : bool             init false;
    bar_2_0  : bool             init false;
    dist_0   : [1..4]    init 1; // distance

    [work_0]   l_0=l_work                                -> work : (l_0'=l_put);

    [put_0_1]  l_0=l_put  & dist_0 = 1                   -> put  : (l_0'=l_wait);
    [put_0_2]  l_0=l_put  & dist_0 = 2                   -> put  : (l_0'=l_wait);
    [put_0_4]  l_0=l_put  & dist_0 = 4                   -> put  : (l_0'=l_wait);

    [wait_5_0] l_0=l_wait & dist_0 = 1 & bar_5_0  = true -> read : (l_0'=l_put) & (dist_0'=dist_0*2);
    [wait_5_0] l_0=l_wait & dist_0 = 1 & bar_5_0 != true -> read : true;
    [wait_4_0] l_0=l_wait & dist_0 = 2 & bar_4_0  = true -> read : (l_0'=l_put) & (dist_0'=dist_0*2);
    [wait_4_0] l_0=l_wait & dist_0 = 2 & bar_4_0 != true -> read : true;
    [wait_2_0] l_0=l_wait & dist_0 = 4 & bar_2_0  = true -> read : (l_0'=l_done);
    [wait_2_0] l_0=l_wait & dist_0 = 4 & bar_2_0 != true -> read : true;

    [done_0]   l_0=l_done                                ->        true;

    // listen for remote puts
    [put_5_0] true -> (bar_5_0'=true);
    [put_4_0] true -> (bar_4_0'=true);
    [put_2_0] true -> (bar_2_0'=true);
endmodule

// *** main process end ***

// *** process labels begin ***

formula one_is_done                  = l_0=l_done | l_1=l_done | l_2=l_done | l_3=l_done | l_4=l_done | l_5=l_done;
formula all_are_done                 = l_0=l_done & l_1=l_done & l_2=l_done & l_3=l_done & l_4=l_done & l_5=l_done;

formula one_is_working               = l_0 = l_work | l_1 = l_work | l_2 = l_work | l_3 = l_work | l_4 = l_work | l_5 = l_work;
formula all_are_working              = l_0 = l_work & l_1 = l_work & l_2 = l_work & l_3 = l_work & l_4 = l_work & l_5 = l_work;

formula round_0_0          = l_0 > l_work & l_0 < l_done & dist_0 = 1;
formula round_0_1          = l_1 > l_work & l_1 < l_done & dist_1 = 1;
formula round_0_2          = l_2 > l_work & l_2 < l_done & dist_2 = 1;
formula round_0_3          = l_3 > l_work & l_3 < l_done & dist_3 = 1;
formula round_0_4          = l_4 > l_work & l_4 < l_done & dist_4 = 1;
formula round_0_5          = l_5 > l_work & l_5 < l_done & dist_5 = 1;
formula one_is_in_round_0  = round_0_0 | round_0_1 | round_0_2 | round_0_3 | round_0_4 | round_0_5;
formula all_are_in_round_0 = round_0_0 & round_0_1 & round_0_2 & round_0_3 & round_0_4 & round_0_5;
formula round_1_0          = l_0 > l_work & l_0 < l_done & dist_0 = 2;
formula round_1_1          = l_1 > l_work & l_1 < l_done & dist_1 = 2;
formula round_1_2          = l_2 > l_work & l_2 < l_done & dist_2 = 2;
formula round_1_3          = l_3 > l_work & l_3 < l_done & dist_3 = 2;
formula round_1_4          = l_4 > l_work & l_4 < l_done & dist_4 = 2;
formula round_1_5          = l_5 > l_work & l_5 < l_done & dist_5 = 2;
formula one_is_in_round_1  = round_1_0 | round_1_1 | round_1_2 | round_1_3 | round_1_4 | round_1_5;
formula all_are_in_round_1 = round_1_0 & round_1_1 & round_1_2 & round_1_3 & round_1_4 & round_1_5;
formula round_2_0          = l_0 > l_work & l_0 < l_done & dist_0 = 4;
formula round_2_1          = l_1 > l_work & l_1 < l_done & dist_1 = 4;
formula round_2_2          = l_2 > l_work & l_2 < l_done & dist_2 = 4;
formula round_2_3          = l_3 > l_work & l_3 < l_done & dist_3 = 4;
formula round_2_4          = l_4 > l_work & l_4 < l_done & dist_4 = 4;
formula round_2_5          = l_5 > l_work & l_5 < l_done & dist_5 = 4;
formula one_is_in_round_2  = round_2_0 | round_2_1 | round_2_2 | round_2_3 | round_2_4 | round_2_5;
formula all_are_in_round_2 = round_2_0 & round_2_1 & round_2_2 & round_2_3 & round_2_4 & round_2_5;

// *** process labels end ***

// *** process copies begin ***

module process_1
    l_1      : [l_init..l_done] init l_init;
    //bar_$fromwhom$_$me$ - an array of bits from whom we will receive
    bar_0_1  : bool             init false;
    bar_5_1  : bool             init false;
    bar_3_1  : bool             init false;
    dist_1   : [1..4]    init 1; // distance

    [work_1]   l_1=l_work                                -> work : (l_1'=l_put);

    [put_1_2]  l_1=l_put  & dist_1 = 1                   -> put  : (l_1'=l_wait);
    [put_1_3]  l_1=l_put  & dist_1 = 2                   -> put  : (l_1'=l_wait);
    [put_1_5]  l_1=l_put  & dist_1 = 4                   -> put  : (l_1'=l_wait);

    [wait_0_1] l_1=l_wait & dist_1 = 1 & bar_0_1  = true -> read : (l_1'=l_put) & (dist_1'=dist_1*2);
    [wait_0_1] l_1=l_wait & dist_1 = 1 & bar_0_1 != true -> read : true;
    [wait_5_1] l_1=l_wait & dist_1 = 2 & bar_5_1  = true -> read : (l_1'=l_put) & (dist_1'=dist_1*2);
    [wait_5_1] l_1=l_wait & dist_1 = 2 & bar_5_1 != true -> read : true;
    [wait_3_1] l_1=l_wait & dist_1 = 4 & bar_3_1  = true -> read : (l_1'=l_done);
    [wait_3_1] l_1=l_wait & dist_1 = 4 & bar_3_1 != true -> read : true;

    [done_1]   l_1=l_done                                ->        true;

    // listen for remote puts
    [put_0_1] true -> (bar_0_1'=true);
    [put_5_1] true -> (bar_5_1'=true);
    [put_3_1] true -> (bar_3_1'=true);
endmodule

module process_2
    l_2      : [l_init..l_done] init l_init;
    //bar_$fromwhom$_$me$ - an array of bits from whom we will receive
    bar_1_2  : bool             init false;
    bar_0_2  : bool             init false;
    bar_4_2  : bool             init false;
    dist_2   : [1..4]    init 1; // distance

    [work_2]   l_2=l_work                                -> work : (l_2'=l_put);

    [put_2_3]  l_2=l_put  & dist_2 = 1                   -> put  : (l_2'=l_wait);
    [put_2_4]  l_2=l_put  & dist_2 = 2                   -> put  : (l_2'=l_wait);
    [put_2_0]  l_2=l_put  & dist_2 = 4                   -> put  : (l_2'=l_wait);

    [wait_1_2] l_2=l_wait & dist_2 = 1 & bar_1_2  = true -> read : (l_2'=l_put) & (dist_2'=dist_2*2);
    [wait_1_2] l_2=l_wait & dist_2 = 1 & bar_1_2 != true -> read : true;
    [wait_0_2] l_2=l_wait & dist_2 = 2 & bar_0_2  = true -> read : (l_2'=l_put) & (dist_2'=dist_2*2);
    [wait_0_2] l_2=l_wait & dist_2 = 2 & bar_0_2 != true -> read : true;
    [wait_4_2] l_2=l_wait & dist_2 = 4 & bar_4_2  = true -> read : (l_2'=l_done);
    [wait_4_2] l_2=l_wait & dist_2 = 4 & bar_4_2 != true -> read : true;

    [done_2]   l_2=l_done                                ->        true;

    // listen for remote puts
    [put_1_2] true -> (bar_1_2'=true);
    [put_0_2] true -> (bar_0_2'=true);
    [put_4_2] true -> (bar_4_2'=true);
endmodule

module process_3
    l_3      : [l_init..l_done] init l_init;
    //bar_$fromwhom$_$me$ - an array of bits from whom we will receive
    bar_2_3  : bool             init false;
    bar_1_3  : bool             init false;
    bar_5_3  : bool             init false;
    dist_3   : [1..4]    init 1; // distance

    [work_3]   l_3=l_work                                -> work : (l_3'=l_put);

    [put_3_4]  l_3=l_put  & dist_3 = 1                   -> put  : (l_3'=l_wait);
    [put_3_5]  l_3=l_put  & dist_3 = 2                   -> put  : (l_3'=l_wait);
    [put_3_1]  l_3=l_put  & dist_3 = 4                   -> put  : (l_3'=l_wait);

    [wait_2_3] l_3=l_wait & dist_3 = 1 & bar_2_3  = true -> read : (l_3'=l_put) & (dist_3'=dist_3*2);
    [wait_2_3] l_3=l_wait & dist_3 = 1 & bar_2_3 != true -> read : true;
    [wait_1_3] l_3=l_wait & dist_3 = 2 & bar_1_3  = true -> read : (l_3'=l_put) & (dist_3'=dist_3*2);
    [wait_1_3] l_3=l_wait & dist_3 = 2 & bar_1_3 != true -> read : true;
    [wait_5_3] l_3=l_wait & dist_3 = 4 & bar_5_3  = true -> read : (l_3'=l_done);
    [wait_5_3] l_3=l_wait & dist_3 = 4 & bar_5_3 != true -> read : true;

    [done_3]   l_3=l_done                                ->        true;

    // listen for remote puts
    [put_2_3] true -> (bar_2_3'=true);
    [put_1_3] true -> (bar_1_3'=true);
    [put_5_3] true -> (bar_5_3'=true);
endmodule

module process_4
    l_4      : [l_init..l_done] init l_init;
    //bar_$fromwhom$_$me$ - an array of bits from whom we will receive
    bar_3_4  : bool             init false;
    bar_2_4  : bool             init false;
    bar_0_4  : bool             init false;
    dist_4   : [1..4]    init 1; // distance

    [work_4]   l_4=l_work                                -> work : (l_4'=l_put);

    [put_4_5]  l_4=l_put  & dist_4 = 1                   -> put  : (l_4'=l_wait);
    [put_4_0]  l_4=l_put  & dist_4 = 2                   -> put  : (l_4'=l_wait);
    [put_4_2]  l_4=l_put  & dist_4 = 4                   -> put  : (l_4'=l_wait);

    [wait_3_4] l_4=l_wait & dist_4 = 1 & bar_3_4  = true -> read : (l_4'=l_put) & (dist_4'=dist_4*2);
    [wait_3_4] l_4=l_wait & dist_4 = 1 & bar_3_4 != true -> read : true;
    [wait_2_4] l_4=l_wait & dist_4 = 2 & bar_2_4  = true -> read : (l_4'=l_put) & (dist_4'=dist_4*2);
    [wait_2_4] l_4=l_wait & dist_4 = 2 & bar_2_4 != true -> read : true;
    [wait_0_4] l_4=l_wait & dist_4 = 4 & bar_0_4  = true -> read : (l_4'=l_done);
    [wait_0_4] l_4=l_wait & dist_4 = 4 & bar_0_4 != true -> read : true;

    [done_4]   l_4=l_done                                ->        true;

    // listen for remote puts
    [put_3_4] true -> (bar_3_4'=true);
    [put_2_4] true -> (bar_2_4'=true);
    [put_0_4] true -> (bar_0_4'=true);
endmodule

module process_5
    l_5      : [l_init..l_done] init l_init;
    //bar_$fromwhom$_$me$ - an array of bits from whom we will receive
    bar_4_5  : bool             init false;
    bar_3_5  : bool             init false;
    bar_1_5  : bool             init false;
    dist_5   : [1..4]    init 1; // distance

    [work_5]   l_5=l_work                                -> work : (l_5'=l_put);

    [put_5_0]  l_5=l_put  & dist_5 = 1                   -> put  : (l_5'=l_wait);
    [put_5_1]  l_5=l_put  & dist_5 = 2                   -> put  : (l_5'=l_wait);
    [put_5_3]  l_5=l_put  & dist_5 = 4                   -> put  : (l_5'=l_wait);

    [wait_4_5] l_5=l_wait & dist_5 = 1 & bar_4_5  = true -> read : (l_5'=l_put) & (dist_5'=dist_5*2);
    [wait_4_5] l_5=l_wait & dist_5 = 1 & bar_4_5 != true -> read : true;
    [wait_3_5] l_5=l_wait & dist_5 = 2 & bar_3_5  = true -> read : (l_5'=l_put) & (dist_5'=dist_5*2);
    [wait_3_5] l_5=l_wait & dist_5 = 2 & bar_3_5 != true -> read : true;
    [wait_1_5] l_5=l_wait & dist_5 = 4 & bar_1_5  = true -> read : (l_5'=l_done);
    [wait_1_5] l_5=l_wait & dist_5 = 4 & bar_1_5 != true -> read : true;

    [done_5]   l_5=l_done                                ->        true;

    // listen for remote puts
    [put_4_5] true -> (bar_4_5'=true);
    [put_3_5] true -> (bar_3_5'=true);
    [put_1_5] true -> (bar_1_5'=true);
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
rewards "time_one_is_in_round_0"
	one_is_in_round_0 : base_rate;
endrewards
rewards "time_one_is_in_round_1"
	one_is_in_round_1 : base_rate;
endrewards
rewards "time_one_is_in_round_2"
	one_is_in_round_2 : base_rate;
endrewards

rewards "time_all_are_in_round_0"
	all_are_in_round_0 : base_rate;
endrewards
rewards "time_all_are_in_round_1"
	all_are_in_round_1 : base_rate;
endrewards
rewards "time_all_are_in_round_2"
	all_are_in_round_2 : base_rate;
endrewards

// *** process rewards end ***

