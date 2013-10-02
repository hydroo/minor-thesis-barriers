ctmc

const thread_count = 3;

const work_ticks  = 100;

// rates
const double base_rate = 1000.0;
const double tick      = base_rate / 1.0;
const double work      = tick / work_ticks;

// thread locations
// all names describe the behaviour of the next transition
const l_init         = 0;
const l_work         = l_init;
const l_atomic_begin = 1;
const l_read         = 2;
const l_write        = 3;
const l_atomic_end   = 4;
const l_wait         = 5;
const l_done         = 6;

// *** main thread begin ***

// * you always need to add transitions for all sync labels in var_shared, otherwise
//   they will not be recognized as synchronized and are able to fire always
//
// * not all labels are for sync. but for easier debugging in the simulator: work_*, done_*
// * always read using [var_read_n]
// * always write using [var_set_to_*_n]
//
// * always introduce an atomic op using [bar_atomic_begin_n]
// * use read and writes as usual in between
// * always end an atomic op using [bar_atomic_end_n]

module thread_0
    l_0 : [l_init..l_done] init l_init;

    [work_0]             l_0=l_work                -> work : (l_0'=l_atomic_begin);

    [bar_atomic_begin_0] l_0=l_atomic_begin        ->        (l_0'=l_read);

    [bar_read_0]         l_0=l_read                ->        (l_0'=l_write);

    [bar_set_to_0_0]     l_0=l_write      & bar =1 ->        (l_0'=l_atomic_end);
    [bar_set_to_1_0]     l_0=l_write      & bar =2 ->        (l_0'=l_atomic_end);
    [bar_set_to_2_0]     l_0=l_write      & bar =3 ->        (l_0'=l_atomic_end);

    [bar_atomic_end_0]   l_0=l_atomic_end          ->        (l_0'=l_wait);

    [bar_read_0]         l_0=l_wait       & bar!=0 ->        true;
    [bar_read_0]         l_0=l_wait       & bar =0 ->        (l_0'=l_done);

    [done_0]             l_0=l_done                ->        true;
endmodule

// *** main thread end ***

// *** thread labels begin ***

formula one_is_done                  = l_0=l_done | l_1=l_done | l_2=l_done;
formula all_are_done                 = l_0=l_done & l_1=l_done & l_2=l_done;

formula one_is_working               = l_0 = l_work | l_1 = l_work | l_2 = l_work;
formula all_are_working              = l_0 = l_work & l_1 = l_work & l_2 = l_work;
formula exactly_one_is_done_working  = (l_0 >= l_atomic_begin & l_1 = l_work & l_2 = l_work) | (l_1 >= l_atomic_begin & l_0 = l_work & l_2 = l_work) | (l_2 >= l_atomic_begin & l_0 = l_work & l_1 = l_work);

formula one_is_writing               = !all_are_working & (l_0 <= l_atomic_end | l_1 <= l_atomic_end | l_2 <= l_atomic_end);
formula all_are_writing              = !one_is_working  & (l_0 <= l_atomic_end & l_1 <= l_atomic_end & l_2 <= l_atomic_end);
formula none_are_writing             = !one_is_writing;

formula one_is_reading               = l_0=l_wait & (l_1>=l_wait & l_2>=l_wait) | l_1=l_wait & (l_0>=l_wait & l_2>=l_wait) | l_2=l_wait & (l_0>=l_wait & l_1>=l_wait);
formula all_are_reading_or_done      = l_0>=l_wait & l_1>=l_wait & l_2>=l_wait;

// *** thread labels end ***

// *** shared memory begin ***

const me_0 = 0; const me_1 = 1; const me_2 = 2; 
const me_bit_0 = 1; const me_bit_1 = 2; const me_bit_2 = 4; 
const empty = 0; const full  = me_bit_0 + me_bit_1 + me_bit_2 + 0;

const someoneIsModified   = 0;
const someoneDoesAtomicOp = 1;
const someAreShared       = 2;

const read_ticks         = 50;
const write_ticks        = 100;
const atomic_begin_ticks = write_ticks;

const double read         = tick / read_ticks;
const double write        = tick / write_ticks;
const double atomic_begin = tick / atomic_begin_ticks;

module bar_variable
	bar : [0..thread_count] init thread_count;
	[bar_set_to_0_0] true -> (bar'=0);
	[bar_set_to_1_0] true -> (bar'=1);
	[bar_set_to_2_0] true -> (bar'=2);
	[bar_set_to_0_1] true -> (bar'=0);
	[bar_set_to_1_1] true -> (bar'=1);
	[bar_set_to_2_1] true -> (bar'=2);
	[bar_set_to_0_2] true -> (bar'=0);
	[bar_set_to_1_2] true -> (bar'=1);
	[bar_set_to_2_2] true -> (bar'=2);
endmodule

module bar_shared
	bar_state : [someoneIsModified..someAreShared] init someoneIsModified;
	bar_who   : [empty..full] init empty;


	[bar_set_to_0_0] (bar_state =someoneIsModified   & bar_who =me_bit_0)          -> tick         : true;
	[bar_set_to_0_0] (bar_state =someoneDoesAtomicOp & bar_who =me_bit_0)          -> tick         : true;
	[bar_set_to_0_0] (bar_state =someoneIsModified   & bar_who!=me_bit_0)          -> write        : (bar_who'=me_bit_0);
	[bar_set_to_0_0] (bar_state =someAreShared)                                    -> write        : (bar_state'=someoneIsModified) & (bar_who'=me_bit_0);
	[bar_set_to_1_0] (bar_state =someoneIsModified   & bar_who =me_bit_0)          -> tick         : true;
	[bar_set_to_1_0] (bar_state =someoneDoesAtomicOp & bar_who =me_bit_0)          -> tick         : true;
	[bar_set_to_1_0] (bar_state =someoneIsModified   & bar_who!=me_bit_0)          -> write        : (bar_who'=me_bit_0);
	[bar_set_to_1_0] (bar_state =someAreShared)                                    -> write        : (bar_state'=someoneIsModified) & (bar_who'=me_bit_0);
	[bar_set_to_2_0] (bar_state =someoneIsModified   & bar_who =me_bit_0)          -> tick         : true;
	[bar_set_to_2_0] (bar_state =someoneDoesAtomicOp & bar_who =me_bit_0)          -> tick         : true;
	[bar_set_to_2_0] (bar_state =someoneIsModified   & bar_who!=me_bit_0)          -> write        : (bar_who'=me_bit_0);
	[bar_set_to_2_0] (bar_state =someAreShared)                                    -> write        : (bar_state'=someoneIsModified) & (bar_who'=me_bit_0);

	[bar_read_0] bar_state=someoneIsModified   & bar_who =me_bit_0                 -> tick         : true;
	[bar_read_0] bar_state=someoneDoesAtomicOp & bar_who =me_bit_0                 -> tick         : true;
	[bar_read_0] bar_state=someoneIsModified   & bar_who!=me_bit_0                 -> read         : (bar_state'=someAreShared) & (bar_who'=min(full,max(bar_who+me_bit_0, empty)));
	[bar_read_0] bar_state=someAreShared       & mod(floor(bar_who/me_bit_0),2)=1  -> tick         : true;
	[bar_read_0] bar_state=someAreShared       & mod(floor(bar_who/me_bit_0),2)=0  -> read         : (bar_who'=min(full,max(bar_who+me_bit_0, empty)));

	[bar_atomic_begin_0] (bar_state =someoneIsModified   & bar_who =me_bit_0)      -> tick         : (bar_state'=someoneDoesAtomicOp);
	[bar_atomic_begin_0] (bar_state =someoneIsModified   & bar_who!=me_bit_0)      -> atomic_begin : (bar_state'=someoneDoesAtomicOp) & (bar_who'=me_bit_0);
	[bar_atomic_begin_0] (bar_state =someAreShared)                                -> atomic_begin : (bar_state'=someoneDoesAtomicOp) & (bar_who'=me_bit_0);
	[bar_atomic_end_0]   (bar_state =someoneDoesAtomicOp & bar_who =me_bit_0)      -> tick         : (bar_state'=someoneIsModified);

	[bar_set_to_0_1] (bar_state =someoneIsModified   & bar_who =me_bit_1)          -> tick         : true;
	[bar_set_to_0_1] (bar_state =someoneDoesAtomicOp & bar_who =me_bit_1)          -> tick         : true;
	[bar_set_to_0_1] (bar_state =someoneIsModified   & bar_who!=me_bit_1)          -> write        : (bar_who'=me_bit_1);
	[bar_set_to_0_1] (bar_state =someAreShared)                                    -> write        : (bar_state'=someoneIsModified) & (bar_who'=me_bit_1);
	[bar_set_to_1_1] (bar_state =someoneIsModified   & bar_who =me_bit_1)          -> tick         : true;
	[bar_set_to_1_1] (bar_state =someoneDoesAtomicOp & bar_who =me_bit_1)          -> tick         : true;
	[bar_set_to_1_1] (bar_state =someoneIsModified   & bar_who!=me_bit_1)          -> write        : (bar_who'=me_bit_1);
	[bar_set_to_1_1] (bar_state =someAreShared)                                    -> write        : (bar_state'=someoneIsModified) & (bar_who'=me_bit_1);
	[bar_set_to_2_1] (bar_state =someoneIsModified   & bar_who =me_bit_1)          -> tick         : true;
	[bar_set_to_2_1] (bar_state =someoneDoesAtomicOp & bar_who =me_bit_1)          -> tick         : true;
	[bar_set_to_2_1] (bar_state =someoneIsModified   & bar_who!=me_bit_1)          -> write        : (bar_who'=me_bit_1);
	[bar_set_to_2_1] (bar_state =someAreShared)                                    -> write        : (bar_state'=someoneIsModified) & (bar_who'=me_bit_1);

	[bar_read_1] bar_state=someoneIsModified   & bar_who =me_bit_1                 -> tick         : true;
	[bar_read_1] bar_state=someoneDoesAtomicOp & bar_who =me_bit_1                 -> tick         : true;
	[bar_read_1] bar_state=someoneIsModified   & bar_who!=me_bit_1                 -> read         : (bar_state'=someAreShared) & (bar_who'=min(full,max(bar_who+me_bit_1, empty)));
	[bar_read_1] bar_state=someAreShared       & mod(floor(bar_who/me_bit_1),2)=1  -> tick         : true;
	[bar_read_1] bar_state=someAreShared       & mod(floor(bar_who/me_bit_1),2)=0  -> read         : (bar_who'=min(full,max(bar_who+me_bit_1, empty)));

	[bar_atomic_begin_1] (bar_state =someoneIsModified   & bar_who =me_bit_1)      -> tick         : (bar_state'=someoneDoesAtomicOp);
	[bar_atomic_begin_1] (bar_state =someoneIsModified   & bar_who!=me_bit_1)      -> atomic_begin : (bar_state'=someoneDoesAtomicOp) & (bar_who'=me_bit_1);
	[bar_atomic_begin_1] (bar_state =someAreShared)                                -> atomic_begin : (bar_state'=someoneDoesAtomicOp) & (bar_who'=me_bit_1);
	[bar_atomic_end_1]   (bar_state =someoneDoesAtomicOp & bar_who =me_bit_1)      -> tick         : (bar_state'=someoneIsModified);

	[bar_set_to_0_2] (bar_state =someoneIsModified   & bar_who =me_bit_2)          -> tick         : true;
	[bar_set_to_0_2] (bar_state =someoneDoesAtomicOp & bar_who =me_bit_2)          -> tick         : true;
	[bar_set_to_0_2] (bar_state =someoneIsModified   & bar_who!=me_bit_2)          -> write        : (bar_who'=me_bit_2);
	[bar_set_to_0_2] (bar_state =someAreShared)                                    -> write        : (bar_state'=someoneIsModified) & (bar_who'=me_bit_2);
	[bar_set_to_1_2] (bar_state =someoneIsModified   & bar_who =me_bit_2)          -> tick         : true;
	[bar_set_to_1_2] (bar_state =someoneDoesAtomicOp & bar_who =me_bit_2)          -> tick         : true;
	[bar_set_to_1_2] (bar_state =someoneIsModified   & bar_who!=me_bit_2)          -> write        : (bar_who'=me_bit_2);
	[bar_set_to_1_2] (bar_state =someAreShared)                                    -> write        : (bar_state'=someoneIsModified) & (bar_who'=me_bit_2);
	[bar_set_to_2_2] (bar_state =someoneIsModified   & bar_who =me_bit_2)          -> tick         : true;
	[bar_set_to_2_2] (bar_state =someoneDoesAtomicOp & bar_who =me_bit_2)          -> tick         : true;
	[bar_set_to_2_2] (bar_state =someoneIsModified   & bar_who!=me_bit_2)          -> write        : (bar_who'=me_bit_2);
	[bar_set_to_2_2] (bar_state =someAreShared)                                    -> write        : (bar_state'=someoneIsModified) & (bar_who'=me_bit_2);

	[bar_read_2] bar_state=someoneIsModified   & bar_who =me_bit_2                 -> tick         : true;
	[bar_read_2] bar_state=someoneDoesAtomicOp & bar_who =me_bit_2                 -> tick         : true;
	[bar_read_2] bar_state=someoneIsModified   & bar_who!=me_bit_2                 -> read         : (bar_state'=someAreShared) & (bar_who'=min(full,max(bar_who+me_bit_2, empty)));
	[bar_read_2] bar_state=someAreShared       & mod(floor(bar_who/me_bit_2),2)=1  -> tick         : true;
	[bar_read_2] bar_state=someAreShared       & mod(floor(bar_who/me_bit_2),2)=0  -> read         : (bar_who'=min(full,max(bar_who+me_bit_2, empty)));

	[bar_atomic_begin_2] (bar_state =someoneIsModified   & bar_who =me_bit_2)      -> tick         : (bar_state'=someoneDoesAtomicOp);
	[bar_atomic_begin_2] (bar_state =someoneIsModified   & bar_who!=me_bit_2)      -> atomic_begin : (bar_state'=someoneDoesAtomicOp) & (bar_who'=me_bit_2);
	[bar_atomic_begin_2] (bar_state =someAreShared)                                -> atomic_begin : (bar_state'=someoneDoesAtomicOp) & (bar_who'=me_bit_2);
	[bar_atomic_end_2]   (bar_state =someoneDoesAtomicOp & bar_who =me_bit_2)      -> tick         : (bar_state'=someoneIsModified);
endmodule

label "bar_invalid_0"   = ((bar_state=someoneIsModified   | bar_state=someAreShared) & mod(floor(bar_who/me_bit_0),2)=0);
label "bar_modified_0"  =  (bar_state=someoneIsModified   & bar_who=me_bit_0);
label "bar_atomic_op_0" =  (bar_state=someoneDoesAtomicOp & bar_who=me_bit_0);
label "bar_shared_0"    =  (bar_state=someAreShared       & mod(floor(bar_who/me_bit_0),2)=1);
label "bar_invalid_1"   = ((bar_state=someoneIsModified   | bar_state=someAreShared) & mod(floor(bar_who/me_bit_1),2)=0);
label "bar_modified_1"  =  (bar_state=someoneIsModified   & bar_who=me_bit_1);
label "bar_atomic_op_1" =  (bar_state=someoneDoesAtomicOp & bar_who=me_bit_1);
label "bar_shared_1"    =  (bar_state=someAreShared       & mod(floor(bar_who/me_bit_1),2)=1);
label "bar_invalid_2"   = ((bar_state=someoneIsModified   | bar_state=someAreShared) & mod(floor(bar_who/me_bit_2),2)=0);
label "bar_modified_2"  =  (bar_state=someoneIsModified   & bar_who=me_bit_2);
label "bar_atomic_op_2" =  (bar_state=someoneDoesAtomicOp & bar_who=me_bit_2);
label "bar_shared_2"    =  (bar_state=someAreShared       & mod(floor(bar_who/me_bit_2),2)=1);

// *** shared memory end ***

// *** thread copies begin ***

module thread_1
    l_1 : [l_init..l_done] init l_init;

    [work_1]             l_1=l_work                -> work : (l_1'=l_atomic_begin);

    [bar_atomic_begin_1] l_1=l_atomic_begin        ->        (l_1'=l_read);

    [bar_read_1]         l_1=l_read                ->        (l_1'=l_write);

    [bar_set_to_0_1]     l_1=l_write      & bar =1 ->        (l_1'=l_atomic_end);
    [bar_set_to_1_1]     l_1=l_write      & bar =2 ->        (l_1'=l_atomic_end);
    [bar_set_to_2_1]     l_1=l_write      & bar =3 ->        (l_1'=l_atomic_end);

    [bar_atomic_end_1]   l_1=l_atomic_end          ->        (l_1'=l_wait);

    [bar_read_1]         l_1=l_wait       & bar!=0 ->        true;
    [bar_read_1]         l_1=l_wait       & bar =0 ->        (l_1'=l_done);

    [done_1]             l_1=l_done                ->        true;
endmodule

module thread_2
    l_2 : [l_init..l_done] init l_init;

    [work_2]             l_2=l_work                -> work : (l_2'=l_atomic_begin);

    [bar_atomic_begin_2] l_2=l_atomic_begin        ->        (l_2'=l_read);

    [bar_read_2]         l_2=l_read                ->        (l_2'=l_write);

    [bar_set_to_0_2]     l_2=l_write      & bar =1 ->        (l_2'=l_atomic_end);
    [bar_set_to_1_2]     l_2=l_write      & bar =2 ->        (l_2'=l_atomic_end);
    [bar_set_to_2_2]     l_2=l_write      & bar =3 ->        (l_2'=l_atomic_end);

    [bar_atomic_end_2]   l_2=l_atomic_end          ->        (l_2'=l_wait);

    [bar_read_2]         l_2=l_wait       & bar!=0 ->        true;
    [bar_read_2]         l_2=l_wait       & bar =0 ->        (l_2'=l_done);

    [done_2]             l_2=l_done                ->        true;
endmodule

// *** thread copies end ***

// *** thread rewards begin ***

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

rewards "time_one_is_writing"
	one_is_writing : base_rate;
endrewards

rewards "time_one_is_reading"
	one_is_reading : base_rate;
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

// *** thread rewards end ***

