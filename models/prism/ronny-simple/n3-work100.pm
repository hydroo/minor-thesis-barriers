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
const l_write        = 2;
const l_wait         = 3;
const l_done         = 4;

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
    i_0 : [0..thread_count] init 0;

    [work_0]                      l_0=l_work                        -> work : (l_0'=l_write);

    [bar_0_set_to_1_0]            l_0=l_write                       ->        (l_0'=l_wait);

    [does_i_equal_thread_count_0] l_0=l_wait  & i_0 = thread_count  -> tick : (l_0'=l_done);
    [bar_0_read_0]                l_0=l_wait  & i_0 = 0 & bar_0 = 1 ->        (i_0' = min(i_0 + 1, thread_count));
    [bar_0_read_0]                l_0=l_wait  & i_0 = 0 & bar_0 = 0 ->        (i_0' = 0);
    [bar_1_read_0]                l_0=l_wait  & i_0 = 1 & bar_1 = 1 ->        (i_0' = min(i_0 + 1, thread_count));
    [bar_1_read_0]                l_0=l_wait  & i_0 = 1 & bar_1 = 0 ->        (i_0' = 0);
    [bar_2_read_0]                l_0=l_wait  & i_0 = 2 & bar_2 = 1 ->        (i_0' = min(i_0 + 1, thread_count));
    [bar_2_read_0]                l_0=l_wait  & i_0 = 2 & bar_2 = 0 ->        (i_0' = 0);

    [done_0]                      l_0=l_done                        ->        true;

    // do never trigger the following sync transitions
    [bar_0_atomic_begin_0] false -> true;
    [bar_0_atomic_end_0]   false -> true;
    [bar_0_set_to_0_0]     false -> true;
    [bar_1_atomic_begin_0] false -> true;
    [bar_1_atomic_end_0]   false -> true;
    [bar_1_set_to_0_0]     false -> true;
    [bar_1_set_to_1_0]     false -> true;
    [bar_2_atomic_begin_0] false -> true;
    [bar_2_atomic_end_0]   false -> true;
    [bar_2_set_to_0_0]     false -> true;
    [bar_2_set_to_1_0]     false -> true;

endmodule

// *** main thread end ***

// *** thread labels begin ***

formula one_is_done                  = l_0=l_done | l_1=l_done | l_2=l_done;
formula all_are_done                 = l_0=l_done & l_1=l_done & l_2=l_done;

formula one_is_working               = l_0 = l_work | l_1 = l_work | l_2 = l_work;
formula all_are_working              = l_0 = l_work & l_1 = l_work & l_2 = l_work;
formula exactly_one_is_done_working  = (l_0 >= l_write & l_1 = l_work & l_2 = l_work) | (l_1 >= l_write & l_0 = l_work & l_2 = l_work) | (l_2 >= l_write & l_0 = l_work & l_1 = l_work);

formula one_is_writing               = !all_are_working & (l_0 <= l_write | l_1 <= l_write | l_2 <= l_write);
formula none_are_writing             = !one_is_writing;

formula one_is_reading               = l_0=l_wait & (l_1>=l_wait & l_2>=l_wait) | l_1=l_wait & (l_0>=l_wait & l_2>=l_wait) | l_2=l_wait & (l_0>=l_wait & l_1>=l_wait);
formula all_are_reading_or_done      = l_0>=l_wait & l_1>=l_wait & l_2>=l_wait;
 label "woot"                      =  (bar_0_state=someAreShared & !(bar_0_who =0 | bar_0_who =me_bit_0 | bar_0_who =me_bit_1 | bar_0_who =me_bit_2)) | (bar_1_state=someAreShared & !(bar_1_who =0 | bar_1_who =me_bit_0 | bar_1_who =me_bit_1 | bar_1_who =me_bit_2)) | (bar_2_state=someAreShared & !(bar_2_who =0 | bar_2_who =me_bit_0 | bar_2_who =me_bit_1 | bar_2_who =me_bit_2));

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

module bar_0_variable
	bar_0 : [0..1] init 0;
	[bar_0_set_to_0_0] true -> (bar_0'=0);
	[bar_0_set_to_1_0] true -> (bar_0'=1);
	[bar_0_set_to_0_1] true -> (bar_0'=0);
	[bar_0_set_to_1_1] true -> (bar_0'=1);
	[bar_0_set_to_0_2] true -> (bar_0'=0);
	[bar_0_set_to_1_2] true -> (bar_0'=1);
endmodule

module bar_0_shared
	bar_0_state : [someoneIsModified..someAreShared] init someoneIsModified;
	bar_0_who   : [empty..full] init empty;


	[bar_0_set_to_0_0] (bar_0_state =someoneIsModified   & bar_0_who =me_bit_0)          -> tick         : true;
	[bar_0_set_to_0_0] (bar_0_state =someoneDoesAtomicOp & bar_0_who =me_bit_0)          -> tick         : true;
	[bar_0_set_to_0_0] (bar_0_state =someoneIsModified   & bar_0_who!=me_bit_0)          -> write        : (bar_0_who'=me_bit_0);
	[bar_0_set_to_0_0] (bar_0_state =someAreShared)                                    -> write        : (bar_0_state'=someoneIsModified) & (bar_0_who'=me_bit_0);
	[bar_0_set_to_1_0] (bar_0_state =someoneIsModified   & bar_0_who =me_bit_0)          -> tick         : true;
	[bar_0_set_to_1_0] (bar_0_state =someoneDoesAtomicOp & bar_0_who =me_bit_0)          -> tick         : true;
	[bar_0_set_to_1_0] (bar_0_state =someoneIsModified   & bar_0_who!=me_bit_0)          -> write        : (bar_0_who'=me_bit_0);
	[bar_0_set_to_1_0] (bar_0_state =someAreShared)                                    -> write        : (bar_0_state'=someoneIsModified) & (bar_0_who'=me_bit_0);

	[bar_0_read_0] bar_0_state=someoneIsModified   & bar_0_who =me_bit_0                 -> tick         : true;
	[bar_0_read_0] bar_0_state=someoneDoesAtomicOp & bar_0_who =me_bit_0                 -> tick         : true;
	[bar_0_read_0] bar_0_state=someoneIsModified   & bar_0_who!=me_bit_0                 -> read         : (bar_0_state'=someAreShared) & (bar_0_who'=min(full,max(bar_0_who+me_bit_0, empty)));
	[bar_0_read_0] bar_0_state=someAreShared       & mod(floor(bar_0_who/me_bit_0),2)=1  -> tick         : true;
	[bar_0_read_0] bar_0_state=someAreShared       & mod(floor(bar_0_who/me_bit_0),2)=0  -> read         : (bar_0_who'=min(full,max(bar_0_who+me_bit_0, empty)));

	[bar_0_atomic_begin_0] (bar_0_state =someoneIsModified   & bar_0_who =me_bit_0)      -> tick         : (bar_0_state'=someoneDoesAtomicOp);
	[bar_0_atomic_begin_0] (bar_0_state =someoneIsModified   & bar_0_who!=me_bit_0)      -> atomic_begin : (bar_0_state'=someoneDoesAtomicOp) & (bar_0_who'=me_bit_0);
	[bar_0_atomic_begin_0] (bar_0_state =someAreShared)                                -> atomic_begin : (bar_0_state'=someoneDoesAtomicOp) & (bar_0_who'=me_bit_0);
	[bar_0_atomic_end_0]   (bar_0_state =someoneDoesAtomicOp & bar_0_who =me_bit_0)      -> tick         : (bar_0_state'=someoneIsModified);

	[bar_0_set_to_0_1] (bar_0_state =someoneIsModified   & bar_0_who =me_bit_1)          -> tick         : true;
	[bar_0_set_to_0_1] (bar_0_state =someoneDoesAtomicOp & bar_0_who =me_bit_1)          -> tick         : true;
	[bar_0_set_to_0_1] (bar_0_state =someoneIsModified   & bar_0_who!=me_bit_1)          -> write        : (bar_0_who'=me_bit_1);
	[bar_0_set_to_0_1] (bar_0_state =someAreShared)                                    -> write        : (bar_0_state'=someoneIsModified) & (bar_0_who'=me_bit_1);
	[bar_0_set_to_1_1] (bar_0_state =someoneIsModified   & bar_0_who =me_bit_1)          -> tick         : true;
	[bar_0_set_to_1_1] (bar_0_state =someoneDoesAtomicOp & bar_0_who =me_bit_1)          -> tick         : true;
	[bar_0_set_to_1_1] (bar_0_state =someoneIsModified   & bar_0_who!=me_bit_1)          -> write        : (bar_0_who'=me_bit_1);
	[bar_0_set_to_1_1] (bar_0_state =someAreShared)                                    -> write        : (bar_0_state'=someoneIsModified) & (bar_0_who'=me_bit_1);

	[bar_0_read_1] bar_0_state=someoneIsModified   & bar_0_who =me_bit_1                 -> tick         : true;
	[bar_0_read_1] bar_0_state=someoneDoesAtomicOp & bar_0_who =me_bit_1                 -> tick         : true;
	[bar_0_read_1] bar_0_state=someoneIsModified   & bar_0_who!=me_bit_1                 -> read         : (bar_0_state'=someAreShared) & (bar_0_who'=min(full,max(bar_0_who+me_bit_1, empty)));
	[bar_0_read_1] bar_0_state=someAreShared       & mod(floor(bar_0_who/me_bit_1),2)=1  -> tick         : true;
	[bar_0_read_1] bar_0_state=someAreShared       & mod(floor(bar_0_who/me_bit_1),2)=0  -> read         : (bar_0_who'=min(full,max(bar_0_who+me_bit_1, empty)));

	[bar_0_atomic_begin_1] (bar_0_state =someoneIsModified   & bar_0_who =me_bit_1)      -> tick         : (bar_0_state'=someoneDoesAtomicOp);
	[bar_0_atomic_begin_1] (bar_0_state =someoneIsModified   & bar_0_who!=me_bit_1)      -> atomic_begin : (bar_0_state'=someoneDoesAtomicOp) & (bar_0_who'=me_bit_1);
	[bar_0_atomic_begin_1] (bar_0_state =someAreShared)                                -> atomic_begin : (bar_0_state'=someoneDoesAtomicOp) & (bar_0_who'=me_bit_1);
	[bar_0_atomic_end_1]   (bar_0_state =someoneDoesAtomicOp & bar_0_who =me_bit_1)      -> tick         : (bar_0_state'=someoneIsModified);

	[bar_0_set_to_0_2] (bar_0_state =someoneIsModified   & bar_0_who =me_bit_2)          -> tick         : true;
	[bar_0_set_to_0_2] (bar_0_state =someoneDoesAtomicOp & bar_0_who =me_bit_2)          -> tick         : true;
	[bar_0_set_to_0_2] (bar_0_state =someoneIsModified   & bar_0_who!=me_bit_2)          -> write        : (bar_0_who'=me_bit_2);
	[bar_0_set_to_0_2] (bar_0_state =someAreShared)                                    -> write        : (bar_0_state'=someoneIsModified) & (bar_0_who'=me_bit_2);
	[bar_0_set_to_1_2] (bar_0_state =someoneIsModified   & bar_0_who =me_bit_2)          -> tick         : true;
	[bar_0_set_to_1_2] (bar_0_state =someoneDoesAtomicOp & bar_0_who =me_bit_2)          -> tick         : true;
	[bar_0_set_to_1_2] (bar_0_state =someoneIsModified   & bar_0_who!=me_bit_2)          -> write        : (bar_0_who'=me_bit_2);
	[bar_0_set_to_1_2] (bar_0_state =someAreShared)                                    -> write        : (bar_0_state'=someoneIsModified) & (bar_0_who'=me_bit_2);

	[bar_0_read_2] bar_0_state=someoneIsModified   & bar_0_who =me_bit_2                 -> tick         : true;
	[bar_0_read_2] bar_0_state=someoneDoesAtomicOp & bar_0_who =me_bit_2                 -> tick         : true;
	[bar_0_read_2] bar_0_state=someoneIsModified   & bar_0_who!=me_bit_2                 -> read         : (bar_0_state'=someAreShared) & (bar_0_who'=min(full,max(bar_0_who+me_bit_2, empty)));
	[bar_0_read_2] bar_0_state=someAreShared       & mod(floor(bar_0_who/me_bit_2),2)=1  -> tick         : true;
	[bar_0_read_2] bar_0_state=someAreShared       & mod(floor(bar_0_who/me_bit_2),2)=0  -> read         : (bar_0_who'=min(full,max(bar_0_who+me_bit_2, empty)));

	[bar_0_atomic_begin_2] (bar_0_state =someoneIsModified   & bar_0_who =me_bit_2)      -> tick         : (bar_0_state'=someoneDoesAtomicOp);
	[bar_0_atomic_begin_2] (bar_0_state =someoneIsModified   & bar_0_who!=me_bit_2)      -> atomic_begin : (bar_0_state'=someoneDoesAtomicOp) & (bar_0_who'=me_bit_2);
	[bar_0_atomic_begin_2] (bar_0_state =someAreShared)                                -> atomic_begin : (bar_0_state'=someoneDoesAtomicOp) & (bar_0_who'=me_bit_2);
	[bar_0_atomic_end_2]   (bar_0_state =someoneDoesAtomicOp & bar_0_who =me_bit_2)      -> tick         : (bar_0_state'=someoneIsModified);
endmodule

module bar_1_variable
	bar_1 : [0..1] init 0;
	[bar_1_set_to_0_0] true -> (bar_1'=0);
	[bar_1_set_to_1_0] true -> (bar_1'=1);
	[bar_1_set_to_0_1] true -> (bar_1'=0);
	[bar_1_set_to_1_1] true -> (bar_1'=1);
	[bar_1_set_to_0_2] true -> (bar_1'=0);
	[bar_1_set_to_1_2] true -> (bar_1'=1);
endmodule

module bar_1_shared
	bar_1_state : [someoneIsModified..someAreShared] init someoneIsModified;
	bar_1_who   : [empty..full] init empty;


	[bar_1_set_to_0_0] (bar_1_state =someoneIsModified   & bar_1_who =me_bit_0)          -> tick         : true;
	[bar_1_set_to_0_0] (bar_1_state =someoneDoesAtomicOp & bar_1_who =me_bit_0)          -> tick         : true;
	[bar_1_set_to_0_0] (bar_1_state =someoneIsModified   & bar_1_who!=me_bit_0)          -> write        : (bar_1_who'=me_bit_0);
	[bar_1_set_to_0_0] (bar_1_state =someAreShared)                                    -> write        : (bar_1_state'=someoneIsModified) & (bar_1_who'=me_bit_0);
	[bar_1_set_to_1_0] (bar_1_state =someoneIsModified   & bar_1_who =me_bit_0)          -> tick         : true;
	[bar_1_set_to_1_0] (bar_1_state =someoneDoesAtomicOp & bar_1_who =me_bit_0)          -> tick         : true;
	[bar_1_set_to_1_0] (bar_1_state =someoneIsModified   & bar_1_who!=me_bit_0)          -> write        : (bar_1_who'=me_bit_0);
	[bar_1_set_to_1_0] (bar_1_state =someAreShared)                                    -> write        : (bar_1_state'=someoneIsModified) & (bar_1_who'=me_bit_0);

	[bar_1_read_0] bar_1_state=someoneIsModified   & bar_1_who =me_bit_0                 -> tick         : true;
	[bar_1_read_0] bar_1_state=someoneDoesAtomicOp & bar_1_who =me_bit_0                 -> tick         : true;
	[bar_1_read_0] bar_1_state=someoneIsModified   & bar_1_who!=me_bit_0                 -> read         : (bar_1_state'=someAreShared) & (bar_1_who'=min(full,max(bar_1_who+me_bit_0, empty)));
	[bar_1_read_0] bar_1_state=someAreShared       & mod(floor(bar_1_who/me_bit_0),2)=1  -> tick         : true;
	[bar_1_read_0] bar_1_state=someAreShared       & mod(floor(bar_1_who/me_bit_0),2)=0  -> read         : (bar_1_who'=min(full,max(bar_1_who+me_bit_0, empty)));

	[bar_1_atomic_begin_0] (bar_1_state =someoneIsModified   & bar_1_who =me_bit_0)      -> tick         : (bar_1_state'=someoneDoesAtomicOp);
	[bar_1_atomic_begin_0] (bar_1_state =someoneIsModified   & bar_1_who!=me_bit_0)      -> atomic_begin : (bar_1_state'=someoneDoesAtomicOp) & (bar_1_who'=me_bit_0);
	[bar_1_atomic_begin_0] (bar_1_state =someAreShared)                                -> atomic_begin : (bar_1_state'=someoneDoesAtomicOp) & (bar_1_who'=me_bit_0);
	[bar_1_atomic_end_0]   (bar_1_state =someoneDoesAtomicOp & bar_1_who =me_bit_0)      -> tick         : (bar_1_state'=someoneIsModified);

	[bar_1_set_to_0_1] (bar_1_state =someoneIsModified   & bar_1_who =me_bit_1)          -> tick         : true;
	[bar_1_set_to_0_1] (bar_1_state =someoneDoesAtomicOp & bar_1_who =me_bit_1)          -> tick         : true;
	[bar_1_set_to_0_1] (bar_1_state =someoneIsModified   & bar_1_who!=me_bit_1)          -> write        : (bar_1_who'=me_bit_1);
	[bar_1_set_to_0_1] (bar_1_state =someAreShared)                                    -> write        : (bar_1_state'=someoneIsModified) & (bar_1_who'=me_bit_1);
	[bar_1_set_to_1_1] (bar_1_state =someoneIsModified   & bar_1_who =me_bit_1)          -> tick         : true;
	[bar_1_set_to_1_1] (bar_1_state =someoneDoesAtomicOp & bar_1_who =me_bit_1)          -> tick         : true;
	[bar_1_set_to_1_1] (bar_1_state =someoneIsModified   & bar_1_who!=me_bit_1)          -> write        : (bar_1_who'=me_bit_1);
	[bar_1_set_to_1_1] (bar_1_state =someAreShared)                                    -> write        : (bar_1_state'=someoneIsModified) & (bar_1_who'=me_bit_1);

	[bar_1_read_1] bar_1_state=someoneIsModified   & bar_1_who =me_bit_1                 -> tick         : true;
	[bar_1_read_1] bar_1_state=someoneDoesAtomicOp & bar_1_who =me_bit_1                 -> tick         : true;
	[bar_1_read_1] bar_1_state=someoneIsModified   & bar_1_who!=me_bit_1                 -> read         : (bar_1_state'=someAreShared) & (bar_1_who'=min(full,max(bar_1_who+me_bit_1, empty)));
	[bar_1_read_1] bar_1_state=someAreShared       & mod(floor(bar_1_who/me_bit_1),2)=1  -> tick         : true;
	[bar_1_read_1] bar_1_state=someAreShared       & mod(floor(bar_1_who/me_bit_1),2)=0  -> read         : (bar_1_who'=min(full,max(bar_1_who+me_bit_1, empty)));

	[bar_1_atomic_begin_1] (bar_1_state =someoneIsModified   & bar_1_who =me_bit_1)      -> tick         : (bar_1_state'=someoneDoesAtomicOp);
	[bar_1_atomic_begin_1] (bar_1_state =someoneIsModified   & bar_1_who!=me_bit_1)      -> atomic_begin : (bar_1_state'=someoneDoesAtomicOp) & (bar_1_who'=me_bit_1);
	[bar_1_atomic_begin_1] (bar_1_state =someAreShared)                                -> atomic_begin : (bar_1_state'=someoneDoesAtomicOp) & (bar_1_who'=me_bit_1);
	[bar_1_atomic_end_1]   (bar_1_state =someoneDoesAtomicOp & bar_1_who =me_bit_1)      -> tick         : (bar_1_state'=someoneIsModified);

	[bar_1_set_to_0_2] (bar_1_state =someoneIsModified   & bar_1_who =me_bit_2)          -> tick         : true;
	[bar_1_set_to_0_2] (bar_1_state =someoneDoesAtomicOp & bar_1_who =me_bit_2)          -> tick         : true;
	[bar_1_set_to_0_2] (bar_1_state =someoneIsModified   & bar_1_who!=me_bit_2)          -> write        : (bar_1_who'=me_bit_2);
	[bar_1_set_to_0_2] (bar_1_state =someAreShared)                                    -> write        : (bar_1_state'=someoneIsModified) & (bar_1_who'=me_bit_2);
	[bar_1_set_to_1_2] (bar_1_state =someoneIsModified   & bar_1_who =me_bit_2)          -> tick         : true;
	[bar_1_set_to_1_2] (bar_1_state =someoneDoesAtomicOp & bar_1_who =me_bit_2)          -> tick         : true;
	[bar_1_set_to_1_2] (bar_1_state =someoneIsModified   & bar_1_who!=me_bit_2)          -> write        : (bar_1_who'=me_bit_2);
	[bar_1_set_to_1_2] (bar_1_state =someAreShared)                                    -> write        : (bar_1_state'=someoneIsModified) & (bar_1_who'=me_bit_2);

	[bar_1_read_2] bar_1_state=someoneIsModified   & bar_1_who =me_bit_2                 -> tick         : true;
	[bar_1_read_2] bar_1_state=someoneDoesAtomicOp & bar_1_who =me_bit_2                 -> tick         : true;
	[bar_1_read_2] bar_1_state=someoneIsModified   & bar_1_who!=me_bit_2                 -> read         : (bar_1_state'=someAreShared) & (bar_1_who'=min(full,max(bar_1_who+me_bit_2, empty)));
	[bar_1_read_2] bar_1_state=someAreShared       & mod(floor(bar_1_who/me_bit_2),2)=1  -> tick         : true;
	[bar_1_read_2] bar_1_state=someAreShared       & mod(floor(bar_1_who/me_bit_2),2)=0  -> read         : (bar_1_who'=min(full,max(bar_1_who+me_bit_2, empty)));

	[bar_1_atomic_begin_2] (bar_1_state =someoneIsModified   & bar_1_who =me_bit_2)      -> tick         : (bar_1_state'=someoneDoesAtomicOp);
	[bar_1_atomic_begin_2] (bar_1_state =someoneIsModified   & bar_1_who!=me_bit_2)      -> atomic_begin : (bar_1_state'=someoneDoesAtomicOp) & (bar_1_who'=me_bit_2);
	[bar_1_atomic_begin_2] (bar_1_state =someAreShared)                                -> atomic_begin : (bar_1_state'=someoneDoesAtomicOp) & (bar_1_who'=me_bit_2);
	[bar_1_atomic_end_2]   (bar_1_state =someoneDoesAtomicOp & bar_1_who =me_bit_2)      -> tick         : (bar_1_state'=someoneIsModified);
endmodule

module bar_2_variable
	bar_2 : [0..1] init 0;
	[bar_2_set_to_0_0] true -> (bar_2'=0);
	[bar_2_set_to_1_0] true -> (bar_2'=1);
	[bar_2_set_to_0_1] true -> (bar_2'=0);
	[bar_2_set_to_1_1] true -> (bar_2'=1);
	[bar_2_set_to_0_2] true -> (bar_2'=0);
	[bar_2_set_to_1_2] true -> (bar_2'=1);
endmodule

module bar_2_shared
	bar_2_state : [someoneIsModified..someAreShared] init someoneIsModified;
	bar_2_who   : [empty..full] init empty;


	[bar_2_set_to_0_0] (bar_2_state =someoneIsModified   & bar_2_who =me_bit_0)          -> tick         : true;
	[bar_2_set_to_0_0] (bar_2_state =someoneDoesAtomicOp & bar_2_who =me_bit_0)          -> tick         : true;
	[bar_2_set_to_0_0] (bar_2_state =someoneIsModified   & bar_2_who!=me_bit_0)          -> write        : (bar_2_who'=me_bit_0);
	[bar_2_set_to_0_0] (bar_2_state =someAreShared)                                    -> write        : (bar_2_state'=someoneIsModified) & (bar_2_who'=me_bit_0);
	[bar_2_set_to_1_0] (bar_2_state =someoneIsModified   & bar_2_who =me_bit_0)          -> tick         : true;
	[bar_2_set_to_1_0] (bar_2_state =someoneDoesAtomicOp & bar_2_who =me_bit_0)          -> tick         : true;
	[bar_2_set_to_1_0] (bar_2_state =someoneIsModified   & bar_2_who!=me_bit_0)          -> write        : (bar_2_who'=me_bit_0);
	[bar_2_set_to_1_0] (bar_2_state =someAreShared)                                    -> write        : (bar_2_state'=someoneIsModified) & (bar_2_who'=me_bit_0);

	[bar_2_read_0] bar_2_state=someoneIsModified   & bar_2_who =me_bit_0                 -> tick         : true;
	[bar_2_read_0] bar_2_state=someoneDoesAtomicOp & bar_2_who =me_bit_0                 -> tick         : true;
	[bar_2_read_0] bar_2_state=someoneIsModified   & bar_2_who!=me_bit_0                 -> read         : (bar_2_state'=someAreShared) & (bar_2_who'=min(full,max(bar_2_who+me_bit_0, empty)));
	[bar_2_read_0] bar_2_state=someAreShared       & mod(floor(bar_2_who/me_bit_0),2)=1  -> tick         : true;
	[bar_2_read_0] bar_2_state=someAreShared       & mod(floor(bar_2_who/me_bit_0),2)=0  -> read         : (bar_2_who'=min(full,max(bar_2_who+me_bit_0, empty)));

	[bar_2_atomic_begin_0] (bar_2_state =someoneIsModified   & bar_2_who =me_bit_0)      -> tick         : (bar_2_state'=someoneDoesAtomicOp);
	[bar_2_atomic_begin_0] (bar_2_state =someoneIsModified   & bar_2_who!=me_bit_0)      -> atomic_begin : (bar_2_state'=someoneDoesAtomicOp) & (bar_2_who'=me_bit_0);
	[bar_2_atomic_begin_0] (bar_2_state =someAreShared)                                -> atomic_begin : (bar_2_state'=someoneDoesAtomicOp) & (bar_2_who'=me_bit_0);
	[bar_2_atomic_end_0]   (bar_2_state =someoneDoesAtomicOp & bar_2_who =me_bit_0)      -> tick         : (bar_2_state'=someoneIsModified);

	[bar_2_set_to_0_1] (bar_2_state =someoneIsModified   & bar_2_who =me_bit_1)          -> tick         : true;
	[bar_2_set_to_0_1] (bar_2_state =someoneDoesAtomicOp & bar_2_who =me_bit_1)          -> tick         : true;
	[bar_2_set_to_0_1] (bar_2_state =someoneIsModified   & bar_2_who!=me_bit_1)          -> write        : (bar_2_who'=me_bit_1);
	[bar_2_set_to_0_1] (bar_2_state =someAreShared)                                    -> write        : (bar_2_state'=someoneIsModified) & (bar_2_who'=me_bit_1);
	[bar_2_set_to_1_1] (bar_2_state =someoneIsModified   & bar_2_who =me_bit_1)          -> tick         : true;
	[bar_2_set_to_1_1] (bar_2_state =someoneDoesAtomicOp & bar_2_who =me_bit_1)          -> tick         : true;
	[bar_2_set_to_1_1] (bar_2_state =someoneIsModified   & bar_2_who!=me_bit_1)          -> write        : (bar_2_who'=me_bit_1);
	[bar_2_set_to_1_1] (bar_2_state =someAreShared)                                    -> write        : (bar_2_state'=someoneIsModified) & (bar_2_who'=me_bit_1);

	[bar_2_read_1] bar_2_state=someoneIsModified   & bar_2_who =me_bit_1                 -> tick         : true;
	[bar_2_read_1] bar_2_state=someoneDoesAtomicOp & bar_2_who =me_bit_1                 -> tick         : true;
	[bar_2_read_1] bar_2_state=someoneIsModified   & bar_2_who!=me_bit_1                 -> read         : (bar_2_state'=someAreShared) & (bar_2_who'=min(full,max(bar_2_who+me_bit_1, empty)));
	[bar_2_read_1] bar_2_state=someAreShared       & mod(floor(bar_2_who/me_bit_1),2)=1  -> tick         : true;
	[bar_2_read_1] bar_2_state=someAreShared       & mod(floor(bar_2_who/me_bit_1),2)=0  -> read         : (bar_2_who'=min(full,max(bar_2_who+me_bit_1, empty)));

	[bar_2_atomic_begin_1] (bar_2_state =someoneIsModified   & bar_2_who =me_bit_1)      -> tick         : (bar_2_state'=someoneDoesAtomicOp);
	[bar_2_atomic_begin_1] (bar_2_state =someoneIsModified   & bar_2_who!=me_bit_1)      -> atomic_begin : (bar_2_state'=someoneDoesAtomicOp) & (bar_2_who'=me_bit_1);
	[bar_2_atomic_begin_1] (bar_2_state =someAreShared)                                -> atomic_begin : (bar_2_state'=someoneDoesAtomicOp) & (bar_2_who'=me_bit_1);
	[bar_2_atomic_end_1]   (bar_2_state =someoneDoesAtomicOp & bar_2_who =me_bit_1)      -> tick         : (bar_2_state'=someoneIsModified);

	[bar_2_set_to_0_2] (bar_2_state =someoneIsModified   & bar_2_who =me_bit_2)          -> tick         : true;
	[bar_2_set_to_0_2] (bar_2_state =someoneDoesAtomicOp & bar_2_who =me_bit_2)          -> tick         : true;
	[bar_2_set_to_0_2] (bar_2_state =someoneIsModified   & bar_2_who!=me_bit_2)          -> write        : (bar_2_who'=me_bit_2);
	[bar_2_set_to_0_2] (bar_2_state =someAreShared)                                    -> write        : (bar_2_state'=someoneIsModified) & (bar_2_who'=me_bit_2);
	[bar_2_set_to_1_2] (bar_2_state =someoneIsModified   & bar_2_who =me_bit_2)          -> tick         : true;
	[bar_2_set_to_1_2] (bar_2_state =someoneDoesAtomicOp & bar_2_who =me_bit_2)          -> tick         : true;
	[bar_2_set_to_1_2] (bar_2_state =someoneIsModified   & bar_2_who!=me_bit_2)          -> write        : (bar_2_who'=me_bit_2);
	[bar_2_set_to_1_2] (bar_2_state =someAreShared)                                    -> write        : (bar_2_state'=someoneIsModified) & (bar_2_who'=me_bit_2);

	[bar_2_read_2] bar_2_state=someoneIsModified   & bar_2_who =me_bit_2                 -> tick         : true;
	[bar_2_read_2] bar_2_state=someoneDoesAtomicOp & bar_2_who =me_bit_2                 -> tick         : true;
	[bar_2_read_2] bar_2_state=someoneIsModified   & bar_2_who!=me_bit_2                 -> read         : (bar_2_state'=someAreShared) & (bar_2_who'=min(full,max(bar_2_who+me_bit_2, empty)));
	[bar_2_read_2] bar_2_state=someAreShared       & mod(floor(bar_2_who/me_bit_2),2)=1  -> tick         : true;
	[bar_2_read_2] bar_2_state=someAreShared       & mod(floor(bar_2_who/me_bit_2),2)=0  -> read         : (bar_2_who'=min(full,max(bar_2_who+me_bit_2, empty)));

	[bar_2_atomic_begin_2] (bar_2_state =someoneIsModified   & bar_2_who =me_bit_2)      -> tick         : (bar_2_state'=someoneDoesAtomicOp);
	[bar_2_atomic_begin_2] (bar_2_state =someoneIsModified   & bar_2_who!=me_bit_2)      -> atomic_begin : (bar_2_state'=someoneDoesAtomicOp) & (bar_2_who'=me_bit_2);
	[bar_2_atomic_begin_2] (bar_2_state =someAreShared)                                -> atomic_begin : (bar_2_state'=someoneDoesAtomicOp) & (bar_2_who'=me_bit_2);
	[bar_2_atomic_end_2]   (bar_2_state =someoneDoesAtomicOp & bar_2_who =me_bit_2)      -> tick         : (bar_2_state'=someoneIsModified);
endmodule


// *** shared memory end ***

// *** thread copies begin ***

module thread_1
    l_1 : [l_init..l_done] init l_init;
    i_1 : [0..thread_count] init 0;

    [work_1]                      l_1=l_work                        -> work : (l_1'=l_write);

    [bar_1_set_to_1_1]            l_1=l_write                       ->        (l_1'=l_wait);

    [does_i_equal_thread_count_1] l_1=l_wait  & i_1 = thread_count  -> tick : (l_1'=l_done);
    [bar_0_read_1]                l_1=l_wait  & i_1 = 0 & bar_0 = 1 ->        (i_1' = min(i_1 + 1, thread_count));
    [bar_0_read_1]                l_1=l_wait  & i_1 = 0 & bar_0 = 0 ->        (i_1' = 0);
    [bar_1_read_1]                l_1=l_wait  & i_1 = 1 & bar_1 = 1 ->        (i_1' = min(i_1 + 1, thread_count));
    [bar_1_read_1]                l_1=l_wait  & i_1 = 1 & bar_1 = 0 ->        (i_1' = 0);
    [bar_2_read_1]                l_1=l_wait  & i_1 = 2 & bar_2 = 1 ->        (i_1' = min(i_1 + 1, thread_count));
    [bar_2_read_1]                l_1=l_wait  & i_1 = 2 & bar_2 = 0 ->        (i_1' = 0);

    [done_1]                      l_1=l_done                        ->        true;

    // do never trigger the following sync transitions
    [bar_0_atomic_begin_1] false -> true;
    [bar_0_atomic_end_1]   false -> true;
    [bar_0_set_to_0_1]     false -> true;
    [bar_0_set_to_1_1]     false -> true;
    [bar_1_atomic_begin_1] false -> true;
    [bar_1_atomic_end_1]   false -> true;
    [bar_1_set_to_0_1]     false -> true;
    [bar_2_atomic_begin_1] false -> true;
    [bar_2_atomic_end_1]   false -> true;
    [bar_2_set_to_0_1]     false -> true;
    [bar_2_set_to_1_1]     false -> true;

endmodule

module thread_2
    l_2 : [l_init..l_done] init l_init;
    i_2 : [0..thread_count] init 0;

    [work_2]                      l_2=l_work                        -> work : (l_2'=l_write);

    [bar_2_set_to_1_2]            l_2=l_write                       ->        (l_2'=l_wait);

    [does_i_equal_thread_count_2] l_2=l_wait  & i_2 = thread_count  -> tick : (l_2'=l_done);
    [bar_0_read_2]                l_2=l_wait  & i_2 = 0 & bar_0 = 1 ->        (i_2' = min(i_2 + 1, thread_count));
    [bar_0_read_2]                l_2=l_wait  & i_2 = 0 & bar_0 = 0 ->        (i_2' = 0);
    [bar_1_read_2]                l_2=l_wait  & i_2 = 1 & bar_1 = 1 ->        (i_2' = min(i_2 + 1, thread_count));
    [bar_1_read_2]                l_2=l_wait  & i_2 = 1 & bar_1 = 0 ->        (i_2' = 0);
    [bar_2_read_2]                l_2=l_wait  & i_2 = 2 & bar_2 = 1 ->        (i_2' = min(i_2 + 1, thread_count));
    [bar_2_read_2]                l_2=l_wait  & i_2 = 2 & bar_2 = 0 ->        (i_2' = 0);

    [done_2]                      l_2=l_done                        ->        true;

    // do never trigger the following sync transitions
    [bar_0_atomic_begin_2] false -> true;
    [bar_0_atomic_end_2]   false -> true;
    [bar_0_set_to_0_2]     false -> true;
    [bar_0_set_to_1_2]     false -> true;
    [bar_1_atomic_begin_2] false -> true;
    [bar_1_atomic_end_2]   false -> true;
    [bar_1_set_to_0_2]     false -> true;
    [bar_1_set_to_1_2]     false -> true;
    [bar_2_atomic_begin_2] false -> true;
    [bar_2_atomic_end_2]   false -> true;
    [bar_2_set_to_0_2]     false -> true;

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

