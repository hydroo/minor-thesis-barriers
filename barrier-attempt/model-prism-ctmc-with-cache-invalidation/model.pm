ctmc

const int me_1 = 1; //index
const int me_2 = 2;
const int me_3 = 3;

const int me_bit_1 = 1; //2^0
const int me_bit_2 = 2; //2^1
const int me_bit_3 = 4; //2^2

const int empty = 0;
const int full  = me_bit_1 + me_bit_2 + me_bit_3;

const int modified = 0;
const int shared   = 1;
const int invalid  = 2;


const int work_ticks = 1000;
const int read_ticks = 50;
const int write_ticks = 100;


const double base_rate = 2500.0;
const double tick      = base_rate / 1.0;
const double work      = tick / work_ticks;
const double read      = tick / read_ticks;
const double write     = tick / write_ticks;


module process_1
	l_1 : [0..11] init 0;
	cp_1 : [empty..full] init empty;
	mesi_1 : [0..2] init invalid;
	exit_1 : [empty..full] init empty;
	entry_1 : [empty..full] init empty;
	left_1 : bool init false;

	//process
	[read_1]  l_1=0 & mesi_1 =invalid -> read : (l_1'=1) & (cp_1'=entry_1) & (mesi_1'=shared);
	[read_1]  l_1=0 & mesi_1!=invalid -> tick : (l_1'=1) & (cp_1'=entry_1);

	[]        l_1=1 & mod(floor(cp_1/me_bit_1),2)=1 -> tick : (l_1'=2);

	[set_entry_1_23] l_1=1 & mesi_1!=modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=1-me_bit_1 -> write : (l_1'=2) & (entry_1'=1) & (mesi_1'=modified); //5
	[set_entry_1_23] l_1=1 & mesi_1 =modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=1-me_bit_1 -> tick  : (l_1'=2) & (entry_1'=1);
	[set_entry_2_23] l_1=1 & mesi_1!=modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=2-me_bit_1 -> write : (l_1'=2) & (entry_1'=2) & (mesi_1'=modified);
	[set_entry_2_23] l_1=1 & mesi_1 =modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=2-me_bit_1 -> tick  : (l_1'=2) & (entry_1'=2);
	[set_entry_3_23] l_1=1 & mesi_1!=modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=3-me_bit_1 -> write : (l_1'=2) & (entry_1'=3) & (mesi_1'=modified);
	[set_entry_3_23] l_1=1 & mesi_1 =modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=3-me_bit_1 -> tick  : (l_1'=2) & (entry_1'=3);
	[set_entry_4_23] l_1=1 & mesi_1!=modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=4-me_bit_1 -> write : (l_1'=2) & (entry_1'=4) & (mesi_1'=modified);
	[set_entry_4_23] l_1=1 & mesi_1 =modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=4-me_bit_1 -> tick  : (l_1'=2) & (entry_1'=4);
	[set_entry_5_23] l_1=1 & mesi_1!=modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=5-me_bit_1 -> write : (l_1'=2) & (entry_1'=5) & (mesi_1'=modified);
	[set_entry_5_23] l_1=1 & mesi_1 =modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=5-me_bit_1 -> tick  : (l_1'=2) & (entry_1'=5);
	[set_entry_6_23] l_1=1 & mesi_1!=modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=6-me_bit_1 -> write : (l_1'=2) & (entry_1'=6) & (mesi_1'=modified); //15
	[set_entry_6_23] l_1=1 & mesi_1 =modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=6-me_bit_1 -> tick  : (l_1'=2) & (entry_1'=6);
	[set_entry_7_23] l_1=1 & mesi_1!=modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=7-me_bit_1 -> write : (l_1'=2) & (entry_1'=7) & (mesi_1'=modified);
	[set_entry_7_23] l_1=1 & mesi_1 =modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=7-me_bit_1 -> tick  : (l_1'=2) & (entry_1'=7);

	[read_1]  l_1=2 & mesi_1 =invalid & (  cp_1 != full & left_1 = false ) -> read : (l_1'=0) & (mesi_1'=shared);
	[read_1]  l_1=2 & mesi_1!=invalid & (  cp_1 != full & left_1 = false ) -> tick : (l_1'=0);
	[read_1]  l_1=2 & mesi_1 =invalid & (!(cp_1 != full & left_1 = false)) -> read : (l_1'=3) & (mesi_1'=shared);
	[read_1]  l_1=2 & mesi_1!=invalid & (!(cp_1 != full & left_1 = false)) -> tick : (l_1'=3);

	[set_exit_0_23]    l_1=3 & mesi_1!=modified -> write : (l_1'=4) & (exit_1'=empty) & (mesi_1'=modified);
	[set_exit_0_23]    l_1=3 & mesi_1 =modified -> tick  : (l_1'=4) & (exit_1'=empty);
	[set_left_true_23] l_1=4 & mesi_1!=modified -> write : (left_1'=true) & (l_1'=5)  & (mesi_1'=modified);
	[set_left_true_23] l_1=4 & mesi_1 =modified -> tick  : (left_1'=true) & (l_1'=5);


	[]        l_1=5 -> work : (l_1'=6);


	[read_1]  l_1=6 & mesi_1 =invalid -> read : (l_1'=7) & (cp_1'=exit_1) & (mesi_1'=shared);
	[read_1]  l_1=6 & mesi_1!=invalid -> tick : (l_1'=7) & (cp_1'=exit_1);
	[]        l_1=7 & mod(floor(cp_1/me_bit_1),2)=1 -> tick : (l_1'=8);

	[set_exit_1_23] l_1=7 & mesi_1!=modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=1-me_bit_1 -> write : (l_1'=8) & (exit_1'=1) & (mesi_1'=modified);
	[set_exit_1_23] l_1=7 & mesi_1 =modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=1-me_bit_1 -> tick  : (l_1'=8) & (exit_1'=1);
	[set_exit_2_23] l_1=7 & mesi_1!=modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=2-me_bit_1 -> write : (l_1'=8) & (exit_1'=2) & (mesi_1'=modified);
	[set_exit_2_23] l_1=7 & mesi_1 =modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=2-me_bit_1 -> tick  : (l_1'=8) & (exit_1'=2);
	[set_exit_3_23] l_1=7 & mesi_1!=modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=3-me_bit_1 -> write : (l_1'=8) & (exit_1'=3) & (mesi_1'=modified);
	[set_exit_3_23] l_1=7 & mesi_1 =modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=3-me_bit_1 -> tick  : (l_1'=8) & (exit_1'=3);
	[set_exit_4_23] l_1=7 & mesi_1!=modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=4-me_bit_1 -> write : (l_1'=8) & (exit_1'=4) & (mesi_1'=modified);
	[set_exit_4_23] l_1=7 & mesi_1 =modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=4-me_bit_1 -> tick  : (l_1'=8) & (exit_1'=4);
	[set_exit_5_23] l_1=7 & mesi_1!=modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=5-me_bit_1 -> write : (l_1'=8) & (exit_1'=5) & (mesi_1'=modified);
	[set_exit_5_23] l_1=7 & mesi_1 =modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=5-me_bit_1 -> tick  : (l_1'=8) & (exit_1'=5);
	[set_exit_6_23] l_1=7 & mesi_1!=modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=6-me_bit_1 -> write : (l_1'=8) & (exit_1'=6) & (mesi_1'=modified);
	[set_exit_6_23] l_1=7 & mesi_1 =modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=6-me_bit_1 -> tick  : (l_1'=8) & (exit_1'=6);
	[set_exit_7_23] l_1=7 & mesi_1!=modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=7-me_bit_1 -> write : (l_1'=8) & (exit_1'=7) & (mesi_1'=modified);
	[set_exit_7_23] l_1=7 & mesi_1 =modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=7-me_bit_1 -> tick  : (l_1'=8) & (exit_1'=7);

	[read_1]  l_1=8 & mesi_1 =invalid & (  cp_1 != full & left_1 = true ) -> read : (l_1'=6) & (mesi_1'=shared);
	[read_1]  l_1=8 & mesi_1!=invalid & (  cp_1 != full & left_1 = true ) -> tick : (l_1'=6);
	[read_1]  l_1=8 & mesi_1 =invalid & (!(cp_1 != full & left_1 = true)) -> read : (l_1'=9) & (mesi_1'=shared);
	[read_1]  l_1=8 & mesi_1!=invalid & (!(cp_1 != full & left_1 = true)) -> tick : (l_1'=9);
	[set_entry_0_23]    l_1=9  & mesi_1!=modified -> write : (l_1'=10) & (entry_1'=empty) & (mesi_1'=modified);
	[set_entry_0_23]    l_1=9  & mesi_1 =modified -> tick  : (l_1'=10) & (entry_1'=empty);
	[set_left_false_23] l_1=10 & mesi_1!=modified -> write : (l_1'=11) & (left_1'=false)  & (mesi_1'=modified);
	[set_left_false_23] l_1=10 & mesi_1 =modified -> tick  : (l_1'=11) & (left_1'=false);


	[]        l_1=11 -> work : (l_1'=0);

	//cacheline
	[read_2]  mesi_1=invalid  -> (mesi_1'=invalid);
	[read_3]  mesi_1=invalid  -> (mesi_1'=invalid);

	[read_2]  mesi_1=shared   -> (mesi_1'=shared);
	[read_3]  mesi_1=shared   -> (mesi_1'=shared);

	[read_2]  mesi_1=modified -> (mesi_1'=shared);
	[read_3]  mesi_1=modified -> (mesi_1'=shared);

	[set_left_false_12]  true -> (left_1'=false)  & (mesi_1'=invalid);
	[set_left_false_13]  true -> (left_1'=false)  & (mesi_1'=invalid);
	[set_left_true_12]   true -> (left_1'=true)   & (mesi_1'=invalid);
	[set_left_true_13]   true -> (left_1'=true)   & (mesi_1'=invalid);

	[set_entry_0_12]     true -> (entry_1'=empty) & (mesi_1'=invalid);
	[set_entry_0_13]     true -> (entry_1'=empty) & (mesi_1'=invalid);
	[set_entry_1_12]     true -> (entry_1'=1)     & (mesi_1'=invalid);
	[set_entry_1_13]     true -> (entry_1'=1)     & (mesi_1'=invalid);
	[set_entry_2_12]     true -> (entry_1'=2)     & (mesi_1'=invalid);
	[set_entry_2_13]     true -> (entry_1'=2)     & (mesi_1'=invalid);
	[set_entry_3_12]     true -> (entry_1'=3)     & (mesi_1'=invalid);
	[set_entry_3_13]     true -> (entry_1'=3)     & (mesi_1'=invalid);
	[set_entry_4_12]     true -> (entry_1'=4)     & (mesi_1'=invalid);
	[set_entry_4_13]     true -> (entry_1'=4)     & (mesi_1'=invalid);
	[set_entry_5_12]     true -> (entry_1'=5)     & (mesi_1'=invalid);
	[set_entry_5_13]     true -> (entry_1'=5)     & (mesi_1'=invalid);
	[set_entry_6_12]     true -> (entry_1'=6)     & (mesi_1'=invalid);
	[set_entry_6_13]     true -> (entry_1'=6)     & (mesi_1'=invalid);
	[set_entry_7_12]     true -> (entry_1'=full)  & (mesi_1'=invalid);
	[set_entry_7_13]     true -> (entry_1'=full)  & (mesi_1'=invalid);

	[set_exit_0_12]      true -> (exit_1'=empty)  & (mesi_1'=invalid);
	[set_exit_0_13]      true -> (exit_1'=empty)  & (mesi_1'=invalid);
	[set_exit_1_12]      true -> (exit_1'=1)      & (mesi_1'=invalid);
	[set_exit_1_13]      true -> (exit_1'=1)      & (mesi_1'=invalid);
	[set_exit_2_12]      true -> (exit_1'=2)      & (mesi_1'=invalid);
	[set_exit_2_13]      true -> (exit_1'=2)      & (mesi_1'=invalid);
	[set_exit_3_12]      true -> (exit_1'=3)      & (mesi_1'=invalid);
	[set_exit_3_13]      true -> (exit_1'=3)      & (mesi_1'=invalid);
	[set_exit_4_12]      true -> (exit_1'=4)      & (mesi_1'=invalid);
	[set_exit_4_13]      true -> (exit_1'=4)      & (mesi_1'=invalid);
	[set_exit_5_12]      true -> (exit_1'=5)      & (mesi_1'=invalid);
	[set_exit_5_13]      true -> (exit_1'=5)      & (mesi_1'=invalid);
	[set_exit_6_12]      true -> (exit_1'=6)      & (mesi_1'=invalid);
	[set_exit_6_13]      true -> (exit_1'=6)      & (mesi_1'=invalid);
	[set_exit_7_12]      true -> (exit_1'=full)   & (mesi_1'=invalid);
	[set_exit_7_13]      true -> (exit_1'=full)   & (mesi_1'=invalid);
endmodule

module process_2 = process_1 [
	me_1              =me_2,
	me_bit_1          =me_bit_2,
	l_1               =l_2,
	cp_1              =cp_2,
	exit_1            =exit_2,
	entry_1           =entry_2,
	left_1            =left_2,
	mesi_1            =mesi_2,
	read_1            =read_2,
	read_2            =read_1,
	write_1           =write_2,
	write_2           =write_1,
	set_left_false_12 =set_left_false_12,
	set_left_false_13 =set_left_false_23,
	set_left_false_23 =set_left_false_13,
	set_left_true_12  =set_left_true_12,
	set_left_true_13  =set_left_true_23,
	set_left_true_23  =set_left_true_13,
	set_entry_0_12    =set_entry_0_12,
	set_entry_0_13    =set_entry_0_23,
	set_entry_0_23    =set_entry_0_13,
	set_entry_1_12    =set_entry_1_12,
	set_entry_1_13    =set_entry_1_23,
	set_entry_1_23    =set_entry_1_13,
	set_entry_2_12    =set_entry_2_12,
	set_entry_2_13    =set_entry_2_23,
	set_entry_2_23    =set_entry_2_13,
	set_entry_3_12    =set_entry_3_12,
	set_entry_3_13    =set_entry_3_23,
	set_entry_3_23    =set_entry_3_13,
	set_entry_4_12    =set_entry_4_12,
	set_entry_4_13    =set_entry_4_23,
	set_entry_4_23    =set_entry_4_13,
	set_entry_5_12    =set_entry_5_12,
	set_entry_5_13    =set_entry_5_23,
	set_entry_5_23    =set_entry_5_13,
	set_entry_6_12    =set_entry_6_12,
	set_entry_6_13    =set_entry_6_23,
	set_entry_6_23    =set_entry_6_13,
	set_entry_7_12    =set_entry_7_12,
	set_entry_7_13    =set_entry_7_23,
	set_entry_7_23    =set_entry_7_13,
	set_exit_0_12     =set_exit_0_12,
	set_exit_0_13     =set_exit_0_23,
	set_exit_0_23     =set_exit_0_13,
	set_exit_1_12     =set_exit_1_12,
	set_exit_1_13     =set_exit_1_23,
	set_exit_1_23     =set_exit_1_13,
	set_exit_2_12     =set_exit_2_12,
	set_exit_2_13     =set_exit_2_23,
	set_exit_2_23     =set_exit_2_13,
	set_exit_3_12     =set_exit_3_12,
	set_exit_3_13     =set_exit_3_23,
	set_exit_3_23     =set_exit_3_13,
	set_exit_4_12     =set_exit_4_12,
	set_exit_4_13     =set_exit_4_23,
	set_exit_4_23     =set_exit_4_13,
	set_exit_5_12     =set_exit_5_12,
	set_exit_5_13     =set_exit_5_23,
	set_exit_5_23     =set_exit_5_13,
	set_exit_6_12     =set_exit_6_12,
	set_exit_6_13     =set_exit_6_23,
	set_exit_6_23     =set_exit_6_13,
	set_exit_7_12     =set_exit_7_12,
	set_exit_7_13     =set_exit_7_23,
	set_exit_7_23     =set_exit_7_13
] endmodule

module process_3 = process_1 [
	me_1              =me_3,
	me_bit_1          =me_bit_3,
	l_1               =l_3,
	cp_1              =cp_3,
	exit_1            =exit_3,
	entry_1           =entry_3,
	left_1            =left_3,
	mesi_1            =mesi_3,
	read_1            =read_3,
	read_3            =read_1,
	write_1           =write_3,
	write_3           =write_1,
	set_left_false_12 =set_left_false_13,
	set_left_false_13 =set_left_false_23,
	set_left_false_23 =set_left_false_12,
	set_left_true_12  =set_left_true_13,
	set_left_true_13  =set_left_true_23,
	set_left_true_23  =set_left_true_12,
	set_entry_0_12    =set_entry_0_23,
	set_entry_0_13    =set_entry_0_13,
	set_entry_0_23    =set_entry_0_12,
	set_entry_1_12    =set_entry_1_23,
	set_entry_1_13    =set_entry_1_13,
	set_entry_1_23    =set_entry_1_12,
	set_entry_2_12    =set_entry_2_23,
	set_entry_2_13    =set_entry_2_13,
	set_entry_2_23    =set_entry_2_12,
	set_entry_3_12    =set_entry_3_23,
	set_entry_3_13    =set_entry_3_13,
	set_entry_3_23    =set_entry_3_12,
	set_entry_4_12    =set_entry_4_23,
	set_entry_4_13    =set_entry_4_13,
	set_entry_4_23    =set_entry_4_12,
	set_entry_5_12    =set_entry_5_23,
	set_entry_5_13    =set_entry_5_13,
	set_entry_5_23    =set_entry_5_12,
	set_entry_6_12    =set_entry_6_23,
	set_entry_6_13    =set_entry_6_13,
	set_entry_6_23    =set_entry_6_12,
	set_entry_7_12    =set_entry_7_23,
	set_entry_7_13    =set_entry_7_13,
	set_entry_7_23    =set_entry_7_12,
	set_exit_0_12     =set_exit_0_23,
	set_exit_0_13     =set_exit_0_13,
	set_exit_0_23     =set_exit_0_12,
	set_exit_1_12     =set_exit_1_23,
	set_exit_1_13     =set_exit_1_13,
	set_exit_1_23     =set_exit_1_12,
	set_exit_2_12     =set_exit_2_23,
	set_exit_2_13     =set_exit_2_13,
	set_exit_2_23     =set_exit_2_12,
	set_exit_3_12     =set_exit_3_23,
	set_exit_3_13     =set_exit_3_13,
	set_exit_3_23     =set_exit_3_12,
	set_exit_4_12     =set_exit_4_23,
	set_exit_4_13     =set_exit_4_13,
	set_exit_4_23     =set_exit_4_12,
	set_exit_5_12     =set_exit_5_23,
	set_exit_5_13     =set_exit_5_13,
	set_exit_5_23     =set_exit_5_12,
	set_exit_6_12     =set_exit_6_23,
	set_exit_6_13     =set_exit_6_13,
	set_exit_6_23     =set_exit_6_12,
	set_exit_7_12     =set_exit_7_23,
	set_exit_7_13     =set_exit_7_13,
	set_exit_7_23     =set_exit_7_12
] endmodule


label "modified_1" = mesi_1=modified;
label "shared_1"   = mesi_1=shared;
label "invalid_1"  = mesi_1=invalid;

label "modified_2" = mesi_2=modified;
label "shared_2"   = mesi_2=shared;
label "invalid_2"  = mesi_2=invalid;

label "modified_3" = mesi_3=modified;
label "shared_3"   = mesi_3=shared;
label "invalid_3"  = mesi_3=invalid;

