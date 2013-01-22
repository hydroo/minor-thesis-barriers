ctmc

const int me_1 = 1; //index
const int me_2 = 2;

const int me_bit_1 = 1; //2^0
const int me_bit_2 = 2; //2^1

const int empty = 0;
const int full  = me_bit_1 + me_bit_2;

const int modified = 0;
const int shared   = 1;
const int invalid  = 2;


const double base_rate = 2500.0;
const double tick      = base_rate / 1.0;
const double work      = base_rate / 1000.0;
const double read      = base_rate / 50.0;
const double write     = base_rate / 100.0;


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

	[set_entry_1_2] l_1=1 & mesi_1!=modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=1-me_bit_1 -> write : (l_1'=2) & (entry_1'=1) & (mesi_1'=modified); //5
	[set_entry_1_2] l_1=1 & mesi_1 =modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=1-me_bit_1 -> tick  : (l_1'=2) & (entry_1'=1);
	[set_entry_2_2] l_1=1 & mesi_1!=modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=2-me_bit_1 -> write : (l_1'=2) & (entry_1'=2) & (mesi_1'=modified);
	[set_entry_2_2] l_1=1 & mesi_1 =modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=2-me_bit_1 -> tick  : (l_1'=2) & (entry_1'=2);
	[set_entry_3_2] l_1=1 & mesi_1!=modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=3-me_bit_1 -> write : (l_1'=2) & (entry_1'=3) & (mesi_1'=modified);
	[set_entry_3_2] l_1=1 & mesi_1 =modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=3-me_bit_1 -> tick  : (l_1'=2) & (entry_1'=3);

	[read_1]  l_1=2 & mesi_1 =invalid & (  cp_1 != full & left_1 = false ) -> read : (l_1'=0) & (mesi_1'=shared);
	[read_1]  l_1=2 & mesi_1!=invalid & (  cp_1 != full & left_1 = false ) -> tick : (l_1'=0);
	[read_1]  l_1=2 & mesi_1 =invalid & (!(cp_1 != full & left_1 = false)) -> read : (l_1'=3) & (mesi_1'=shared);
	[read_1]  l_1=2 & mesi_1!=invalid & (!(cp_1 != full & left_1 = false)) -> tick : (l_1'=3);

	[set_exit_0_2]    l_1=3 & mesi_1!=modified -> write : (l_1'=4) & (exit_1'=empty) & (mesi_1'=modified);
	[set_exit_0_2]    l_1=3 & mesi_1 =modified -> tick  : (l_1'=4) & (exit_1'=empty);
	[set_left_true_2] l_1=4 & mesi_1!=modified -> write : (left_1'=true) & (l_1'=5)  & (mesi_1'=modified);
	[set_left_true_2] l_1=4 & mesi_1 =modified -> tick  : (left_1'=true) & (l_1'=5);


	[]        l_1=5 -> work : (l_1'=6);


	[read_1]  l_1=6 & mesi_1 =invalid -> read : (l_1'=7) & (cp_1'=exit_1) & (mesi_1'=shared);
	[read_1]  l_1=6 & mesi_1!=invalid -> tick : (l_1'=7) & (cp_1'=exit_1);
	[]        l_1=7 & mod(floor(cp_1/me_bit_1),2)=1 -> tick : (l_1'=8);

	[set_exit_1_2] l_1=7 & mesi_1!=modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=1-me_bit_1 -> write : (l_1'=8) & (exit_1'=1) & (mesi_1'=modified);
	[set_exit_1_2] l_1=7 & mesi_1 =modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=1-me_bit_1 -> tick  : (l_1'=8) & (exit_1'=1);
	[set_exit_2_2] l_1=7 & mesi_1!=modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=2-me_bit_1 -> write : (l_1'=8) & (exit_1'=2) & (mesi_1'=modified);
	[set_exit_2_2] l_1=7 & mesi_1 =modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=2-me_bit_1 -> tick  : (l_1'=8) & (exit_1'=2);
	[set_exit_3_2] l_1=7 & mesi_1!=modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=3-me_bit_1 -> write : (l_1'=8) & (exit_1'=3) & (mesi_1'=modified);
	[set_exit_3_2] l_1=7 & mesi_1 =modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=3-me_bit_1 -> tick  : (l_1'=8) & (exit_1'=3);

	[read_1]  l_1=8 & mesi_1 =invalid & (  cp_1 != full & left_1 = true ) -> read : (l_1'=6) & (mesi_1'=shared);
	[read_1]  l_1=8 & mesi_1!=invalid & (  cp_1 != full & left_1 = true ) -> tick : (l_1'=6);
	[read_1]  l_1=8 & mesi_1 =invalid & (!(cp_1 != full & left_1 = true)) -> read : (l_1'=9) & (mesi_1'=shared);
	[read_1]  l_1=8 & mesi_1!=invalid & (!(cp_1 != full & left_1 = true)) -> tick : (l_1'=9);
	[set_entry_0_2]    l_1=9  & mesi_1!=modified -> write : (l_1'=10) & (entry_1'=empty) & (mesi_1'=modified);
	[set_entry_0_2]    l_1=9  & mesi_1 =modified -> tick  : (l_1'=10) & (entry_1'=empty);
	[set_left_false_2] l_1=10 & mesi_1!=modified -> write : (l_1'=11) & (left_1'=false)  & (mesi_1'=modified);
	[set_left_false_2] l_1=10 & mesi_1 =modified -> tick  : (l_1'=11) & (left_1'=false);


	[]        l_1=11 -> work : (l_1'=0);

	//cacheline
	[read_2] mesi_1=invalid  -> (mesi_1'=invalid);

	[read_2] mesi_1=shared   -> (mesi_1'=shared);

	[read_2] mesi_1=modified -> (mesi_1'=shared);

	[set_left_false_1]  true -> (left_1'=false)  & (mesi_1'=invalid);
	[set_left_true_1]   true -> (left_1'=true)   & (mesi_1'=invalid);

	[set_entry_0_1]     true -> (entry_1'=empty) & (mesi_1'=invalid);
	[set_entry_1_1]     true -> (entry_1'=1)     & (mesi_1'=invalid);
	[set_entry_2_1]     true -> (entry_1'=2)     & (mesi_1'=invalid);
	[set_entry_3_1]     true -> (entry_1'=full)  & (mesi_1'=invalid);

	[set_exit_0_1]      true -> (exit_1'=empty)  & (mesi_1'=invalid);
	[set_exit_1_1]      true -> (exit_1'=1)      & (mesi_1'=invalid);
	[set_exit_2_1]      true -> (exit_1'=2)      & (mesi_1'=invalid);
	[set_exit_3_1]      true -> (exit_1'=full)   & (mesi_1'=invalid);
endmodule

module process_2 = process_1 [
	me_1             =me_2,
	me_bit_1         =me_bit_2,
	l_1              =l_2,
	cp_1             =cp_2,
	exit_1           =exit_2,
	entry_1          =entry_2,
	left_1           =left_2,
	mesi_1           =mesi_2,
	read_1           =read_2,
	read_2           =read_1,
	write_1          =write_2,
	write_2          =write_1,
	set_left_false_1 =set_left_false_2,
	set_left_false_2 =set_left_false_1,
	set_left_true_1  =set_left_true_2,
	set_left_true_2  =set_left_true_1,
	set_entry_0_1    =set_entry_0_2,
	set_entry_0_2    =set_entry_0_1,
	set_entry_1_1    =set_entry_1_2,
	set_entry_1_2    =set_entry_1_1,
	set_entry_2_1    =set_entry_2_2,
	set_entry_2_2    =set_entry_2_1,
	set_entry_3_1    =set_entry_3_2,
	set_entry_3_2    =set_entry_3_1,
	set_exit_0_1     =set_exit_0_2,
	set_exit_0_2     =set_exit_0_1,
	set_exit_1_1     =set_exit_1_2,
	set_exit_1_2     =set_exit_1_1,
	set_exit_2_1     =set_exit_2_2,
	set_exit_2_2     =set_exit_2_1,
	set_exit_3_1     =set_exit_3_2,
	set_exit_3_2     =set_exit_3_1
] endmodule


label "modified_1" = mesi_1=modified;
label "shared_1"   = mesi_1=shared;
label "invalid_1"  = mesi_1=invalid;

label "modified_2" = mesi_2=modified;
label "shared_2"   = mesi_2=shared;
label "invalid_2"  = mesi_2=invalid;

