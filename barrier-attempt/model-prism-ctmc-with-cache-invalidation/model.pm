ctmc

const me_1 = 1; //index
const me_2 = 2;
const me_3 = 3;

const me_bit_1 = 1; //2^0
const me_bit_2 = 2; //2^1
const me_bit_3 = 4; //2^2

const empty = 0;
const full = me_bit_1 + me_bit_2 + me_bit_3;
//const full = me_bit_1 + me_bit_2;

const min_invalid = empty - 1;
const max_invalid = full + 1;

const modified = 0;
const shared = 1;
const invalid = 2;

global exit : [min_invalid..max_invalid] init empty;
global entry : [min_invalid..max_invalid] init empty;



formula base_rate  = 2500.0;
formula micro      = base_rate * 100.0; //used for intermediate transitions that should fire very quickly
formula tick       = base_rate / 1.0;
formula work       = base_rate / 1000.0;
formula read       = base_rate / 50.0;
formula write      = base_rate / 100.0;



module process_1
	l_1 : [0..17] init 0;
	cp_1 : [min_invalid..max_invalid] init empty;
	left_1 : bool init false;
	mesi_1 : [0..2] init invalid;

	//process
	[read_1]  l_1=0 & mesi_1 =invalid -> read : (l_1'=1) & (cp_1'=entry) & (mesi_1'=shared);
	[read_1]  l_1=0 & mesi_1!=invalid -> tick : (l_1'=1) & (cp_1'=entry);

	[]        l_1=1 & mod(floor(cp_1/me_bit_1),2)=1 -> tick : (l_1'=3);
	[write_1] l_1=1 & mesi_1!=modified & mod(floor(cp_1/me_bit_1),2)=0 -> write : (l_1'=2) & (mesi_1'=modified);
	[write_1] l_1=1 & mesi_1 =modified & mod(floor(cp_1/me_bit_1),2)=0 -> tick  : (l_1'=2);
	[]        l_1=2 -> micro : (l_1'=3) & (entry'=min(max_invalid,max(cp_1+me_bit_1, min_invalid)));

	[read_1]  l_1=3 & mesi_1 =invalid & (  cp_1 != full & left_1 = false ) -> read : (l_1'=0) & (mesi_1'=shared);
	[read_1]  l_1=3 & mesi_1!=invalid & (  cp_1 != full & left_1 = false ) -> tick : (l_1'=0);
	[read_1]  l_1=3 & mesi_1 =invalid & (!(cp_1 != full & left_1 = false)) -> read : (l_1'=4) & (mesi_1'=shared);
	[read_1]  l_1=3 & mesi_1!=invalid & (!(cp_1 != full & left_1 = false)) -> tick : (l_1'=4);
	[write_1] l_1=4 & mesi_1!=modified -> write : (l_1'=5) & (mesi_1'=modified);
	[write_1] l_1=4 & mesi_1 =modified -> tick  : (l_1'=5);
	[]        l_1=5 -> micro : (l_1'=6) & (exit'=empty);
	[set_left_true_23] l_1=6 & mesi_1!=modified -> write : (left_1'=true) & (l_1'=8) & (mesi_1'=modified);
	[set_left_true_23] l_1=6 & mesi_1 =modified -> tick  : (left_1'=true) & (l_1'=8);
//	[set_left_true_2]  l_1=6 & mesi_1!=modified -> write : (left_1'=true) & (l_1'=8) & (mesi_1'=modified);
//	[set_left_true_2]  l_1=6 & mesi_1 =modified -> tick  : (left_1'=true) & (l_1'=8);


	[]        l_1=8 -> work : (l_1'=9);


	[read_1]  l_1=9 & mesi_1 =invalid -> read : (l_1'=10) & (cp_1'=exit) & (mesi_1'=shared);
	[read_1]  l_1=9 & mesi_1!=invalid -> tick : (l_1'=10) & (cp_1'=exit);

	[]        l_1=10 & mod(floor(cp_1/me_bit_1),2)=1 -> tick : (l_1'=12);
	[write_1] l_1=10 & mesi_1!=modified & mod(floor(cp_1/me_bit_1),2)=0 -> write : (l_1'=11) & (mesi_1'=modified);
	[write_1] l_1=10 & mesi_1 =modified & mod(floor(cp_1/me_bit_1),2)=0 -> tick  : (l_1'=11);
	[]        l_1=11 -> micro : (l_1'=12) & (exit'=min(max_invalid,max(cp_1+me_bit_1, min_invalid)));

	[read_1]  l_1=12 & mesi_1 =invalid & (  cp_1 != full & left_1 = true ) -> read : (l_1'=9) & (mesi_1'=shared);
	[read_1]  l_1=12 & mesi_1!=invalid & (  cp_1 != full & left_1 = true ) -> tick : (l_1'=9);
	[read_1]  l_1=12 & mesi_1 =invalid & (!(cp_1 != full & left_1 = true)) -> read : (l_1'=13) & (mesi_1'=shared);
	[read_1]  l_1=12 & mesi_1!=invalid & (!(cp_1 != full & left_1 = true)) -> tick : (l_1'=13);
	[write_1] l_1=13 & mesi_1!=modified -> write : (l_1'=14) & (mesi_1'=modified);
	[write_1] l_1=13 & mesi_1 =modified -> tick  : (l_1'=14);
	[]        l_1=14 -> micro : (l_1'=15) & (entry'=empty);
	[set_left_false_23] l_1=15 & mesi_1!=modified -> write : (left_1'=false) & (l_1'=17) & (mesi_1'=modified);
	[set_left_false_23] l_1=15 & mesi_1 =modified -> tick  : (left_1'=false) & (l_1'=17);
//	[set_left_false_2]  l_1=15 & mesi_1!=modified -> write : (left_1'=false) & (l_1'=17) & (mesi_1'=modified);
//	[set_left_false_2]  l_1=15 & mesi_1 =modified -> tick  : (left_1'=false) & (l_1'=17);


	[]        l_1=17 -> work : (l_1'=0);

	//cacheline
	[write_2] true            -> (mesi_1'=invalid);
	[write_3] true            -> (mesi_1'=invalid);

	[read_2]  mesi_1=invalid  -> (mesi_1'=invalid);
	[read_3]  mesi_1=invalid  -> (mesi_1'=invalid);

	[read_2]  mesi_1=shared   -> (mesi_1'=shared);
	[read_3]  mesi_1=shared   -> (mesi_1'=shared);

	[read_2]  mesi_1=modified -> (mesi_1'=shared);
	[read_3]  mesi_1=modified -> (mesi_1'=shared);

	[set_left_false_12] true -> (left_1'=false) & (mesi_1'=invalid);
	[set_left_false_13] true -> (left_1'=false) & (mesi_1'=invalid);
	[set_left_true_12]  true -> (left_1'=true)  & (mesi_1'=invalid);
	[set_left_true_13]  true -> (left_1'=true)  & (mesi_1'=invalid);
//	[set_left_false_1]  true -> (left_1'=false) & (mesi_1'=invalid);
//	[set_left_true_1]   true -> (left_1'=true)  & (mesi_1'=invalid);

endmodule

module process_2 = process_1 [
	me_1     =me_2,
	me_bit_1 =me_bit_2,
	l_1      =l_2,
	cp_1     =cp_2,
	left_1   =left_2,
	mesi_1   =mesi_2,
	read_1   =read_2,
	read_2   =read_1,
	write_1  =write_2,
	write_2  =write_1,
	set_left_false_12 = set_left_false_12,
	set_left_false_13 = set_left_false_23,
	set_left_false_23 = set_left_false_13,
	set_left_true_12  = set_left_true_12,
	set_left_true_13  = set_left_true_23,
	set_left_true_23  = set_left_true_13
//	set_left_false_1 = set_left_false_2,
//	set_left_false_2 = set_left_false_1,
//	set_left_true_1  = set_left_true_2,
//	set_left_true_2  = set_left_true_1
] endmodule

module process_3 = process_1 [
	me_1     =me_3,
	me_bit_1 =me_bit_3,
	l_1      =l_3,
	cp_1     =cp_3,
	left_1   =left_3,
	mesi_1   =mesi_3,
	read_1   =read_3,
	read_3   =read_1,
	write_1  =write_3,
	write_3  =write_1,
	set_left_false_12 = set_left_false_13,
	set_left_false_13 = set_left_false_23,
	set_left_false_23 = set_left_false_12,
	set_left_true_12  = set_left_true_13,
	set_left_true_13  = set_left_true_23,
	set_left_true_23  = set_left_true_12
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

