dtmc

const me_1 = 1; //index
const me_2 = 2;
const me_3 = 3;

const me_bit_1 = 1; //2^0
const me_bit_2 = 2; //2^1
const me_bit_3 = 4;

const empty = 0;
const full = me_bit_1 + me_bit_2 + me_bit_3;

const min_invalid = -1;
const max_invalid = full + 1;


global entry : [min_invalid..max_invalid] init empty;
global exit : [min_invalid..max_invalid] init empty;
global left : bool init false;


module process_1
	l_1 : [0..17] init 0;
	cp_1 : [min_invalid..max_invalid] init empty;

	[] l_1=0 -> (l_1'=1) & (entry'=empty);

	[] l_1=1 -> (l_1'=2) & (cp_1'=entry);

	// emulate bit manipulation: (cp_1&me) != 0
	[] l_1=2 & mod(floor(cp_1/me_bit_1),2)=1 -> (l_1'=5);
	// emulate bit manipulation: (cp_1&me) == 0
	[] l_1=2 & mod(floor(cp_1/me_bit_1),2)=0 ->  (l_1'=5) & (entry'=min(max_invalid,max(cp_1+me_bit_1, min_invalid)));

	// diamond/nondeterminism for cp_1 != full & left = false
	[] l_1=5 & (  cp_1 != full & left = false ) -> (l_1'=1);
	[] l_1=5 & (!(cp_1 != full & left = false)) -> (l_1'=8);

	[] l_1=8 -> (l_1'=9) & (left'=true);

	[] l_1=9 -> (l_1'=10) & (exit'=empty);

	[] l_1=10 -> (l_1'=11) & (cp_1'=exit);

	[] l_1=11 & mod(floor(cp_1/me_bit_1),2)=1 -> (l_1'=14);
	[] l_1=11 & mod(floor(cp_1/me_bit_1),2)=0 -> (l_1'=14) & (exit'=min(max_invalid,max(cp_1+me_bit_1, min_invalid)));

	// diamond/nondeterminism for cp_1 != full & left = true
	[] l_1=14 & (  cp_1 != full & left = true ) -> (l_1'=10);
	[] l_1=14 & (!(cp_1 != full & left = true)) -> (l_1'=17);

	[] l_1=17 -> (l_1'=0) & (left'=false);

endmodule


module process_2 = process_1 [
	me_1     =me_2,
	me_bit_1 =me_bit_2,
	l_1      =l_2,
	cp_1     =cp_2
] endmodule

module process_3 = process_1 [
	me_1     =me_3,
	me_bit_1 =me_bit_3,
	l_1      =l_3,
	cp_1     =cp_3
] endmodule


label "invalid_barrier" =
	entry=min_invalid | entry=max_invalid |
	cp_1=min_invalid  | cp_1=max_invalid |
	cp_2=min_invalid  | cp_2=max_invalid |
	cp_3=min_invalid  | cp_3=max_invalid |
	exit=min_invalid  | exit=max_invalid;


formula p1_before        = l_1 = 0 | l_1 = 17;
formula p1_entry_barrier = l_1 >= 1 & l_1 <= 7;
formula p1_between       = l_1 = 8 | l_1 = 9;
formula p1_exit_barrier  = l_1 >= 10 & l_1 <= 16;

formula p2_before        = l_2 = 0 | l_2 = 17;
formula p2_entry_barrier = l_2 >= 1 & l_2 <= 7;
formula p2_between       = l_2 = 8 | l_2 = 9;
formula p2_exit_barrier  = l_2 >= 10 & l_2 <= 16;

formula p3_before        = l_3 = 0 | l_3 = 17;
formula p3_entry_barrier = l_3 >= 1 & l_3 <= 7;
formula p3_between       = l_3 = 8 | l_3 = 9;
formula p3_exit_barrier  = l_3 >= 10 & l_3 <= 16;

label "invalid_locations" =
	(p1_before & p2_between) | (p2_before & p1_between) |
	(p2_before & p3_between) | (p3_before & p2_between) |
	(p1_before & p3_between) | (p3_before & p1_between);
