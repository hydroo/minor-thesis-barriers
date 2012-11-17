mdp

const me_1 = 1; //index
const me_2 = 2;

const me_bit_1 = 1;
const me_bit_2 = 2;

const full = me_bit_1 + me_bit_2;

const min_invalid = -1;
const max_invalid = full + 1;


global sched : [me_1..me_2] init me_2; //currently scheduled process
global entry : [min_invalid..max_invalid] init 0;
global exit : [min_invalid..max_invalid] init 0;
global left : bool;

label "invalid_barrier" =
	entry=min_invalid | entry=max_invalid |
	cp_1=min_invalid  | cp_1=max_invalid |
	cp_2=min_invalid  | cp_2=max_invalid |
	exit=min_invalid  | exit=max_invalid;


module scheduler
	l : [0..1] init 0;
	[] l=0 -> (sched'=me_1);
	[] l=0 -> (sched'=me_2);
endmodule


module process_1
	l_1 : [0..17] init 0;
	cp_1 : [min_invalid..max_invalid] init 0;

	[] sched=me_1 & l_1=0 -> (l_1'=1) & (entry'=1);

	[] sched=me_1 & l_1=1 -> (l_1'=2) & (cp_1'=entry);

	// emulate bit manipulation: (cp_1&me) != 0
	[] sched=me_1 & l_1=2 & mod(floor(cp_1/me_bit_1),2)=1 -> (l_1'=4);
	// emulate bit manipulation: (cp_1&me) == 0
	[] sched=me_1 & l_1=2 & mod(floor(cp_1/me_bit_1),2)=0 -> (l_1'=3);
	// prism wouldn't accept + because it might exceed the bounds ... therefore use min, max
	// emulate bit manipulation: cp_1 |= me_bit_1
	[] sched=me_1 & l_1=3 -> (l_1'=4) & (cp_1'=min(max_invalid,max(cp_1+me_bit_1, min_invalid)));

	[] sched=me_1 & l_1=4 -> (l_1'=5) & (entry'=cp_1);

	// diamond/nondeterminism for cp_1 != full & left = false
	[] sched=me_1 & l_1=5 & (  cp_1 != full                ) -> (l_1'=6);
	[] sched=me_1 & l_1=5 & (                 left = false ) -> (l_1'=7);
	[] sched=me_1 & l_1=5 & (!(cp_1 != full & left = false)) -> (l_1'=8);
	[] sched=me_1 & l_1=6 &   left = false  -> (l_1'=1);
	[] sched=me_1 & l_1=6 & !(left = false) -> (l_1'=8);
	[] sched=me_1 & l_1=7 &   cp_1 != full  -> (l_1'=1);
	[] sched=me_1 & l_1=7 & !(cp_1 != full) -> (l_1'=8);

	[] sched=me_1 & l_1=8 -> (l_1'=9) & (left'=true);

	[] sched=me_1 & l_1=9 -> (l_1'=10) & (exit'=1);

	[] sched=me_1 & l_1=10 -> (l_1'=11) & (cp_1'=exit);

	[] sched=me_1 & l_1=11 & mod(floor(cp_1/me_bit_1),2)=1 -> (l_1'=14);
	[] sched=me_1 & l_1=11 & mod(floor(cp_1/me_bit_1),2)=0 -> (l_1'=12);
	[] sched=me_1 & l_1=12 -> (l_1'=13) & (cp_1'=min(max_invalid,max(cp_1+me_bit_1, min_invalid)));

	[] sched=me_1 & l_1=13 -> (l_1'=14) & (exit'=cp_1);

	// diamond/nondeterminism for cp_1 != full & left = true
	[] sched=me_1 & l_1=14 & (  cp_1 != full               ) -> (l_1'=15);
	[] sched=me_1 & l_1=14 & (                 left = true ) -> (l_1'=16);
	[] sched=me_1 & l_1=14 & (!(cp_1 != full & left = true)) -> (l_1'=17);
	[] sched=me_1 & l_1=15 &   left = true  -> (l_1'=10);
	[] sched=me_1 & l_1=15 & !(left = true) -> (l_1'=17);
	[] sched=me_1 & l_1=16 &   cp_1 != full  -> (l_1'=10);
	[] sched=me_1 & l_1=16 & !(cp_1 != full) -> (l_1'=17);

	[] sched=me_1 & l_1=17 -> (l_1'=0) & (left'=false);

endmodule


module process_2 = process_1 [
	me_1     =me_2,
	me_bit_1 =me_bit_2,
	l_1      =l_2,
	cp_1     =cp_2,
	tick_1   =tick_2
] endmodule
