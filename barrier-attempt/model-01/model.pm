mdp


const me_1 = 1;
const me_2 = 2;

const full = me_1 + me_2;

const min_invalid = -1;
const max_invalid = full + 1;


global entry : [min_invalid..max_invalid] init 0;
global exit : [min_invalid..max_invalid] init 0;
global left : bool;

label "invalid_barrier" =
	entry=min_invalid | entry=max_invalid |
	cp_1=min_invalid  | cp_1=max_invalid |
	cp_2=min_invalid  | cp_2=max_invalid |
	exit=min_invalid  | exit=max_invalid;


module process_1
	l_1 : [0..17] init 0;
	cp_1 : [min_invalid..max_invalid] init 0;

	[] l_1=0 -> (l_1'=1) & (entry'=1);

	[] l_1=1 -> (l_1'=2) & (cp_1'=entry);

	// emulate bit manipulation: (cp_1&me) != 0
	[] l_1=2 & mod(floor(cp_1/me_1),2)=1 -> (l_1'=4);
	// emulate bit manipulation: (cp_1&me) == 0
	[] l_1=2 & mod(floor(cp_1/me_1),2)=0 -> (l_1'=3);
	// prism wouldn't accept + because it might exceed the bounds ... therefore use min, max
	// emulate bit manipulation: cp_1 |= me_1
	[] l_1=3 -> (l_1'=4) & (cp_1'=min(max_invalid,max(cp_1+me_1, min_invalid)));

	[] l_1=4 -> (l_1'=5) & (entry'=cp_1);

	// diamond/nondeterminism for cp_1 != full & left = false
	[] l_1=5 & (  cp_1 != full                ) -> (l_1'=6);
	[] l_1=5 & (                 left = false ) -> (l_1'=7);
	[] l_1=5 & (!(cp_1 != full & left = false)) -> (l_1'=8);
	[] l_1=6 &   left = false  -> (l_1'=1);
	[] l_1=6 & !(left = false) -> (l_1'=8);
	[] l_1=7 &   cp_1 != full  -> (l_1'=1);
	[] l_1=7 & !(cp_1 != full) -> (l_1'=8);

	[] l_1=8 -> (l_1'=9) & (left'=true);

	[] l_1=9 -> (l_1'=10) & (exit'=1);

	[] l_1=10 -> (l_1'=11) & (cp_1'=exit);

	[] l_1=11 & mod(floor(cp_1/me_1),2)=1 -> (l_1'=14);
	[] l_1=11 & mod(floor(cp_1/me_1),2)=0 -> (l_1'=12);
	[] l_1=12 -> (l_1'=13) & (cp_1'=min(max_invalid,max(cp_1+me_1, min_invalid)));

	[] l_1=13 -> (l_1'=14) & (exit'=cp_1);

	// diamond/nondeterminism for cp_1 != full & left = true
	[] l_1=14 & (  cp_1 != full               ) -> (l_1'=15);
	[] l_1=14 & (                 left = true ) -> (l_1'=16);
	[] l_1=14 & (!(cp_1 != full & left = true)) -> (l_1'=17);
	[] l_1=15 &   left = true  -> (l_1'=10);
	[] l_1=15 & !(left = true) -> (l_1'=17);
	[] l_1=16 &   cp_1 != full  -> (l_1'=10);
	[] l_1=16 & !(cp_1 != full) -> (l_1'=17);

	[] l_1=17 -> (l_1'=0) & (left'=false);

endmodule


module process_2 = process_1 [
	me_1 =me_2,
	l_1  =l_2,
	cp_1 =cp_2
] endmodule
