dtmc


const me_1 = 1;
const me_2 = 2;

const full = 3;

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
	s_1 : [0..17] init 0;
	cp_1 : [min_invalid..max_invalid] init 0;

	[] s_1=0 -> (s_1'=1) & (entry'=1);

	[] s_1=1 -> (s_1'=2) & (cp_1'=entry);

	// emulate bit manipulation: (cp_1&me) != 0
	[] s_1=2 & mod(floor(cp_1/me_1),2)=1 -> (s_1'=4);
	// emulate bit manipulation: (cp_1&me) == 0
	[] s_1=2 & mod(floor(cp_1/me_1),2)=0 -> (s_1'=3);
	// prism wouldn't accept + because it might exceed the bounds ... therefore use min, max
	// emulate bit manipulation: cp_1 |= me_1
	[] s_1=3 -> (s_1'=4) & (cp_1'=min(max_invalid,max(cp_1+me_1, min_invalid)));

	[] s_1=4 -> (s_1'=5) & (entry'=cp_1);

	// diamon/nondeterminis for cp_1 != full & left = false
	[] s_1=5 & (  cp_1 != full &   left = false ) -> 0.5:(s_1'=6) + 0.5:(s_1'=7);
	[] s_1=5 & (  cp_1 != full & !(left = false)) -> 0.5:(s_1'=6) + 0.5:(s_1'=8);
	[] s_1=5 & (!(cp_1 != full) &  left = false ) -> 0.5:(s_1'=7) + 0.5:(s_1'=8);
	[] s_1=6 &   left = false  -> (s_1'=1);
	[] s_1=6 & !(left = false) -> (s_1'=8);
	[] s_1=7 &   cp_1 != full  -> (s_1'=1);
	[] s_1=7 & !(cp_1 != full) -> (s_1'=8);

	[] s_1=5 &  !(cp_1 != full) & !(left = false) -> (s_1'=8);
	[] s_1=8 -> (s_1'=9) & (left'=true);

	[] s_1=9 -> (s_1'=10) & (exit'=1);

	[] s_1=10 -> (s_1'=11) & (cp_1'=exit);

	[] s_1=11 & mod(floor(cp_1/me_1),2)=1 -> (s_1'=14);
	[] s_1=11 & mod(floor(cp_1/me_1),2)=0 -> (s_1'=12);
	[] s_1=12 -> (s_1'=13) & (cp_1'=min(max_invalid,max(cp_1+me_1, min_invalid)));

	[] s_1=13 -> (s_1'=14) & (exit'=cp_1);

	// diamond/nondeterminism for cp_1 != full & left = true
	[] s_1=14 & (  cp_1 != full  &   left = true ) -> 0.5:(s_1'=15) + 0.5:(s_1'=16);
	[] s_1=14 & (  cp_1 != full  & !(left = true)) -> 0.5:(s_1'=15) + 0.5:(s_1'=17);
	[] s_1=14 & (!(cp_1 != full) &   left = true ) -> 0.5:(s_1'=16) + 0.5:(s_1'=17);
	[] s_1=15 &   left = true  -> (s_1'=10);
	[] s_1=15 & !(left = true) -> (s_1'=17);
	[] s_1=16 &   cp_1 != full  -> (s_1'=10);
	[] s_1=16 & !(cp_1 != full) -> (s_1'=17);

	[] s_1=14 & !(cp_1 != full) & !(left = true) -> (s_1'=17);
	[] s_1=17 -> (s_1'=0) & (left'=false);

endmodule


module process_2 = process_1 [
	me_1 =me_2,
	s_1  =s_2,
	cp_1 =cp_2
] endmodule
