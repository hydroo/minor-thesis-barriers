dtmc


const prime_1 = 2;
const prime_2 = 3;

const full = 6;

const min_invalid = 0;
const max_invalid = 7;


global entry : [0..7] init 1;
global exit : [0..7] init 1;
global left : bool;

label "invalid_barrier" =
	entry=0      | entry=4      | entry=5      | entry>full      |
	entry_cp_1=0 | entry_cp_1=4 | entry_cp_1=5 | entry_cp_1>full |
	entry_cp_2=0 | entry_cp_2=4 | entry_cp_2=5 | entry_cp_2>full |
	exit=0       | exit=4       | exit=5       | exit>full       |
	exit_cp_1=0  | exit_cp_1=4  | exit_cp_1=5  | exit_cp_1>full  |
	exit_cp_2=0  | exit_cp_2=4  | exit_cp_2=5  | exit_cp_2>full;


module process_1
	s_1 : [0..17] init 0;
	entry_cp_1 : [0..7] init 1;
	exit_cp_1 : [0..7] init 1;

	[] s_1=0 -> (s_1'=1) & (entry'=1);

	[] s_1=1 -> (s_1'=2) & (entry_cp_1'=entry);

	[] s_1=2 & mod(entry_cp_1,prime_1) =0 -> (s_1'=4);
	// prism wouldn't accept * without the max, because it thinks entry_copy can go out of bounds ... I am pretty sure it cannot, though
	[] s_1=2 & mod(entry_cp_1,prime_1)!=0 -> (s_1'=3);
	[] s_1=3 -> (s_1'=4) & (entry_cp_1'=min(max_invalid,max(entry_cp_1*prime_1, min_invalid)));

	[] s_1=4 -> (s_1'=5) & (entry'=entry_cp_1);

	// diamon/nondeterminis for entry_cp_1 != full & left = false
	[] s_1=5 & (  entry_cp_1 != full &   left = false ) -> 0.5:(s_1'=6) + 0.5:(s_1'=7);
	[] s_1=5 & (  entry_cp_1 != full & !(left = false)) -> 0.5:(s_1'=6) + 0.5:(s_1'=8);
	[] s_1=5 & (!(entry_cp_1 != full) &  left = false ) -> 0.5:(s_1'=7) + 0.5:(s_1'=8);
	[] s_1=6 &   left = false  -> (s_1'=1);
	[] s_1=6 & !(left = false) -> (s_1'=8);
	[] s_1=7 &   entry_cp_1 != full  -> (s_1'=1);
	[] s_1=7 & !(entry_cp_1 != full) -> (s_1'=8);

	[] s_1=5 &  !(entry_cp_1 != full) & !(left = false) -> (s_1'=8);
	[] s_1=8 -> (s_1'=9) & (left'=true);

	[] s_1=9 -> (s_1'=10) & (exit'=1);

	[] s_1=10 -> (s_1'=11) & (exit_cp_1'=exit);

	[] s_1=11 & mod(exit_cp_1,prime_1) =0 -> (s_1'=14);
	[] s_1=11 & mod(exit_cp_1,prime_1)!=0 -> (s_1'=12);
	[] s_1=12 -> (s_1'=13) & (exit_cp_1'=min(max_invalid,max(exit_cp_1*prime_1, min_invalid)));

	[] s_1=13 -> (s_1'=14) & (exit'=exit_cp_1);

	// diamond/nondeterminism for exit_cp_1 != full & left = true
	[] s_1=14 & (  exit_cp_1 != full  &   left = true ) -> 0.5:(s_1'=15) + 0.5:(s_1'=16);
	[] s_1=14 & (  exit_cp_1 != full  & !(left = true)) -> 0.5:(s_1'=15) + 0.5:(s_1'=17);
	[] s_1=14 & (!(exit_cp_1 != full) &   left = true ) -> 0.5:(s_1'=16) + 0.5:(s_1'=17);
	[] s_1=15 &   left = true  -> (s_1'=10);
	[] s_1=15 & !(left = true) -> (s_1'=17);
	[] s_1=16 &   exit_cp_1 != full  -> (s_1'=10);
	[] s_1=16 & !(exit_cp_1 != full) -> (s_1'=17);

	[] s_1=14 & !(exit_cp_1 != full) & !(left = true) -> (s_1'=17);
	[] s_1=17 -> (s_1'=0) & (left'=false);

endmodule


module process_2 = process_1 [
	prime_1    =prime_2,s_1=s_2,
	entry_cp_1 =entry_cp_2,
	exit_cp_1  =exit_cp_2
] endmodule
