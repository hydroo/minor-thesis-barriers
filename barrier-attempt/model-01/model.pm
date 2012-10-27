dtmc


const prime_1 = 2;
const prime_2 = 3;

const product_of_all_primes = 6;

const min_invalid_barrier_value = 0;
const max_invalid_barrier_value = 7;


global entry : [0..7] init 1;
global exit : [0..7] init 1;
global someone_left : bool;

label "invalid_barrier" =
	entry=0        | entry=4        | entry=5        | entry>product_of_all_primes        |
	entry_copy_1=0 | entry_copy_1=4 | entry_copy_1=5 | entry_copy_1>product_of_all_primes |
	entry_copy_2=0 | entry_copy_2=4 | entry_copy_2=5 | entry_copy_2>product_of_all_primes |
	exit=0         | exit=4         | exit=5         | exit>product_of_all_primes         |
	exit_copy_1=0  | exit_copy_1=4  | exit_copy_1=5  | exit_copy_1>product_of_all_primes  |
	exit_copy_2=0  | exit_copy_2=4  | exit_copy_2=5  | exit_copy_2>product_of_all_primes;


module process_1
	s_1 : [0..17] init 0;
	entry_copy_1 : [0..7] init 1;
	exit_copy_1 : [0..7] init 1;

	[] s_1=0 -> (s_1'=1) & (entry'=1);

	[] s_1=1 -> (s_1'=2) & (entry_copy_1'=entry);

	[] s_1=2 & mod(entry_copy_1,prime_1) =0 -> (s_1'=4);
	// prism wouldn't accept * without the max, because it thinks entry_copy can go out of bounds ... I am pretty sure it cannot, though
	[] s_1=2 & mod(entry_copy_1,prime_1)!=0 -> (s_1'=3);
	[] s_1=3 -> (s_1'=4) & (entry_copy_1'=min(max_invalid_barrier_value,max(entry_copy_1*prime_1, min_invalid_barrier_value)));

	[] s_1=4 -> (s_1'=5) & (entry'=entry_copy_1);

	// diamond for entry_copy_1 != product_of_all_primes & someone_left = false
	// overlapping intentional ... maybe remove later?
	[] s_1=5 & (  entry_copy_1 != product_of_all_primes &   someone_left = false ) -> 0.5:(s_1'=6) + 0.5:(s_1'=7);
	[] s_1=5 & (  entry_copy_1 != product_of_all_primes & !(someone_left = false)) -> 0.5:(s_1'=6) + 0.5:(s_1'=8);
	[] s_1=5 & (!(entry_copy_1 != product_of_all_primes) &  someone_left = false ) -> 0.5:(s_1'=7) + 0.5:(s_1'=8);
	[] s_1=6 &   someone_left = false  -> (s_1'=1);
	[] s_1=6 & !(someone_left = false) -> (s_1'=8);
	[] s_1=7 &   entry_copy_1 != product_of_all_primes  -> (s_1'=1);
	[] s_1=7 & !(entry_copy_1 != product_of_all_primes) -> (s_1'=8);

	[] s_1=5 &  !(entry_copy_1 != product_of_all_primes) & !(someone_left = false) -> (s_1'=8);
	[] s_1=8 -> (s_1'=9) & (someone_left'=true);

	[] s_1=9 -> (s_1'=10) & (exit'=1);

	[] s_1=10 -> (s_1'=11) & (exit_copy_1'=exit);

	[] s_1=11 & mod(exit_copy_1,prime_1) =0 -> (s_1'=14);
	[] s_1=11 & mod(exit_copy_1,prime_1)!=0 -> (s_1'=12);
	[] s_1=12 -> (s_1'=13) & (exit_copy_1'=min(max_invalid_barrier_value,max(exit_copy_1*prime_1, min_invalid_barrier_value)));

	[] s_1=13 -> (s_1'=14) & (exit'=exit_copy_1);

	// diamond for exit_copy_1 != product_of_all_primes & someone_left = true
	[] s_1=14 & (  exit_copy_1 != product_of_all_primes  &   someone_left = true ) -> 0.5:(s_1'=15) + 0.5:(s_1'=16);
	[] s_1=14 & (  exit_copy_1 != product_of_all_primes  & !(someone_left = true)) -> 0.5:(s_1'=15) + 0.5:(s_1'=17);
	[] s_1=14 & (!(exit_copy_1 != product_of_all_primes) &   someone_left = true ) -> 0.5:(s_1'=16) + 0.5:(s_1'=17);
	[] s_1=15 &   someone_left = true  -> (s_1'=10);
	[] s_1=15 & !(someone_left = true) -> (s_1'=17);
	[] s_1=16 &   exit_copy_1 != product_of_all_primes  -> (s_1'=10);
	[] s_1=16 & !(exit_copy_1 != product_of_all_primes) -> (s_1'=17);

	[] s_1=14 & !(exit_copy_1 != product_of_all_primes) & !(someone_left = true) -> (s_1'=17);
	[] s_1=17 -> (s_1'=0) & (someone_left'=false);

endmodule


module process_2 = process_1 [
	prime_1                =prime_2,s_1=s_2,
	entry_copy_1           =entry_copy_2,
	exit_copy_1            =exit_copy_2,
	reset_entry_1          =reset_entry_2,
	announce_entry_1       =announce_entry_2,
	announce_entry_leave_1 =announce_entry_leave_2,

	reset_exit_1           =reset_exit_2,
	announce_exit_1        =announce_exit_2,
	announce_exit_leave_1  =announce_exit_leave_2
] endmodule
