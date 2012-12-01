mdp

const me_1 = 1; //index
const me_2 = 2;
const me_3 = 3;

const me_bit_1 = 1; //2^0
const me_bit_2 = 2; //2^1
const me_bit_3 = 4;

const empty = 0;
const full = me_bit_1 + me_bit_2 + me_bit_3;

const min_invalid = empty - 1;
const max_invalid = full + 1;


global entry : [min_invalid..max_invalid] init empty;
global exit : [min_invalid..max_invalid] init empty;
global left : bool init false;


module process_1
	l_1 : [0..5] init 0;
	cp_1 : [min_invalid..max_invalid] init empty;

	[] l_1=0 -> (l_1'=1) & (cp_1'=entry);

	[] l_1=1 & mod(floor(cp_1/me_bit_1),2)=1 -> (l_1'=2);
	[] l_1=1 & mod(floor(cp_1/me_bit_1),2)=0 ->  (l_1'=2) & (entry'=min(max_invalid,max(cp_1+me_bit_1, min_invalid)));

	[] l_1=2 & (  cp_1 != full & left = false ) -> (l_1'=0);
	[] l_1=2 & (!(cp_1 != full & left = false)) -> (l_1'=3) & (exit'=empty) & (left'=true);


	[] l_1=3 -> (l_1'=4) & (cp_1'=exit);

	[] l_1=4 & mod(floor(cp_1/me_bit_1),2)=1 -> (l_1'=5);
	[] l_1=4 & mod(floor(cp_1/me_bit_1),2)=0 -> (l_1'=5) & (exit'=min(max_invalid,max(cp_1+me_bit_1, min_invalid)));

	[] l_1=5 & (  cp_1 != full & left = true ) -> (l_1'=3);
	[] l_1=5 & (!(cp_1 != full & left = true)) -> (l_1'=0) & (entry'=empty) & (left'=false);

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

