ctmc

const me_1 = 1; //index
const me_2 = 2;

const me_bit_1 = 1; //2^0
const me_bit_2 = 2; //2^1

const empty = 0;
const full = me_bit_1 + me_bit_2;

const min_invalid = empty - 1;
const max_invalid = full + 1;


global entry : [min_invalid..max_invalid] init empty;
global exit : [min_invalid..max_invalid] init empty;
global left : bool init false;



formula base_rate  = 2500.0;
formula tick       = base_rate / 1.0;
formula work       = base_rate / 1000.0;
formula read       = base_rate / 50.0;
formula write      = base_rate / 100.0;



module process_1
	l_1 : [0..9] init 0;
	cp_1 : [min_invalid..max_invalid] init empty;

	[] l_1=0 -> read : (l_1'=1) & (cp_1'=entry);

	[] l_1=1 & mod(floor(cp_1/me_bit_1),2)=1 -> tick : (l_1'=2);
	[] l_1=1 & mod(floor(cp_1/me_bit_1),2)=0 -> write : (l_1'=2) & (entry'=min(max_invalid,max(cp_1+me_bit_1, min_invalid)));

	[] l_1=2 & (  cp_1 != full & left = false ) -> tick : (l_1'=0);
	[] l_1=2 & (!(cp_1 != full & left = false)) -> write : (l_1'=3) & (exit'=empty);
	[] l_1=3 -> write : (l_1'=4) & (left'=true);


	[] l_1=4 -> work : (l_1'=5);


	[] l_1=5 -> read : (l_1'=6) & (cp_1'=exit);

	[] l_1=6 & mod(floor(cp_1/me_bit_1),2)=1 -> tick : (l_1'=7);
	[] l_1=6 & mod(floor(cp_1/me_bit_1),2)=0 -> write : (l_1'=7) & (exit'=min(max_invalid,max(cp_1+me_bit_1, min_invalid)));

	[] l_1=7 & (  cp_1 != full & left = true ) -> tick : (l_1'=4);
	[] l_1=7 & (!(cp_1 != full & left = true)) -> write : (l_1'=8) & (entry'=empty) & (left'=false);
	[] l_1=7 & (!(cp_1 != full & left = true)) -> write : (l_1'=8) & (entry'=empty);
	[] l_1=8 -> write : (l_1'=9) & (left'=false);


	[] l_1=9 -> work : (l_1'=0);

endmodule


module process_2 = process_1 [
	me_1     =me_2,
	me_bit_1 =me_bit_2,
	l_1      =l_2,
	cp_1     =cp_2
] endmodule

