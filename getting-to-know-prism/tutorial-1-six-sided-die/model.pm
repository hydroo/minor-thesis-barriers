dtmc

module die

	//state in the graph
	s : [0..7] init 0;

	//value of the die
	v : [0..6] init 0;

	[] s=0 -> 0.5 : (s'=1) + 0.5 : (s'=2);
	[] s=1 -> 0.5 : (s'=3) + 0.5 : (s'=4);
	[] s=2 -> 0.5 : (s'=5) + 0.5 : (s'=6);
	[] s=3 -> 0.5 : (s'=1) + 0.5 : (s'=7) & (v'=1);
	[] s=4 -> 0.5 : (s'=7) & (v'=2) + 0.5 : (s'=7) & (v'=3);
	[] s=5 -> 0.5 : (s'=7) & (v'=4) + 0.5 : (s'=7) & (v'=5);
	[] s=6 -> 0.5 : (s'=2) + 0.5 : (s'=7) & (v'=6);
	[] s=7 -> (s'=7);

endmodule

rewards "steps"
	true : 1;
endrewards
