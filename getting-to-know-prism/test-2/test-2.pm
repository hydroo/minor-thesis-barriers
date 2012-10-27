dtmc

const t_max = 50;

const busy_time_1 = 5;
const busy_time_2 = 4;

const s_start = 0;
const s_busy = 1;
const s_wait = 2;

label "busy_1" = s_1=s_busy;
label "busy_2" = s_2=s_busy;

label "start_1" = s_1=s_start;
label "start_2" = s_2=s_start;

label "wait_1" = s_1=s_wait;
label "wait_2" = s_2=s_wait;


module process_1
	t_1 : [0..t_max];
	s_1 : [0..2] init s_start;

	[] s_1=s_start -> 0.5 : (s_1'=s_busy) & (t_1'=busy_time_1) + 0.5 : (s_1'=s_busy) & (t_1'=busy_time_2);

	[] s_1=s_busy & t_1=1 -> (s_1'=s_wait);
	[] s_1=s_busy & t_1>1 -> (t_1'=t_1-1);

	[release] true -> (s_1'=s_start);
endmodule	


module process_2 = process_1 [t_1=t_2, s_1=s_2] endmodule


module barrier
	[release] s_1=s_wait & s_2=s_wait -> true;
endmodule
