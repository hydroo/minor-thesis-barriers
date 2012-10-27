dtmc


const t_max  = 68;

const ncrit = 2;
const wait = 0;
const crit = 1;

const free = 0;
const lock_1 = 1;
const lock_2 = 2;


label "failed" = lock!=lock_1 & loc_1=wait & t_1=1;
label "spinning" = lock!=lock_1 & loc_1=wait & t_1>0;
label "request" = loc_1=wait & t_1=0;
label "release" = loc_1=crit & t_1=0;
label "race" =
	((loc_1=wait) | (loc_2=wait))
	& (lock=free | (loc_1=crit & t_1=0) | (loc_2=crit & t_2=0));


init
	(lock=free)
	& (loc_1=ncrit) & ((t_1=48) | (t_1=58) | (t_1=68) | (t_1=38))
	& (loc_2=ncrit) & ((t_2=48) | (t_2=58) | (t_2=68) | (t_2=38))
endinit


module Process_1
	t_1: [0..t_max];
	loc_1: [0..2];

	//-------------------------------------------------------------------------------------------------------------------------
	[tick] loc_1=ncrit & t_1!=0	->	(t_1'=t_1-1);
	[tick] loc_1=ncrit & t_1=0	->	(loc_1'=wait);

	//-------------------------------------------------------------------------------------------------------------------------
	[tick] loc_1=wait & lock!=lock_1 & t_1=0	->	(t_1'=1);
	[tick] loc_1=wait & lock!=lock_1 & t_1>0	->	(t_1'=2);
	[tick] loc_1=wait & lock=lock_1 & t_1=1	->	1/1: (loc_1'=crit) & (t_1'=3);
	[tick] loc_1=wait & lock=lock_1 & t_1=2	->	1/1: (loc_1'=crit) & (t_1'=4);

	//-------------------------------------------------------------------------------------------------------------------------
	[tick] loc_1=crit & t_1!=0	->	(t_1'=t_1-1);
	[tick] loc_1=crit & t_1=0	->	1/2: (loc_1'=ncrit) & (t_1'=48) + 1/2: (loc_1'=ncrit);
endmodule


module Process_2 = Process_1 [t_1=t_2, loc_1=loc_2, lock_1=lock_2] endmodule


module Lock
	lock: [0..2];
	//-------------------------------------------------------------------------------------------------------------------------
	//from unlock to lock_1
	[tick] lock=free & loc_1=wait	->	(lock'=lock_1);
	//self loop in lock_1
	[tick] lock=lock_1 & !(loc_1=crit & t_1=0)	->	true;
	//from lock_1 to unlock
	[tick] lock=lock_1 & loc_1=crit & t_1=0 & loc_1!=wait & loc_2!=wait	->	(lock'=free);
	//from lock_1 to other locks
	[tick] lock=lock_1 & loc_1=crit & t_1=0 & loc_2=wait	->	(lock'=lock_2);

	//-------------------------------------------------------------------------------------------------------------------------
	//from unlock to lock_2
	[tick] lock=free & loc_2=wait	->	(lock'=lock_2);
	//self loop in lock_2
	[tick] lock=lock_2 & !(loc_2=crit & t_2=0)	->	true;
	//from lock_2 to unlock
	[tick] lock=lock_2 & loc_2=crit & t_2=0 & loc_1!=wait & loc_2!=wait	->	(lock'=free);
	//from lock_2 to other locks
	[tick] lock=lock_2 & loc_2=crit & t_2=0 & loc_1=wait	->	(lock'=lock_1);

	//-------------------------------------------------------------------------------------------------------------------------
	//self loop in unlock
	[tick] lock=free & loc_1!=wait & loc_2!=wait	->	true;
endmodule


rewards "spin"
	lock!=lock_1 & loc_1=wait & t_1>0: 1;
endrewards

rewards "wait"
	loc_1=wait & (lock=free | (loc_2=crit & t_2=0)): 1;	
	loc_2=wait & (lock=free | (loc_1=crit & t_1=0)): 1;	
endrewards
