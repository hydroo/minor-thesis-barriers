#! /usr/bin/env python3

import sys
sys.path.append("../shared-memory")

import shared_memory

def generateModel(threadCount, workTicks, readTicks, writeTicks, debug) :

	s = "" # model
	t = "" # correctness props

	s += "ctmc\n" # nothing but ctmc is supported
	s += "\n"

	s += generateConstants(threadCount, workTicks)
	s += "\n"

	s += "// *** main thread begin ***\n"
	s += "\n"
	s += "// * last _# at labels and variables is always the id of the \"owning\" process "
	s += "//\n"
	s += "// * you always need to add transitions for all sync labels in var_shared, otherwise\n"
	s += "//   they will not be recognized as synchronized and are able to fire always\n"
	s += "//\n"
	s += "// * not all labels are for sync. but for easier debugging in the simulator: work_*, done_*\n"
	s += "// * always read using [var_read_n]\n"
	s += "// * always write using [var_set_to_*_n]\n"
	s += "//\n"
	s += "// * always introduce an atomic op using [bar_atomic_begin_n]\n"
	s += "// * use read and writes as usual in between\n"
	s += "// * always end an atomic op using [bar_atomic_end_n]\n"
	s += "\n"

	s += generateThread(0, threadCount)
	s += "\n"

	s += "// *** main thread end ***\n\n"

	s += "// *** thread labels begin ***\n\n"
	s += generateLabels(threadCount)
	s += "\n"
	s += "// *** thread labels end ***\n\n"

	s += "// *** shared memory begin ***\n\n"
	t += "// *** shared memory begin ***\n\n"

	s_, t_ = shared_memory.generatePrerequisites(threadCount, readTicks, writeTicks)
	s += s_
	t += t_

	s += "\n"

	s_, t_ = shared_memory.generateVariable("bar", "[0..thread_count]",  "thread_count", [str(i) for i in range(0, threadCount)], threadCount, debug, True)
	s += s_
	t += t_

	t += "\n"

	s += shared_memory.generateRewards()
	s += "\n"

	s += "// *** shared memory end ***\n\n"
	t += "// *** shared memory end ***\n\n"

	s += "// *** thread copies begin ***\n\n"
	for p in range(1, threadCount) :
		s += generateThread(p, threadCount)
		s += "\n"

	s += "// *** thread copies end ***\n\n"

	s += "// *** thread rewards begin ***\n\n"
	s += generateRewards(threadCount)
	s += "\n"
	s += "// *** thread rewards end ***\n\n"

	return s, t

def generateConstants(threadCount, workTicks) :

	s = ""

	s = "const thread_count = " + str(threadCount) + ";\n"

	s += "\n"

	s += "const work_ticks  = " + str(workTicks) + ";\n"

	s += "\n"

	s += "// rates\n"
	s += "const double base_rate = 1000.0;\n"            # needed for shared_memory as well
	s += "const double rare      = tick / 1000000;\n"
	s += "const double tick      = base_rate / 1.0;\n"   # needed for shared_memory as well
	s += "const double work      = tick / work_ticks;\n"

	s += "\n"

	s += "// thread locations\n"
	s += "// all names describe the behaviour of the next transition\n"
	s += "const l_init         = 0;\n"
	s += "const l_work         = l_init;\n"
	s += "const l_atomic_begin = 1;\n"
	s += "const l_read         = 2;\n"
	s += "const l_write        = 3;\n"
	s += "const l_atomic_end   = 4;\n"
	s += "const l_wait         = 5;\n"
	s += "const l_done         = 6;\n"

	return s

def generateThread(p, threadCount) :

	s = ""

	s += "module thread_#\n"

	s += "    l_# : [l_init..l_done] init l_init;\n"

	s += "\n"

	s += "    [work_#]             l_#=l_work                -> work : (l_#'=l_atomic_begin);\n"
	s += "\n"
	s += "    [bar_atomic_begin_#] l_#=l_atomic_begin        ->        (l_#'=l_read);\n"
	s += "\n"
	s += "    [bar_read_#]         l_#=l_read                ->        (l_#'=l_write);\n"
	s += "\n"

	# set to 2 will never be triggered, but is needed for sync
	for i in range(1, threadCount+1) :
		s += "    [bar_set_to_" + str(i-1) + "_#]     l_#=l_write      & bar =" + str(i) + " ->        (l_#'=l_atomic_end);\n"

	s += "\n"
	s += "    [bar_atomic_end_#]   l_#=l_atomic_end          ->        (l_#'=l_wait);\n"
	s += "\n"
	s += "    [bar_read_#]         l_#=l_wait       & bar!=0 ->        true;\n"
	s += "    [bar_read_#]         l_#=l_wait       & bar =0 ->        (l_#'=l_done);\n"
	s += "\n"
	s += "    [done_#]             l_#=l_done                -> rare : true;\n"

	s += "endmodule\n"

	return s.replace('#', str(p))

def generateRewards(threadCount) :
	s = ""

	s += "// state rewards\n"
	s += "rewards \"time\"\n"
	s += "    true : base_rate;\n"
	s += "endrewards\n"

	s += "\n"

	s += "rewards \"time_all_are_working\"\n"
	s += "    all_are_working : base_rate;\n"
	s += "endrewards\n"

	s += "\n"

	s += "rewards \"time_not_all_are_working\"\n"
	s += "    !all_are_working : base_rate;\n"
	s += "endrewards\n"

	s += "\n"

	s += "rewards \"time_one_is_working\"\n"
	s += "    one_is_working : base_rate;\n"
	s += "endrewards\n"

	s += "\n"

	s += "rewards \"time_not_one_is_working\"\n"
	s += "    !one_is_working : base_rate;\n"
	s += "endrewards\n"

	s += "\n"

	s += "rewards \"time_one_is_writing\"\n"
	s += "    one_is_writing : base_rate;\n"
	s += "endrewards\n"

	s += "\n"

	s += "rewards \"time_one_is_writing_inc\"\n"
	s += "    one_is_writing_inc : base_rate;\n"
	s += "endrewards\n"

	s += "\n"

	s += "rewards \"time_one_is_reading\"\n"
	s += "    one_is_reading : base_rate;\n"
	s += "endrewards\n"

	s += "\n"

	s += "rewards \"time_one_is_done\"\n"
	s += "    one_is_done : base_rate;\n"
	s += "endrewards\n"

	s += "\n"

	s += "rewards \"time_not_one_is_done\"\n"
	s += "    !one_is_done : base_rate;\n"
	s += "endrewards\n"

	s += "\n"

	s += "rewards \"time_not_all_are_done\"\n"
	s += "    !all_are_done : base_rate;\n"
	s += "endrewards\n"

	s += "\n"

	s += "rewards \"time_all_are_done\"\n"
	s += "    all_are_done : base_rate;\n"
	s += "endrewards\n"

	s += "\n" + operationRewards("all_are_working", threadCount)

	s += "\n" + operationRewards("one_is_working", threadCount)

	s += "\n" + operationRewards("not_one_is_done", threadCount)

	s += "\n" + operationRewards("not_all_are_done", threadCount)

	s += "\n" + operationRewards("one_is_writing_inc", threadCount)

	return s

def operationRewards(guard, threadCount) :

	s = ""

	if guard.startswith("not_") :
		guardName = "!" + guard[4:]
	else :
		guardName = guard
	localRewardName = "local_operations_" + guard
	sharedRewardName = "shared_operations_" + guard

	s += "rewards \"%s\"\n" % localRewardName
	for p in range(0, threadCount) :
		s += "    [bar_read_%d]          %s & bar_local_read_%d  : %d;\n" % (p, guardName, p, 1)
		s += "    [bar_atomic_begin_%d]  %s & bar_local_write_%d : %d;\n" % (p, guardName, p, 1)
		for q in range(0, threadCount) :
			s += "    [bar_set_to_%d_%d]      %s & bar_local_write_%d : %d;\n" % (q, p, guardName, p, 1)
	s += "endrewards\n"

	s += "rewards \"%s\"\n" % sharedRewardName
	for p in range(0, threadCount) :
		s += "    [bar_read_%d]          %s & bar_shared_read_%d  : %d;\n" % (p, guardName, p, 1)
		s += "    [bar_atomic_begin_%d]  %s & bar_shared_write_%d : %d;\n" % (p, guardName, p, 1)
	s += "endrewards\n"

	# module thread_#
	#     [work_#]             l_#=l_work                -> work : (l_#'=l_atomic_begin)  # (local ops:0, shared ops:0)
	#
	#     [bar_atomic_begin_#] l_#=l_atomic_begin        ->        (l_#'=l_read)          # (0, 1)
	#
	#     [bar_read_#]         l_#=l_read                ->        (l_#'=l_write)         # (0, 1)
	#
	#     [bar_set_to_..._#]   l_#=l_write      & bar =... ->      (l_#'=l_atomic_end)    # (1, 0) only happens locally anyways
	#
	#     [bar_atomic_end_#]   l_#=l_atomic_end          ->        (l_#'=l_wait)          # (0, 0)
	#
	#     [bar_read_#]         l_#=l_wait       & bar!=0 ->        true                   # (0, 1)
	#     [bar_read_#]         l_#=l_wait       & bar =0 ->        (l_#'=l_done)          # (0, 1)
	#
	#     [done_#]             l_#=l_done                -> rare : true                   # (0, 0)
	# endmodule

	return s

def generateLabels(threadCount) :

	s = ""

	s += "formula one_is_done                  = " + " | ".join(["l_%d=l_done" % i for i in range(0, threadCount)]) + ";\n"
	s += "formula all_are_done                 = " + " & ".join(["l_%d=l_done" % i for i in range(0, threadCount)]) + ";\n"
	#s += "formula exactly_one_is_done          = " +  " | ".join([ "(l_%d = l_done & " % i + " & ".join(["l_%d < l_done" % j for j in range(0, threadCount) if j!=i]) + ")" for i in range(0, threadCount)]) + ";\n"
	#s += "label \"one_is_done\"                  = one_is_done;\n"
	#s += "label \"all_are_done\"                 = all_are_done;\n"
	#s += "label \"exactly_one_is_done\"          = exactly_one_is_done;\n"

	s += "\n"

	s += "formula one_is_working               = " +  " | ".join([ "l_%d = l_work" % i for i in range(0, threadCount)]) + ";\n"
	s += "formula all_are_working              = " +  " & ".join([ "l_%d = l_work" % i for i in range(0, threadCount)]) + ";\n"
	s += "formula exactly_one_is_done_working  = " +  " | ".join([ "(l_%d >= l_atomic_begin & " % i + " & ".join(["l_%d = l_work" % j for j in range(0, threadCount) if j!=i]) + ")" for i in range(0, threadCount)]) + ";\n"
	#s += "label \"one_is_working\"               = one_is_working;\n"
	#s += "label \"all_are_working\"              = all_are_working;\n"
	#s += "label \"exactly_one_is_done_working\"  = exactly_one_is_done_working;\n"

	s += "\n"

	s += "formula one_is_writing               = !all_are_working & (" + " | ".join([ "l_%d <= l_atomic_end" % i for i in range(0, threadCount)]) + ");\n"
	s += "formula one_is_writing_inc           = " + " | ".join([ "l_%d <= l_atomic_end" % i for i in range(0, threadCount)]) + ";\n"
	s += "formula all_are_writing              = !one_is_working  & (" + " & ".join([ "l_%d <= l_atomic_end" % i for i in range(0, threadCount)]) + ");\n"
	s += "formula none_are_writing             = !one_is_writing;\n"
	#s += "label \"one_is_writing\"               = one_is_writing;\n"
	#s += "label \"all_are_writing\"              = all_are_writing;\n"

	s += "\n"

	s += "formula one_is_reading               = " + " | ".join(["l_%d=l_wait & (" % i + " & ".join(["l_%d>=l_wait" % j for j in range(0, threadCount) if i!=j]) + ")" for i in range(0, threadCount)]) + ";\n"
	s += "formula all_are_reading_or_done      = " + " & ".join(["l_%d>=l_wait" % i for i in range(0, threadCount)]) + ";\n"
	#s += "label \"one_is_reading\"             = one_is_reading;\n"
	#s += "label \"all_are_reading_or_done\"    = all_are_reading_or_done;\n"

	return s

# ### correctness props ### ###################################################
def generateCorrectnessProperties(threadCount) :

	t = ""

	t += "// *** thread begin ***\n\n"

	t += "P>=1 [F all_are_done]\n"
	t += "\n"

	t += "// the following 4 queries partition the state space and have to add up to the total state count\n"
	t += "filter(+, P=? [all_are_working]) + filter(+, P=? [one_is_writing]) + filter(+, P=? [one_is_reading]) + filter(+, P=? [all_are_done])\n"

	t += "\n"

	t += "// *** thread end ***\n"

	return t

# ### quantitative props ### ##################################################
def generateQuantitativeProperties(threadCount) :

	t = ""

	t += "// *** thread begin ***\n\n"

	t += "// python source contains comments on queries as well\n"
	t += "\n"
	t += "// e for expected value\n"
	t += "// c for cumulative\n"
	t += "// p for partition\n\n"

	# sascha queries A-D begin
	t += "// sascha queries A-D begin\n\n"

	basicQueries = {
		#key : [query, comment]
		"A" : ["time_not_all_are_working" , "time up to: first finished working and entered"],            # correct
		"B" : ["time_not_one_is_working"  , "time up to: last finished working and entered"],             # correct
		"C" : ["time_one_is_done"         , "time up to: first recognized the barrier is full and left"], # correct
		"D" : ["time_all_are_done"        , "time up to: all recognized the barrier is full and left"],   # correct
		}

	# D-B is probably R{\"time_all_are_done\"}=? [I=time2]), where time2 = time-R{\"time_one_is_working\"}=? [I=time]\n"
	# prose: you subtract the time which at least one is working from the x-axis of the query for all done
	# You can't query like that. It is very possible to do in a script though. Making sure it is correct is hard.

	for k in sorted(basicQueries.keys()) :
		query = basicQueries[k]
		t += "// (%s) and (%se) %s\n" % (k, k, query[1])
		t += "R{\"%s\"}=? [I=time] / base_rate\n" % query[0]                              # correct
		# invers of label %s. reachability reward until the label holds, or during the invers of the label holds
		t += "R{\"time\"}=? [F all_are_done] - R{\"%s\"}=? [F all_are_done]\n" % query[0] # correct
		t += "\n"

	t += "\n"

	t += "// sascha queries A-D end\n\n"

	# ### cumulative queries begin
	# shows how much time has been spent in different parts of the algorithm
	# if simulated up to a certain point
	#
	# in order for cumulative queries to make sense here we have to invert some labels
	t += "// cumulative queries begin\n\n"

	queries = {
		#key : [query, comment]
		"Ac" : ["time_all_are_working"    , "time up to: first finished working and entered"],
		"Bc" : ["time_one_is_working"     , "time up to: last finished working and entered"],
		"Cc" : ["time_not_one_is_done"    , "time up to: first recognized the barrier is full and left"],
		"Dc" : ["time_not_all_are_done"   , "time up to: all recognized the barrier is full and left"],
		"Ec" : ["time_one_is_writing_inc" , "time up to: no one is writing"],
	}

	for k in sorted(queries.keys()) :
		query = queries[k]
		t += "// (%s) and (%se) %s\n" % (k, k, query[1])
		t += "R{\"%s\"}=? [C<=time]\n" % query[0]
		t += "R{\"%s\"}=? [F all_are_done]\n" % query[0]
		t += "\n"

	t += "// cumulative queries end\n\n"
	# ### cumulative queries end

	# ### operation counting queries begin
	t += "// operation countingqueries begin\n\n"

	queries = {
		#key : [query, comment]
		"Al" : ["local_operations_all_are_working"     , "local operations up to: first finished working and entered"],
		"Bl" : ["local_operations_one_is_working"      , "local operations up to: last finished working and entered"],
		"Cl" : ["local_operations_not_one_is_done"     , "local operations up to: first recognized the barrier is full and left"],
		"Dl" : ["local_operations_not_all_are_done"    , "local operations up to: all recognized the barrier is full and left"],
		"El" : ["local_operations_one_is_writing_inc"  , "local operations up to: no one is writing"],
		"As" : ["shared_operations_all_are_working"    , "shared operations up to: first finished working and entered"],
		"Bs" : ["shared_operations_one_is_working"     , "shared operations up to: last finished working and entered"],
		"Cs" : ["shared_operations_not_one_is_done"    , "shared operations up to: first recognized the barrier is full and left"],
		"Ds" : ["shared_operations_not_all_are_done"   , "shared operations up to: all recognized the barrier is full and left"],
		"Es" : ["shared_operations_one_is_writing_inc" , "shared operations up to: no one is writing"],
	}

	for k in sorted(queries.keys()) :
		query = queries[k]
		t += "// (%s) and (%se) %s\n" % (k, k, query[1])
		t += "R{\"%s\"}=? [C<=time]\n" % query[0]
		t += "R{\"%s\"}=? [F all_are_done]\n" % query[0]
		t += "\n"

	t += "// operation counting queries end\n\n"
	# ### operation counting queries end

	t += "const double time=ticks/base_rate;\n"
	t += "const double ticks;\n"

	t += "\n"

	t += "// *** thread end ***\n"

	return t

# ### helper ### ##############################################################
def everyThreadButMyself (p, threadCount) :
	l = []
	for j in range(0, threadCount):
		if p != j:
			l += [j]
	return l

def forMe(p, threadCount) :
	#me and all but one other
	l = []
	for fromWhom in range(0, threadCount) :
		if fromWhom != p :
			s = ""
			for forWhom in range(0, threadCount) :
				if forWhom != fromWhom :
					s += str(forWhom)
			l += [s]
	return l

# #############################################################################
helpMessage = \
"""
 gen.py [OPTIONS] [outfile-prefix]

  -h, --help              print help message
  -n <nr>                 set thread count
  --work  <ticks>         set tick count for a work period [default 1]
  --read  <ticks>         set tick count for a cache read  [default 50]
  --write <ticks>         set tick count a cache write     [default 100]

  --debug                                                  [default False]
"""

if __name__ == "__main__":

	threadCount = 0
	filePrefix = modelFileName = correctnessPropertiesFileName = quantitativePropertiesFileName = ""

	workTicks  = 1
	readTicks  = 50
	writeTicks = 100
	debug = False

	i = 1
	while i < len(sys.argv):
		if sys.argv[i] == "-h" or sys.argv[i] == "--help":
			print (helpMessage)
			exit(0)
		elif sys.argv[i] == "-n" or sys.argv[i] == "--threads":
			threadCount = int(sys.argv[i+1])
			i += 1
		elif sys.argv[i] == "--work":
			workTicks = int(sys.argv[i+1])
			i += 1
		elif sys.argv[i] == "--read":
			readTicks = int(sys.argv[i+1])
			i += 1
		elif sys.argv[i] == "--write":
			writeTicks = int(sys.argv[i+1])
			i += 1
		elif sys.argv[i] == "--debug":
			debug = True
		elif sys.argv[i].startswith("--") :
			print ("unknown parameter: " + sys.argv[i])
			exit(-1)
		elif filePrefix == "":
			filePrefix = sys.argv[i]
			modelFileName = filePrefix + ".pm"
			correctnessPropertiesFileName = filePrefix + "-correctness.props"
			quantitativePropertiesFileName = filePrefix + "-quantitative.props"
		else :
			print ("unknown parameter: " + sys.argv[i])
			exit(-1)
		i += 1

	if len(filePrefix) == 0 :
		print(helpMessage)
		exit(0)

	assert threadCount >= 2
	assert workTicks   >= 1
	assert readTicks   >= 1
	assert writeTicks  >= 1

	modelString = ""
	correctnessPropertiesString = ""

	modelString, correctnessPropertiesString = generateModel(threadCount, workTicks, readTicks, writeTicks, debug)

	correctnessPropertiesString += generateCorrectnessProperties(threadCount)

	quantitativePropertiesString = generateQuantitativeProperties(threadCount)

	f = open(modelFileName, 'w')
	f.write(modelString)
	f.close()

	f = open(correctnessPropertiesFileName, 'w')
	f.write(correctnessPropertiesString)
	f.close()

	f = open(quantitativePropertiesFileName, 'w')
	f.write(quantitativePropertiesString)
	f.close()

