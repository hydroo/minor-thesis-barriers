#! /usr/bin/env python3

import sys

def generateModel(processCount, workTicks, readTicks, writeTicks, getTicks, putTicks, debug) :

	s = "" # model
	t = "" # correctness props

	s += "ctmc\n"
	s += "\n"

	s += generateConstants(processCount, workTicks, readTicks, writeTicks, getTicks, putTicks)
	s += "\n"

	s += "// *** main process begin ***\n"
	s += "\n"
	#s += "// * you always need to add transitions for all sync labels in var_shared, otherwise\n"
	#s += "//   they will not be recognized as synchronized and are able to fire always\n"
	#s += "//\n"
	#s += "// * not all labels are for sync. but for easier debugging in the simulator: work_*, done_*\n"
	#s += "// * always read using [var_read_n]\n"
	#s += "// * always write using [var_set_to_*_n]\n"
	#s += "//\n"
	#s += "// * always introduce an atomic op using [bar_atomic_begin_n]\n"
	#s += "// * use read and writes as usual in between\n"
	#s += "// * always end an atomic op using [bar_atomic_end_n]\n"
	#s += "\n"

	s += generateProcess(0, processCount)
	s += "\n"

	s += "// *** main process end ***\n\n"

	s += "// *** process labels begin ***\n\n"
	s += generateLabels(processCount)
	s += "\n"
	s += "// *** process labels end ***\n\n"

	s += "// *** process copies begin ***\n\n"
	for p in range(1, processCount) :
		s += generateProcess(p, processCount)
		s += "\n"

	s += "// *** process copies end ***\n\n"

	s += "// *** process rewards begin ***\n\n"
	s += generateRewards()
	s += "\n"
	s += "// *** process rewards end ***\n\n"

	return s, t

def generateConstants(processCount, workTicks, readTicks, writeTicks, getTicks, putTicks) :

	s = ""

	s = "const process_count = " + str(processCount) + ";\n"

	s += "\n"

	s += "const work_ticks   = " + str(workTicks)  + ";\n"
	s += "const read_ticks   = " + str(readTicks)  + ";\n"
	s += "const write_ticks  = " + str(writeTicks) + ";\n"
	s += "const get_ticks    = " + str(getTicks)   + ";\n"
	s += "const put_ticks    = " + str(putTicks)   + ";\n"

	s += "\n"

	s += "// rates\n"
	s += "const double base_rate = 1000.0;\n"
	s += "const double tick      = base_rate / 1.0;\n"
	s += "const double work      = tick / work_ticks;\n"
	s += "const double read      = tick / read_ticks;\n"
	s += "const double write     = tick / write_ticks;\n"
	s += "const double get       = tick / get_ticks;\n"
	s += "const double put       = tick / put_ticks;\n"

	s += "\n"

	s += "// process locations\n"
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

def generateProcess(p, processCount) :

	s = ""

	s += "module process_#\n"

	s += "    l_# : [l_init..l_done] init l_init;\n"

	s += "\n"

	s += "    [work_#]             l_#=l_work                -> work : (l_#'=l_atomic_begin);\n"
	s += "\n"
	s += "    [bar_atomic_begin_#] l_#=l_atomic_begin        ->        (l_#'=l_read);\n"
	s += "\n"
	s += "    [bar_read_#]         l_#=l_read                ->        (l_#'=l_write);\n"
	s += "\n"

	# set to 2 will never be triggered, but is needed for sync
	for i in range(1, processCount+1) :
		s += "    [bar_set_to_" + str(i-1) + "_#]     l_#=l_write      & bar =" + str(i) + " ->        (l_#'=l_atomic_end);\n"

	s += "\n"
	s += "    [bar_atomic_end_#]   l_#=l_atomic_end          ->        (l_#'=l_wait);\n"
	s += "\n"
	s += "    [bar_read_#]         l_#=l_wait       & bar!=0 ->        true;\n"
	s += "    [bar_read_#]         l_#=l_wait       & bar =0 ->        (l_#'=l_done);\n"
	s += "\n"
	s += "    [done_#]             l_#=l_done                ->        true;\n"

	s += "endmodule\n"

	return s.replace('#', str(p))

def generateRewards() :
	s = ""

	s += "// state rewards\n"
	s += "rewards \"time\"\n"
	s += "\t" + "true : base_rate;\n"
	s += "endrewards\n"

	s += "\n"

	s += "rewards \"time_all_are_working\"\n"
	s += "\t" + "all_are_working : base_rate;\n"
	s += "endrewards\n"

	s += "\n"

	s += "rewards \"time_not_all_are_working\"\n"
	s += "\t" + "!all_are_working : base_rate;\n"
	s += "endrewards\n"

	s += "\n"

	s += "rewards \"time_one_is_working\"\n"
	s += "\t" + "one_is_working : base_rate;\n"
	s += "endrewards\n"

	s += "\n"

	s += "rewards \"time_not_one_is_working\"\n"
	s += "\t" + "!one_is_working : base_rate;\n"
	s += "endrewards\n"

	s += "\n"

	s += "rewards \"time_one_is_writing\"\n"
	s += "\t" + "one_is_writing : base_rate;\n"
	s += "endrewards\n"

	s += "\n"

	s += "rewards \"time_one_is_reading\"\n"
	s += "\t" + "one_is_reading : base_rate;\n"
	s += "endrewards\n"

	s += "\n"

	s += "rewards \"time_one_is_done\"\n"
	s += "\t" + "one_is_done : base_rate;\n"
	s += "endrewards\n"

	s += "\n"

	s += "rewards \"time_not_one_is_done\"\n"
	s += "\t" + "!one_is_done : base_rate;\n"
	s += "endrewards\n"

	s += "\n"

	s += "rewards \"time_not_all_are_done\"\n"
	s += "\t" + "!all_are_done : base_rate;\n"
	s += "endrewards\n"

	s += "\n"

	s += "rewards \"time_all_are_done\"\n"
	s += "\t" + "all_are_done : base_rate;\n"
	s += "endrewards\n"

	return s

def generateLabels(processCount) :

	s = ""

	s += "formula one_is_done                  = " + " | ".join(["l_%d=l_done" % i for i in range(0, processCount)]) + ";\n"
	s += "formula all_are_done                 = " + " & ".join(["l_%d=l_done" % i for i in range(0, processCount)]) + ";\n"
	#s += "formula exactly_one_is_done          = " +  " | ".join([ "(l_%d = l_done & " % i + " & ".join(["l_%d < l_done" % j for j in range(0, processCount) if j!=i]) + ")" for i in range(0, processCount)]) + ";\n"
	#s += "label \"one_is_done\"                  = one_is_done;\n"
	#s += "label \"all_are_done\"                 = all_are_done;\n"
	#s += "label \"exactly_one_is_done\"          = exactly_one_is_done;\n"

	s += "\n"

	s += "formula one_is_working               = " +  " | ".join([ "l_%d = l_work" % i for i in range(0, processCount)]) + ";\n"
	s += "formula all_are_working              = " +  " & ".join([ "l_%d = l_work" % i for i in range(0, processCount)]) + ";\n"
	s += "formula exactly_one_is_done_working  = " +  " | ".join([ "(l_%d >= l_atomic_begin & " % i + " & ".join(["l_%d = l_work" % j for j in range(0, processCount) if j!=i]) + ")" for i in range(0, processCount)]) + ";\n"
	#s += "label \"one_is_working\"               = one_is_working;\n"
	#s += "label \"all_are_working\"              = all_are_working;\n"
	#s += "label \"exactly_one_is_done_working\"  = exactly_one_is_done_working;\n"

	s += "\n"

	s += "formula one_is_writing               = !all_are_working & (" + " | ".join([ "l_%d <= l_atomic_end" % i for i in range(0, processCount)]) + ");\n"
	s += "formula all_are_writing              = !one_is_working  & (" + " & ".join([ "l_%d <= l_atomic_end" % i for i in range(0, processCount)]) + ");\n"
	s += "formula none_are_writing             = !one_is_writing;\n"
	#s += "label \"one_is_writing\"               = one_is_writing;\n"
	#s += "label \"all_are_writing\"              = all_are_writing;\n"

	s += "\n"

	s += "formula one_is_reading               = " + " | ".join(["l_%d=l_wait & (" % i + " & ".join(["l_%d>=l_wait" % j for j in range(0, processCount) if i!=j]) + ")" for i in range(0, processCount)]) + ";\n"
	s += "formula all_are_reading_or_done      = " + " & ".join(["l_%d>=l_wait" % i for i in range(0, processCount)]) + ";\n"
	#s += "label \"one_is_reading\"             = one_is_reading;\n"
	#s += "label \"all_are_reading_or_done\"    = all_are_reading_or_done;\n"

	return s

# ### correctness props ### ###################################################
def generateCorrectnessProperties(processCount) :

	t = ""

	t += "// *** process begin ***\n\n"

	t += "P>=1 [F all_are_done]\n"
	t += "\n"

	t += "// the following 4 queries partition the state space and have to add up to the total state count\n"
	t += "filter(+, P=? [all_are_working]) + filter(+, P=? [one_is_writing]) + filter(+, P=? [one_is_reading]) + filter(+, P=? [all_are_done])\n"

	t += "\n"

	t += "// *** process end ***\n"

	return t

# ### quantitative props ### ##################################################
def generateQuantitativeProperties(processCount) :

	t = ""

	t += "// *** process begin ***\n\n"

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

	diffQueries = [
		["D", "B", "from last to enter to last to leave"],
		["D", "C", "from first to leave to last to leave"]
	]

	for query in diffQueries :
		q = basicQueries[query[0]]
		u = basicQueries[query[1]]
		t += "// (%s-%s)e %s\n" % (query[0], query[1], query[2])
		# no better than expected value difference is possible at the moment
		t += "(R{\"time\"}=? [F all_are_done] - R{\"%s\"}=? [F all_are_done]) - (R{\"time\"}=? [F all_are_done] - R{\"%s\"}=? [F all_are_done])\n" % (q[0], u[0]) # correct
		t += "\n"

	t += "// sascha queries A-D end\n\n"

	# ### partition queries begin
	t += "// partition queries begin\n\n"

	# the following 4 queries partition the state space.
	# useful for a diagram showing with which percentage we are in which phase at a certain point in time
	# perhaps as a stacked diagram
	queries = {
		#key : [query, comment]
		"Ap" : ["time_all_are_working" , "time up to: first finished working and entered"],
		"Ep" : ["time_one_is_writing"  , "time spent writing"],
		"Fp" : ["time_one_is_reading"  , "time spent reading"],
		"Dp" : ["time_all_are_done"    , "time all are done" ],
	}

	for k in sorted(queries.keys()) :
		query = queries[k]
		t += "// (%s) and (%se) %s\n" % (k, k, query[1])
		t += "R{\"%s\"}=? [I=time] / base_rate\n" % query[0] # correct
		t += "R{\"%s\"}=? [F all_are_done]\n" % query[0]     # correct
		t += "\n"

	t += "// partition queries end\n\n"
	# ### partition queries end

	# ### cumulative queries begin
	# shows how much time has been spent in different parts of the algorithm
	# if simulated up to a certain point
	#
	# in order for cumulative queries to make sense here we have to invert some labels
	t += "// cumulative queries begin\n\n"

	queries = {
		#key : [query, comment]
		"Ac" : ["time_all_are_working" , "time up to: first finished working and entered"],
		"Bc" : ["time_one_is_working"  , "time up to: last finished working and entered"],
		"Cc" : ["time_not_one_is_done" , "time up to: first recognized the barrier is full and left"],
		"Dc" : ["time_not_all_are_done", "time up to: all recognized the barrier is full and left"],
		"Ec" : ["time_one_is_writing"  , "time spent writing"],
		"Fc" : ["time_one_is_reading"  , "time spent reading"],
	}

	for k in sorted(queries.keys()) :
		query = queries[k]
		t += "// (%s) and (%se) %s\n" % (k, k, query[1])
		t += "R{\"%s\"}=? [C<=time]\n" % query[0]
		t += "R{\"%s\"}=? [F all_are_done]\n" % query[0]
		t += "\n"

	t += "// cumulative queries end\n\n"
	# ### cumulative queries end

	t += "const double time=ticks/base_rate;\n"
	t += "const double ticks;\n"

	t += "\n"

	t += "// *** process end ***\n"

	return t

# ### helper ### ##############################################################
def everyProcessButMyself (p, processCount) :
	l = []
	for j in range(0, processCount):
		if p != j:
			l += [j]
	return l

def forMe(p, processCount) :
	#me and all but one other
	l = []
	for fromWhom in range(0, processCount) :
		if fromWhom != p :
			s = ""
			for forWhom in range(0, processCount) :
				if forWhom != fromWhom :
					s += str(forWhom)
			l += [s]
	return l

# #############################################################################
helpMessage = \
"""
 gen.py [OPTIONS] [outfile-prefix]

  -h, --help              print help message
  -n <nr>                 set process count
  --work  <ticks>         set tick count for a work period        [default 1]
  --read  <ticks>         set tick count for a local read         [default 1]
  --write <ticks>         set tick count for a local write        [default 1]
  --get   <ticks>         set tick count for a remote read (get)  [default 100]
  --put   <ticks>         set tick count for a remote write (put) [default 100]

  --debug                                                         [default False]
"""

if __name__ == "__main__":

	processCount = 0
	filePrefix = modelFileName = correctnessPropertiesFileName = ""

	workTicks  = 1
	readTicks  = 1
	writeTicks = 1
	getTicks   = 100
	putTicks   = 100
	debug = False

	i = 1
	while i < len(sys.argv):
		if sys.argv[i] == "-h" or sys.argv[i] == "--help":
			print (helpMessage)
			exit(0)
		elif sys.argv[i] == "-n" or sys.argv[i] == "--processes":
			processCount = int(sys.argv[i+1])
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
		elif sys.argv[i] == "--get":
			getTicks = int(sys.argv[i+1])
			i += 1
		elif sys.argv[i] == "--put":
			putTicks = int(sys.argv[i+1])
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

	assert processCount >= 2
	assert workTicks   >= 1
	assert readTicks   >= 1
	assert writeTicks  >= 1
	assert getTicks    >= 1
	assert putTicks    >= 1

	modelString = ""
	correctnessPropertiesString = ""

	modelString, correctnessPropertiesString = generateModel(processCount, workTicks, readTicks, writeTicks, getTicks, putTicks, debug)

	correctnessPropertiesString  = generateCorrectnessProperties(processCount)

	quantitativePropertiesString = generateQuantitativeProperties(processCount)

	f = open(modelFileName, 'w')
	f.write(modelString)
	f.close()

	f = open(correctnessPropertiesFileName, 'w')
	f.write(correctnessPropertiesString)
	f.close()

	f = open(quantitativePropertiesFileName, 'w')
	f.write(quantitativePropertiesString)
	f.close()

