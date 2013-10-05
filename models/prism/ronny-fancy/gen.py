#! /usr/bin/env python3

import math
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
	s += "// * last _# at labels and variables is always the id of the \"owning\" process "
	s += "//\n"
	s += "\n"
	s += "// * no label is for sync. all are for easyier debugging in the simulator\n"
	s += "\n"
	s += "// * changing read and write rates does not work anymore because we collapsed some of those transitions (optimization)\n"
	s += "\n"

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

	for i in range(0, processCount+0) :
		s += "const int me_" + str(i) + " = " + str(i) + ";\n"
	s += "\n"

	for i in range(0, processCount) :
		s += "const int me_bit_" + str(i) + " = " + str(2**i) + ";\n"
	s += "\n"

	s += "const int empty = 0;\n"
	s += "const int full  = "
	for i in range(0, processCount) :
		s += "me_bit_" + str(i) + " + "
	s += "0;\n"
	s += "\n"

	s += "const work_ticks  = " + str(workTicks)  + ";\n"
	s += "const read_ticks  = " + str(readTicks)  + ";\n"
	s += "const write_ticks = " + str(writeTicks) + ";\n"
	s += "const get_ticks   = " + str(getTicks)   + ";\n"
	s += "const put_ticks   = " + str(putTicks)   + ";\n"

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
	s += "const l_init   = 0;\n"
	s += "const l_work   = l_init;\n"
	s += "const l_write  = 1;\n"
	s += "const l_search = 2;\n"
	s += "const l_test   = 3;\n"
	s += "const l_done   = 4;\n"

	return s

def generateProcess(p, processCount) :

	s = ""

	s += "module process_#\n"

	s += "    l_#   : [l_init..l_done]     init l_init;\n"
	s += "    bar_# : [0..full]            init 0;\n"
	s += "    i_#   : [0..process_count-1] init me_#;\n"

	s += "\n"

	s += "    [work_#]     l_#=l_work  -> work  : (l_#'=l_write);\n"
	s += "\n"

	s += "    [write_#]    l_#=l_write -> write : (l_#'=l_search) & (bar_#'=me_bit_#);\n"

	s += "\n"

	s += "    // bar_# = bar_# | bar_x. all combinations for all i's\n"
	s += "    // emulates a foot controlled loop by clevery using +1 and i increment\n"
	for i in range(0, processCount) :
		s += "    [search_#]   l_#=l_search & i_#=%d & mod(floor(bar_#/me_bit_%d),2) = 1                        ->  read  : (l_#'=l_search) & (i_#'=mod(i_#+1, process_count));\n" % (i, (i + 1) % processCount)
		for j in range(0, 2**processCount) :
			for k in range(0, 2**processCount) :
				s += "    [search_#]   l_#=l_search & i_#=%d & mod(floor(bar_#/me_bit_%d),2) = 0 & bar_#=%2d & bar_%d=%2d  ->  get   : (l_#'=l_test)   & (i_#'=mod(i_#+1, process_count)) & (bar_#'=%d);\n" % (i, (i+1) % processCount, j, (i+1) % processCount, k, j|k)

	s += "\n"

	s += "    [test_#]     l_#=l_test   & bar_# =full -> read : (l_#'=l_done);\n"
	s += "    [test_#]     l_#=l_test   & bar_#!=full -> read : (l_#'=l_search);\n"

	s += "\n"

	s += "    [done_#]     l_#=l_done                 ->        true;\n"

	s += "endmodule\n"

	return s.replace('#', str(p))

def generateRewards() :

	s = ""

	s += "// state rewards\n"
	s += "rewards \"time\"\n"
	s += "    true : base_rate;\n"
	s += "endrewards\n\n"

	s += "rewards \"time_all_are_working\"\n"
	s += "    all_are_working : base_rate;\n"
	s += "endrewards\n\n"

	s += "rewards \"time_not_all_are_working\"\n"
	s += "    !all_are_working : base_rate;\n"
	s += "endrewards\n\n"

	s += "rewards \"time_one_is_working\"\n"
	s += "    one_is_working : base_rate;\n"
	s += "endrewards\n\n"

	s += "rewards \"time_not_one_is_working\"\n"
	s += "    !one_is_working : base_rate;\n"
	s += "endrewards\n\n"

	s += "rewards \"time_one_is_done\"\n"
	s += "    one_is_done : base_rate;\n"
	s += "endrewards\n\n"

	s += "rewards \"time_not_one_is_done\"\n"
	s += "    !one_is_done : base_rate;\n"
	s += "endrewards\n\n"

	s += "rewards \"time_not_all_are_done\"\n"
	s += "    !all_are_done : base_rate;\n"
	s += "endrewards\n\n"

	s += "rewards \"time_all_are_done\"\n"
	s += "    all_are_done : base_rate;\n"
	s += "endrewards\n\n"

	return s

def generateLabels(processCount) :

	s = ""

	s += "formula one_is_done       = " + " | ".join(["l_%d = l_done" % i for i in range(0, processCount)]) + ";\n"
	s += "formula all_are_done      = " + " & ".join(["l_%d = l_done" % i for i in range(0, processCount)]) + ";\n"
	#s += "formula exactly_one_is_done          = " +  " | ".join([ "(l_%d = l_done & " % i + " & ".join(["l_%d < l_done" % j for j in range(0, processCount) if j!=i]) + ")" for i in range(0, processCount)]) + ";\n"
	#s += "label \"one_is_done\"                  = one_is_done;\n"
	#s += "label \"all_are_done\"                 = all_are_done;\n"
	#s += "label \"exactly_one_is_done\"          = exactly_one_is_done;\n"

	s += "\n"

	s += "formula one_is_working    = " +  " | ".join([ "l_%d = l_work" % i for i in range(0, processCount)]) + ";\n"
	s += "formula all_are_working   = " +  " & ".join([ "l_%d = l_work" % i for i in range(0, processCount)]) + ";\n"
	##s += "formula exactly_one_is_done_working  = " +  " | ".join([ "(l_%d >= l_atomic_begin & " % i + " & ".join(["l_%d = l_work" % j for j in range(0, processCount) if j!=i]) + ")" for i in range(0, processCount)]) + ";\n"
	#s += "label \"one_is_working\"               = one_is_working;\n"
	#s += "label \"all_are_working\"              = all_are_working;\n"
	#s += "label \"exactly_one_is_done_working\"  = exactly_one_is_done_working;\n"

	#s += "\n"

	return s

# ### correctness props ### ###################################################
def generateCorrectnessProperties(processCount) :

	t = ""

	t += "// *** process begin ***\n\n"

	t += "P>=1 [F all_are_done]\n"
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

	## ### partition queries "one" begin
	#t += "// partition queries \"one\" begin\n\n"

	## the following queries partition the state space.
	## useful for a diagram showing with which percentage we are in which phase at a certain point in time
	## perhaps as a stacked diagram
	#queries = [
	#	#[key, query, comment]
	#	["Ap", "time_all_are_working" , "time up to: first finished working and entered"],
	#	["Cp", "time_one_is_done"     , "time all are done" ],
	#]
	#for r in range(0, int(math.log(maxDist, 2)) + 1) :
	#	queries.insert(-1, ["%dp" % r, "time_round_%d_one" % r, "time from the first entered round %d until the first entered round %d" % (r, r+1)])
	#for query in queries :
	#	t += "// (%s) and (%se) %s\n" % (query[0], query[0], query[2])
	#	t += "R{\"%s\"}=? [I=time] / base_rate\n" % query[1]
	#	t += "R{\"%s\"}=? [F all_are_done]\n" % query[1]
	#	t += "\n"

	#t += "// partition queries \"one\" end\n\n"
	## ### partition queries "one" end

	## ### partition queries "all" begin
	#t += "// partition queries \"all\" begin\n\n"

	#queries = [
	#	#[key, query, comment]
	#	["Bp", "time_one_is_working" , "time up to: first finished working and entered"],
	#	["Dp", "time_all_are_done"   , "time all are done" ],
	#]
	#for r in range(0, int(math.log(maxDist, 2)) + 1) :
	#	queries.insert(-1, ["%dp" % r, "time_round_%d_all" % r, "time from the last entered round %d until the last entered round %d" % (r, r+1)])
	#for query in queries :
	#	t += "// (%s) and (%se) %s\n" % (query[0], query[0], query[2])
	#	t += "R{\"%s\"}=? [I=time] / base_rate\n" % query[1]
	#	t += "R{\"%s\"}=? [F all_are_done]\n" % query[1]
	#	t += "\n"


	#t += "// partition queries \"all\" end\n\n"
	## ### partition queries "all" end

	# ### cumulative queries begin
	# shows how much time has been spent in different parts of the algorithm
	# if simulated up to a certain point
	#
	# in order for cumulative queries to make sense here we have to invert some labels
	t += "// cumulative queries begin\n\n"

	queries = [
		#[key, query, comment]
		["Ac", "time_all_are_working" , "time up to: first finished working and entered"],
		["Bc", "time_one_is_working"  , "time up to: last finished working and entered"],
		["Cc", "time_not_one_is_done" , "time up to: first recognized the barrier is full and left"],
		["Dc", "time_not_all_are_done", "time up to: all recognized the barrier is full and left"],
	]
	#for r in range(0, int(math.log(maxDist, 2)) + 1) :
	#	queries.insert(-2, ["%dc" % r, "time_up_to_round_%d_one" % r, "time up to: first entered round %d" % (r+1)])
	#	queries.insert(-2, ["%dc" % r, "time_up_to_round_%d_all" % r, "time up to: last entered round %d" % (r+1)])

	for query in queries :
		t += "// (%s) and (%se) %s\n" % (query[0], query[0], query[2])
		t += "R{\"%s\"}=? [C<=time]\n" % query[1]
		t += "R{\"%s\"}=? [F all_are_done]\n" % query[1]
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

