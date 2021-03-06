#! /usr/bin/env python3

import math
import sys

def generateModel(processCount, workTicks, getTicks, debug) :

	s = "" # model
	t = "" # correctness props

	s += "ctmc\n"
	s += "\n"

	s += generateConstants(processCount, workTicks, getTicks)
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
	s += generateRewards(processCount)
	s += "\n"
	s += "// *** process rewards end ***\n\n"

	return s, t

def generateConstants(processCount, workTicks, getTicks) :

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
	s += "const get_ticks   = " + str(getTicks)   + ";\n"

	s += "\n"

	s += "// rates\n"
	s += "const double base_rate = 1000.0;\n"
	s += "const double tick      = base_rate / 1.0;\n"
	s += "const double rare      = tick / 1000000;\n"
	s += "const double work      = tick / work_ticks;\n"
	s += "const double get       = tick / get_ticks;\n"

	s += "\n"

	s += "// process locations\n"
	s += "// all names describe the behaviour of the next transition\n"
	s += "const l_init   = 0;\n"
	s += "const l_work   = l_init;\n"
	s += "const l_search = 1;\n"
	s += "const l_done   = 2;\n"

	return s

def generateProcess(p, processCount) :

	s = ""

	full = 0
	for i in range(0, processCount) :
		full = full | 2**i

	s += "module process_#\n"

	s += "    l_#   : [l_init..l_done]     init l_init;\n"
	s += "    bar_# : [0..full]            init 0;\n"
	s += "    i_#   : [0..process_count-1] init me_#;\n"

	s += "\n"

	s += "    [work_#]     l_#=l_work  -> work  : (l_#'=l_search) & (bar_#'=me_bit_#);\n"
	s += "\n"

	s += "\n"

	s += "    // bar_# = bar_# | bar_x. all combinations for all i's\n"
	s += "    // emulates a foot controlled loop by clevery using +1 and i increment\n"
	for i in range(0, processCount) :
		s += "    [search_%d_#] l_#=l_search & i_#=%d & mod(floor(bar_#/me_bit_%d),2) = 1                        ->  tick  : (l_#'=l_search) & (i_#'=mod(i_#+1, process_count));\n" % ((i+1) % processCount, i, (i+1) % processCount)
		for j in range(0, 2**processCount) :
			for k in range(0, 2**processCount) :
				if j|k != full :
					s += "    [search_%d_#] l_#=l_search & i_#=%d & mod(floor(bar_#/me_bit_%d),2) = 0 & bar_#=%2d & bar_%d=%2d  ->  get   : (l_#'=l_search) & (i_#'=mod(i_#+1, process_count)) & (bar_#'=%d);\n" % ((i+1) % processCount, i, (i+1) % processCount, j, (i+1) % processCount, k, j|k)
				else :
					s += "    [search_%d_#] l_#=l_search & i_#=%d & mod(floor(bar_#/me_bit_%d),2) = 0 & bar_#=%2d & bar_%d=%2d  ->  get   : (l_#'=l_done)   & (i_#'=mod(i_#+1, process_count)) & (bar_#'=%d);\n" % ((i+1) % processCount, i, (i+1) % processCount, j, (i+1) % processCount, k, j|k)

	s += "\n"

	s += "    [done_#]     l_#=l_done                 -> rare : true;\n"

	s += "endmodule\n"

	return s.replace('#', str(p))

def generateRewards(processCount) :

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

	s += "rewards \"remote_transfer_success\"\n"
	for i in range(0, processCount) :
		for j in range(0, processCount) :
			if i != j :
				s += "    [search_%d_%d] l_%d=l_search & mod(floor(bar_%d/me_bit_%d),2) = 0 & bar_%d!=0 : 1;\n" % (j, i, i, i, j, j)
	s += "endrewards\n\n"

	s += "rewards \"remote_transfer_fail\"\n"
	for i in range(0, processCount) :
		for j in range(0, processCount) :
			if i != j :
				s += "    [search_%d_%d] l_%d=l_search & mod(floor(bar_%d/me_bit_%d),2) = 0 & bar_%d =0 : 1;\n" % (j, i, i, i, j, j)
	s += "endrewards\n\n"

	s += "\n" + operationRewards("all_are_working", processCount)

	s += "\n" + operationRewards("one_is_working", processCount)

	s += "\n" + operationRewards("not_one_is_done", processCount)

	s += "\n" + operationRewards("not_all_are_done", processCount)

	return s

def operationRewards(guard, processCount) :

	s = ""

	maxDist = 2**math.floor(math.log(processCount-1, 2))

	if guard.startswith("not_") :
		guardName = "!" + guard[4:]
	else :
		guardName = guard
	localRewardName = "local_operations_" + guard
	remoteRewardName = "remote_operations_" + guard

	s += "rewards \"%s\"\n" % localRewardName
	for p in range(0, processCount) :
		s += "    [work_%d]     %s  : %d;\n" % (p, guardName, 1)
		for q in range(0, processCount) :
			s += "    [search_%d_%d] %s  : %d;\n" % (q, p, guardName, 1)
	s += "endrewards\n"

	s += "rewards \"%s\"\n" % remoteRewardName
	for p in range(0, processCount) :
		for i in range(0, processCount) :
			if (i+1) % processCount != p :
				s += "    [search_%d_%d] i_%d=%d & mod(floor(bar_%d/me_bit_%d),2) = 0 & %s : %d;\n" % ((i+1) % processCount, p, p, i, p, (i+1) % processCount, guardName, 1)
	s += "endrewards\n"

	# module process_#
	#    [work_#]      l_#=l_work  -> work  : (l_#'=l_search) & (bar_#'=me_bit_#)                          #(local op: 1, remote op: 0)

	# for i in range(0, processCount) :
	#    [search_%d_#] l_#=l_search & bar_# has  me_bit_%d      ->  tick : (l_#'=l_search) & (i_#'=i_#+1 % process_count))      #(1, 0)
	#    [search_%d_#] l_#=l_search & bar_# !has me_bit_%d ...  ->  get  : (l_#'=l_search) & (i_#'=i_#+1 % process_count)) ...  #(1, 1)
	#    [search_%d_#] l_#=l_search & bar_# !has me_bit_%d ...  ->  get  : (l_#'=l_done)   & (i_#'=i_#+1 % process_count)) ...  #(1, 1)

	#     [done_#]     l_#=l_done                               -> rare : true                                                  #(0, 0)
	# endmodule

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

	t += "// sascha queries A-D end\n\n"

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

	# ### remote transfer queries begin
	t += "// remote transfer queries begin\n\n"

	t += "//successful remote transfer range between 2*(n-1) = %d and n*(n-1) = %d\n" % (2*(processCount-1), processCount*(processCount-1))
	t += "R{\"remote_transfer_success\"}=? [F all_are_done]\n"
	t += "R{\"remote_transfer_fail\"}=? [F all_are_done]\n"
	t += "\n"

	t += "// remote transfer queries end\n\n"
	# ### remote transfer queries end

	# ### operation counting queries begin
	t += "// operation countingqueries begin\n\n"

	queries = [
		#[key, query, comment]
		["Al", "local_operations_all_are_working"     , "local operations up to: first finished working and entered"],
		["Ar", "remote_operations_all_are_working"    , "remote operations up to: first finished working and entered"],
		["Bl", "local_operations_one_is_working"      , "local operations up to: last finished working and entered"],
		["Br", "remote_operations_one_is_working"     , "remote operations up to: last finished working and entered"],
		["Cl", "local_operations_not_one_is_done"     , "local operations up to: first recognized the barrier is full and left"],
		["Cr", "remote_operations_not_one_is_done"    , "remote operations up to: first recognized the barrier is full and left"],
		["Dl", "local_operations_not_all_are_done"    , "local operations up to: all recognized the barrier is full and left"],
		["Dr", "remote_operations_not_all_are_done"   , "remote operations up to: all recognized the barrier is full and left"],
	]

	for query in queries :
		t += "// (%s) and (%se) %s\n" % (query[0], query[0], query[2])
		t += "R{\"%s\"}=? [C<=time]\n" % query[1]
		t += "R{\"%s\"}=? [F all_are_done]\n" % query[1]
		t += "\n"

	t += "// operation counting queries end\n\n"
	# ### operation counting queries end

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
  --get   <ticks>         set tick count for a remote read (get)  [default 100]

  --debug                                                         [default False]
"""

if __name__ == "__main__":

	processCount = 0
	filePrefix = modelFileName = correctnessPropertiesFileName = quantitativePropertiesFileName = ""

	workTicks  = 1
	getTicks   = 100
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
		elif sys.argv[i] == "--get":
			getTicks = int(sys.argv[i+1])
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
	assert workTicks    >= 1
	assert getTicks     >= 1

	modelString = ""
	correctnessPropertiesString = ""

	modelString, correctnessPropertiesString = generateModel(processCount, workTicks, getTicks, debug)

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

