#! /usr/bin/env python3

import sys

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

	s_, t_ = shared_memory.generateVariable("bar", "[0..thread_count]",  "thread_count", [str(i) for i in range(0, threadCount)], threadCount, debug)
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
	s += generateRewards()
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
	s += "    [done_#]             l_#=l_done                ->        true;\n"

	s += "endmodule\n"

	return s.replace('#', str(p))

def generateRewards() :
	s = ""
	s += "rewards \"time\"\n"
	s += "\ttrue : 1;\n"
	s += "endrewards\n"
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
	s += "formula exactly_one_is_done_working  = " +  " | ".join([ "(l_%d = l_atomic_begin & " % i + " & ".join(["l_%d = l_work" % j for j in range(0, threadCount) if j!=i]) + ")" for i in range(0, threadCount)]) + ";\n"
	#s += "label \"one_is_working\"               = one_is_working;\n"
	#s += "label \"all_are_working\"              = all_are_working;\n"
	#s += "label \"exactly_one_is_done_working\"  = exactly_one_is_done_working;\n"

	s += "\n"

	s += "formula one_is_writing               = !all_are_working & (" + " | ".join([ "l_%d <= l_atomic_end" % i for i in range(0, threadCount)]) + ");\n"
	s += "formula all_are_writing              = !one_is_working  & (" + " & ".join([ "l_%d <= l_atomic_end" % i for i in range(0, threadCount)]) + ");\n"
	s += "formula none_are_writing             = !one_is_writing;\n"
	#s += "label \"one_is_writing\"               = one_is_writing;\n"
	#s += "label \"all_are_writing\"              = all_are_writing;\n"

	s += "\n"

	s += "formula one_is_reading               = " + " | ".join(["l_%d=l_wait" % i for i in range(0, threadCount)]) + ";\n"
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

	t += "// *** thread end ***\n"

	return t

# ### quantitative props ### ##################################################
def generateQuantitativeProperties(threadCount) :

	t = ""

	t += "// *** thread begin ***\n\n"

	basicQuerySpecs = {
		"A" : ["F", "!all_are_working"         , "first finished working phase and entered the barrier"],
		"B" : ["F", "!one_is_working "         , "last finished working phase and entered the barrier"],
		"C" : ["F",  "one_is_done"             , "first recognized the barrier is full and left"],
		"D" : ["F",  "all_are_done"            , "all recognized the barrier is full and left"],
		"E" : ["F",  "one_is_writing"          , "at least one is still writing"],
		"F" : ["F",  "all_are_reading_or_done" , "all are reading or already finished"]}

	basicQueryStrings = {}
	for k in basicQuerySpecs.keys() :
		query = basicQuerySpecs[k]
		basicQueryStrings[k      ] = ["P=? [%s<=time (%s)]" % (query[0], query[1]), "%s" % (query[2])]
		basicQueryStrings[k + "e"] = ["base_rate * R{\"time\"}=? [%s (%s)]" % (query[0], query[1]), ""]

	queryStrings = {}
	#wrong
	queryStrings["C-A"]  = ["(" + basicQueryStrings["C" ][0] + ") - ("+ basicQueryStrings["A" ][0] + ")", "from the first entered until the first is done"]
	#correct
	queryStrings["C-Ae"] = ["(" + basicQueryStrings["Ce"][0] + ") - ("+ basicQueryStrings["Ae"][0] + ")", ""]
	#queryStrings["D-A"]  = ["(" + basicQueryStrings["D" ][0] + ") - ("+ basicQueryStrings["A" ][0] + ")", ""]
	#queryStrings["D-Ae"] = ["(" + basicQueryStrings["De"][0] + ") - ("+ basicQueryStrings["Ae"][0] + ")", ""]
	#wrong
	queryStrings["D-B"]  = ["(" + basicQueryStrings["D" ][0] + ") - ("+ basicQueryStrings["B" ][0] + ")", "from all entered until all are done"]
	#correct
	queryStrings["D-Be"] = ["(" + basicQueryStrings["De"][0] + ") - ("+ basicQueryStrings["Be"][0] + ")", ""]
	#wrong
	queryStrings["D-C"]  = ["(" + basicQueryStrings["D" ][0] + ") - ("+ basicQueryStrings["C" ][0] + ")", "from all entered until one is done"]
	#correct
	queryStrings["D-Ce"] = ["(" + basicQueryStrings["De"][0] + ") - ("+ basicQueryStrings["Ce"][0] + ")", ""]

	#wrong
	queryStrings["F-E"]  = ["(" + basicQueryStrings["F" ][0] + ") - ("+ basicQueryStrings["E" ][0] + ")", "%s" % "writing phase: from the first entered until the all finished writing"]
	#correct
	queryStrings["F-Ee"] = ["(" + basicQueryStrings["Fe"][0] + ") - ("+ basicQueryStrings["Ee"][0] + ")", "%s" % ""]

	#wrong
	queryStrings["D-F"]  = ["(" + basicQueryStrings["D" ][0] + ") - ("+ basicQueryStrings["F" ][0] + ")", "%s" % "reading phase: from all are read to all are done"]
	#correct
	queryStrings["D-Fe"] = ["(" + basicQueryStrings["De"][0] + ") - ("+ basicQueryStrings["Fe"][0] + ")", "%s" % ""]

	t += "// e for expected value\n"
	t += "\n"

	for query_ in sorted(basicQueryStrings.items()) + sorted(queryStrings.items()) :
		k     = query_[0]
		query = query_[1]

		t += "// (%s) %s\n" % (k, query[1])
		t += "%s\n" % query[0]
		t += "\n"

	t += "\n"

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

  --debug
"""

if __name__ == "__main__":

	threadCount = 0
	filePrefix = modelFileName = correctnessPropertiesFileName = ""

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

