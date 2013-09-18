#! /usr/bin/env python3

import sys

def generateModel(threadCount, workTicks, read_ticks, writeTicks, debug) :

	s = "" # model
	t = "" # correctness props

	s += generateModelType()
	s += "\n"

	s += generateConstants(threadCount)
	s += "\n"

	s += "// *** main thread begin ***\n\n"
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

	s_, t_ = generateSharedMemoryPrerequisites(threadCount)
	s += s_
	t += t_

	s += "\n"

	s_, t_ = generateSharedVariable("bar", "[0..thread_count]",  "thread_count", [str(i) for i in range(0, threadCount)], threadCount, debug)
	s += s_
	t += t_

	t += "\n"

	s += generateSharedMemoryRewards()
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

def generateModelType() :
	return "ctmc\n"

def generateConstants(threadCount) :

	s = ""

	s = "const thread_count = " + str(threadCount) + ";\n"

	s += "\n"

	s += "const work_ticks  = " + str(workTicks) + ";\n"

	s += "\n"

	s += "// rates\n"
	s += "const double base_rate = 1000.0;\n"
	s += "const double tick      = base_rate / 1.0;\n"
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
	s += "const l_exit         = 6;\n"

	return s

def generateThread(p, threadCount) :

	s = ""

	s += "module thread_#\n"

	s += "    l_# : [l_init..l_exit] init l_init;\n"

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
	s += "    [bar_read_#]         l_#=l_wait       & bar =0 ->        (l_#'=l_exit);\n"
	s += "\n"
	s += "    [done_#]             l_#=l_exit                ->        true;\n"

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

	for p in range(0, threadCount) :
		s += "formula done_# = l_# = l_exit; "
		s = s.replace('#', str(p))
	s += "\n"


	s += "formula one_done  = " + " | ".join(["done_%d" % i for i in range(0, threadCount)]) + ";\n"
	s += "formula all_done  = " + " & ".join(["done_%d" % i for i in range(0, threadCount)]) + ";\n"
	s += "formula none_done = !one_done;\n"

	s += "\n"

	s += "label \"one_done\" = one_done;\n"
	s += "label \"all_done\" = all_done;\n"

	s += "\n"

	s += "formula writing_phase = " +  " & ".join([ "l_%d <= l_atomic_end" % i for i in range(0, threadCount)]) + "; // all are before reading\n"
	s += "formula reading_phase = !all_done & " +  " & ".join([ "l_%d >= l_wait" % i for i in range(0, threadCount)]) + ";       // all are at least waiting, but we are not yet done\n"

	s += "\n"

	s += "label \"writing_phase\" = writing_phase;\n"
	s += "label \"reading_phase\" = reading_phase;\n"

	return s

# ### shared memory ###########################################################

def generateSharedMemoryPrerequisites(threadCount) :

	s = ""
	t = ""

	for i in range(0, threadCount) :
		s += "const me_" + str(i) + " = " + str(i) + "; "
	s += "\n"
	for i in range(0, threadCount) :
		s += "const me_bit_" + str(i) + " = " + str(2**i) + "; "
	
	s += "\n"

	s += "const empty = 0; "
	s += "const full  = "
	for i in range(0, threadCount) :
		s += "me_bit_" + str(i) + " + "
	s += "0;\n"

	s += "\n"

	s += "const someoneIsModified   = 0;\n"
	s += "const someoneDoesAtomicOp = 1;\n"
	s += "const someAreShared       = 2;\n"

	s += "\n"

	s += "const read_ticks         = " + str(readTicks) + ";\n"
	s += "const write_ticks        = " + str(writeTicks) + ";\n"
	s += "const atomic_begin_ticks = write_ticks;\n"

	s += "\n"

	s += "const double read         = tick / read_ticks;\n"
	s += "const double write        = tick / write_ticks;\n"
	s += "const double atomic_begin = tick / atomic_begin_ticks;\n"

	return s, t

def generateSharedVariable(name, typee, init, values, threadCount, debug) :

	s = ""

	s += generatePseudoGlobalVariable(name, typee, init, values, threadCount)

	s += "\n"

	s += "module var_shared\n"

	s += "\tvar_state : [someoneIsModified..someAreShared] init someoneIsModified;\n"
	s += "\tvar_who   : [empty..full] init empty;\n"
	if debug == True:
		s += "\tvar_error : bool init false;"

	s += "\n"

	for p in range(0,threadCount) :
		s += "\n"
		for value in values :
			s += "\t[var_set_to_" + value + "_#] (var_state =someoneIsModified   & var_who =me_bit_#)          -> tick         : true;\n"
			s += "\t[var_set_to_" + value + "_#] (var_state =someoneDoesAtomicOp & var_who =me_bit_#)          -> tick         : true;\n"
			s += "\t[var_set_to_" + value + "_#] (var_state =someoneIsModified   & var_who!=me_bit_#)          -> write        : (var_who'=me_bit_#);\n"
			s += "\t[var_set_to_" + value + "_#] (var_state =someAreShared)                                    -> write        : (var_state'=someoneIsModified) & (var_who'=me_bit_#);\n"

		s += "\n"

		s += "\t[var_read_#] var_state=someoneIsModified   & var_who =me_bit_#                 -> tick         : true;\n"
		s += "\t[var_read_#] var_state=someoneDoesAtomicOp & var_who =me_bit_#                 -> tick         : true;\n"
		s += "\t[var_read_#] var_state=someoneIsModified   & var_who!=me_bit_#                 -> read         : (var_state'=someAreShared) & (var_who'=min(full,max(var_who+me_bit_#, empty)));\n"
		s += "\t[var_read_#] var_state=someAreShared       & mod(floor(var_who/me_bit_#),2)=1  -> tick         : true;\n"
		s += "\t[var_read_#] var_state=someAreShared       & mod(floor(var_who/me_bit_#),2)=0  -> read         : (var_who'=min(full,max(var_who+me_bit_#, empty)));\n"

		s += "\n"

		s += "\t[var_atomic_begin_#] (var_state =someoneIsModified   & var_who =me_bit_#)      -> tick         : (var_state'=someoneDoesAtomicOp);\n"
		s += "\t[var_atomic_begin_#] (var_state =someoneIsModified   & var_who!=me_bit_#)      -> atomic_begin : (var_state'=someoneDoesAtomicOp) & (var_who'=me_bit_#);\n"
		s += "\t[var_atomic_begin_#] (var_state =someAreShared)                                -> atomic_begin : (var_state'=someoneDoesAtomicOp) & (var_who'=me_bit_#);\n"
		s += "\t[var_atomic_end_#]   (var_state =someoneDoesAtomicOp & var_who =me_bit_#)      -> tick         : (var_state'=someoneIsModified);\n"

		if debug == True :
			s += "\t[var_atomic_begin_#] (var_state =someoneDoesAtomicOp & var_who =me_bit_#)      ->                (var_error'=true);\n"
			s += "\t[var_atomic_end_#]   (var_state =someoneDoesAtomicOp & var_who!=me_bit_#)      ->                (var_error'=true);\n"
			s += "\t[var_atomic_end_#]   (var_state!=someoneDoesAtomicOp)                          ->                (var_error'=true);\n"

		s = s.replace('#', str(p))

	s += "endmodule\n"
	s += "\n"

	# labels
	for p in range(0, threadCount) :
		s += "label \"var_invalid_#\"   = ((var_state=someoneIsModified   | var_state=someAreShared) & mod(floor(var_who/me_bit_#),2)=0);\n"
		s += "label \"var_modified_#\"  =  (var_state=someoneIsModified   & var_who=me_bit_#);\n"
		s += "label \"var_atomic_op_#\" =  (var_state=someoneDoesAtomicOp & var_who=me_bit_#);\n"
		s += "label \"var_shared_#\"    =  (var_state=someAreShared       & mod(floor(var_who/me_bit_#),2)=1);\n"
		s = s.replace('#', str(p))

	s = s.replace("var_", name + "_")

	# correctness props
	t = ""

	t += "P<=0 [F (var_state=someoneIsModified   &  " + " & ".join(["var_who!=0"] + [ "var_who!=me_bit_%d" % i for i in range(0, threadCount) ]) + ")]; // one or zero threads can be in modified state at a time\n"

	t += "P<=0 [F (var_state=someoneDoesAtomicOp &               " + " & ".join([ "var_who!=me_bit_%d" % i for i in range(0, threadCount) ]) + ")]; // one and only one thread can be in atomic op state at a time\n"

	t += "\n"
	t += "P<=0 [F (var_state=someAreShared       & (" + " | ".join(["var_who =0"] + [ "var_who =me_bit_%d" % i for i in range(0, threadCount)]) + "))]; // if a cache copy is shared, at least one other is too\n"

	if debug == True :
		t += "\n"
		t += "P<=0 [F (var_error=true)]; // if a cache copy is shared, at least one other is too\n"

	t = t.replace("var_", name + "_")

	return s, t

# works around the problem that global variables cannot be assigned a value in a synchronized transition
# by making it a local variable with transitions for assigning values
def generatePseudoGlobalVariable(name, typee, init, values, threadCount) :

	s = ""

	s += "module " + name + "_variable\n"
	s += "\t" + name + " : " + typee + " init " + init + ";\n"

	for p in range(0, threadCount) :
		for value in values :
			s += "\t[" + name + "_set_to_" + value + "_#] true -> (" + name + "'=" + value + ");\n"
		s = s.replace('#', str(p))

	s += "endmodule\n"

	return s

def generateSharedMemoryRewards() :
	s = ""
	#s += "rewards \"time\"\n"
	#s += "\ttrue : 1;\n"
	#s += "endrewards\n"
	return s

# ### correctness props ### ###################################################
def generateCorrectnessProperties(threadCount) :

	t = ""

	#t += "const double error=1.0E-6;\n"
	#t += "\n"

	return t

# ### quantitative props ### ##################################################
def generateQuantitativeProperties(threadCount) :

	s = ""

	#loc = "l_between_2"

	#s += "// how long does it take for one thread to get behind the first barrier\n"
	#q = ""
	#for p in range(0, threadCount) :
	#	q += "l_" + str(p) + ">=" + loc + "|"
	#s += "P=? [F<=time (" + q + "false)]\n"
	#s += "\n"
	#s += "// excpected number of ticks\n"
	#s += "base_rate * R{\"time\"}=? [F (" + q + "false)]\n"
	#s += "\n"

	#s += "// how long does it take for all thread to get behind the first barrier\n"
	#q = ""
	#for p in range(0, threadCount) :
	#	q += "l_" + str(p) + ">=" + loc + "&"
	#s += "P=? [F<=time (" + q + "true)]\n"
	#s += "\n"
	#s += "//excpected number of ticks\n"
	#s += "base_rate * R{\"time\"}=? [F (" + q + "true)]\n"
	#s += "\n"

	#s += "const double time=ticks/base_rate;\n"
	#s += "const double ticks;\n"

	return s

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
			work_ticks = int(sys.argv[i+1])
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

