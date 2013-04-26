#! /usr/bin/env python3

import sys

def generateModel(processCount, workTicks, readTicks, writeTicks, oneLoop) :

	s = ""

	s += generateModelType()
	s += "\n"

	s += generateGlobalConstants(processCount)
	s += "\n"

	s += generatePseudoGlobalVariables(processCount, oneLoop)
	s += "\n"

	s += generateCache(processCount, oneLoop)
	s += "\n"

	for p in range(1, processCount+1) :
		s += generateProcess(p, processCount, workTicks > 0, oneLoop)
		s += "\n"
	s += "\n"

	s += generateRewards()
	s += "\n"

	s += generateLabels(processCount)
	s += "\n"

	return s

def generateModelType() :
	return "ctmc\n"

def generateGlobalConstants(processCount) :

	s = ""

	for i in range(1, processCount+1) :
		s += "const int me_" + str(i) + " = " + str(i) + ";\n"
	s += "\n"

	for i in range(1, processCount+1) :
		s += "const int me_bit_" + str(i) + " = " + str(1<<(i-1)) + ";\n"
	s += "\n"

	s += "const int empty = 0;\n"
	s += "const int full  = "
	for i in range(1, processCount+1) :
		s += "me_bit_" + str(i) + " + "
	s += "0;\n"
	s += "\n"

	s += "const int work_ticks  = " + str(workTicks) + ";\n"
	s += "const int read_ticks  = " + str(readTicks) + ";\n"
	s += "const int write_ticks = " + str(writeTicks) + ";\n"

	s += "\n"

	s += "const double base_rate = 1000.0;\n"
	s += "const double tick      = base_rate / 1.0;\n"
	s += "const double work      = tick / work_ticks;\n"
	s += "const double read      = tick / read_ticks;\n"
	s += "const double write     = tick / write_ticks;\n"

	s += "\n"
	s += "const int l_init       = 0;\n"

	s += "const int l_entry_0    = 1;\n"
	s += "const int l_entry_1    = 2;\n"
	s += "const int l_entry_2    = 3;\n"

	s += "const int l_between_0  = 4;\n"
	s += "const int l_between_1  = 5;\n"
	s += "const int l_between_2  = 6;\n"

	s += "const int l_exit_0     = 7;\n"
	s += "const int l_exit_1     = 8;\n"
	s += "const int l_exit_2     = 9;\n"
	s += "const int l_after_0    = 10;\n"
	s += "const int l_after_1    = 11;\n"
	s += "const int l_after_2    = l_init;\n"

	return s

def generatePseudoGlobalVariables(processCount, oneLoop) :

	s = ""

	empty = str(0)
	full = str((2**processCount)-1)

	if oneLoop :
		s += generatePseudoGlobalVariable("left", "bool",  "false", ["true"], processCount, oneLoop)
	else :
		s += generatePseudoGlobalVariable("left", "bool",  "false", ["false", "true"], processCount, oneLoop)
	s += "\n"
	if not oneLoop :
		s += generatePseudoGlobalVariable("exit", "[empty..full]",  "empty", [str(i) for i in range(int(empty), int(full)+1)], processCount, oneLoop)
		s += "\n"
	s += generatePseudoGlobalVariable("entry", "[empty..full]", "empty", [str(i) for i in range(int(empty), int(full)+1)], processCount, oneLoop)
	s += "\n"
	s += "\n"

	return s

def generatePseudoGlobalVariable(name, typee, init, values, processCount, oneLoop) :

	s = ""

	s += "module " + name + "_g\n"
	s += "\t" + name + " : " + typee + " init " + init + ";\n"

	for p in range(1, processCount+1) :
		for value in values :
			s += "\t[set_" + name + "_to_" + value + "_#] true -> (" + name + "'=" + value + ");\n"
		s = s.replace('#', str(p))

	if name == "left" and oneLoop:
		s += "\t[set_left_to_false_and_sync_all] true -> (" + name + "'=" + value + ");\n"

	s += "endmodule\n"

	return s

def generateProcess(p, processCount, useWorkPeriod, oneLoop) :

	s = ""

	s += "module process_#\n"

	empty = str(0)
	full = str((2**processCount)-1)
	possibleValues = [str(i) for i in range(int(empty), int(full)+1)]

	if useWorkPeriod :
		s += "\tl_# : [l_init..l_after_1] init l_init;\n"
	else :
		s += "\tl_# : [l_init..l_after_1] init l_entry_0;\n"
	s += "\tcp_# : [empty..full] init empty;\n"
	s += "\n"

	if useWorkPeriod :
		s += "\t[] l_#=l_init -> work : (l_#'=l_entry_0);\n"
	else :
		s += "\t// work period\n"

	s += "\n"

	s += "\t[read_#] l_#=l_entry_0 -> (l_#'=l_entry_1) & (cp_#'=entry);\n"
	s += "\n"

	s += "\t[] l_#=l_entry_1 & mod(floor(cp_#/me_bit_#),2)=1 -> tick : (l_#'=l_entry_2);\n"
	for value in possibleValues:
		s += "\t[set_entry_to_" + value + "_#] l_#=l_entry_1 & mod(floor(cp_#/me_bit_#),2)=0 & cp_#=" + value + "-me_bit_# -> (l_#'=l_entry_2) & (cp_#'=" + value + ");\n"
	s += "\n"

	s += "\t[read_#] l_#=l_entry_2 & (  cp_# != full & left = false ) -> (l_#'=l_entry_0);\n"
	s += "\t[read_#] l_#=l_entry_2 & (!(cp_# != full & left = false)) -> (l_#'=l_between_0);\n"
	s += "\n"

	s += "\t[set_left_to_true_#] l_#=l_between_0 -> (l_#'=l_between_1);\n"

	if oneLoop :
		s += "\t// syncs all processes\n"
		if useWorkPeriod :
			s += "\t[set_left_to_false_and_sync_all] l_#=l_between_1 -> (l_#'=l_init);\n"
		else :
			s += "\t[set_left_to_false_and_sync_all] l_#=l_between_1 -> (l_#'=l_entry_0);\n"

		s += "\t[read_#] l_#=l_between_1 & !("
		for q in everyProcessButMyself(p, processCount) :
			s += "l_" + str(q) + "=l_between_1&"
		s += "true) -> (l_#'=l_between_1);\n"

	if not oneLoop :

		if useWorkPeriod :
			s += "\t[set_exit_to_0_#]    l_#=l_between_1 -> (l_#'=l_between_2);\n"
			s += "\n"
			s += "\n"
			s += "\t[] l_#=l_between_2 -> work : (l_#'=l_exit_0);\n"
		else :
			s += "\t[set_exit_to_0_#]    l_#=l_between_1 -> (l_#'=l_exit_0);\n"
			s += "\n"
			s += "\n"
			s += "\t// work period\n"

		s += "\n"
		s += "\n"

		s += "\t[read_#] l_#=l_exit_0 -> (l_#'=l_exit_1) & (cp_#'=exit);\n"

		s += "\n"

		s += "\t[] l_#=l_exit_1 & mod(floor(cp_#/me_bit_#),2)=1 -> tick : (l_#'=l_exit_2);\n"
		for value in possibleValues:
			s += "\t[set_exit_to_" + value + "_#] l_#=l_exit_1 & mod(floor(cp_#/me_bit_#),2)=0 & cp_#=" + value + "-me_bit_# -> (l_#'=l_exit_2) & (cp_#'=" + value + ");\n"
		s += "\n"

		s += "\t[read_#] l_#=l_exit_2 & (  cp_# != full & left = true ) -> (l_#'=l_exit_0);\n"
		s += "\t[read_#] l_#=l_exit_2 & (!(cp_# != full & left = true)) -> (l_#'=l_after_0);\n"
		s += "\n"

		s += "\t[set_left_to_false_#] l_#=l_after_0  -> (l_#'=l_after_1);\n"

		if useWorkPeriod :
			s += "\t[set_entry_to_0_#]     l_#=l_after_1  -> (l_#'=l_init);\n"
		else :
			s += "\t[set_entry_to_0_#]     l_#=l_after_1  -> (l_#'=l_entry_0);\n"

	s += "endmodule\n"

	return s.replace('#', str(p))

def generateRewards() :
	s = ""
	s += "rewards \"time\"\n"
	s += "\ttrue : 1;\n"
	s += "endrewards\n"
	return s

def generateLabels(processCount) :
	return ""

# ### cache ### ###############################################################

def generateCache(processCount, oneLoop) :
	s = ""

	empty = str(0)
	full = str((2**processCount)-1)
	possibleValues = [str(i) for i in range(int(empty), int(full)+1)]

	s += "const int someoneIsModified = 0;\n"
	s += "const int someoneIsShared   = 1;\n"
	s += "\n"


	s += "module cache\n"

	s += "\t// we exclude the case that all are invalid and say the default is that the cache line copy on process 1 is modified\n"
	s += "\tstate_c : [someoneIsModified..someoneIsShared] init someoneIsModified;\n"
	s += "\twho_c   : [empty..full] init me_bit_1;\n"
	s += "\n"

	for p in range(1,processCount+1) :

		if oneLoop :
			variables = ["entry"]
			leftValues = ["true"]
		else :
			variables = ["entry", "exit"]
			leftValues = ["false", "true"]

		for variable in variables :
			for value in possibleValues :
				s += "\t[set_" + variable + "_to_" + value + "_#]  (state_c=someoneIsModified & who_c=me_bit_#) -> tick : true;\n"
				s += "\t[set_" + variable + "_to_" + value + "_#] !(state_c=someoneIsModified & who_c=me_bit_#) -> write : (state_c'=someoneIsModified) & (who_c'=me_bit_#);\n"

		for value in leftValues :
			s += "\t[set_left_to_" + value + "_#]  (state_c=someoneIsModified & who_c=me_bit_#) -> tick : true;\n"
			s += "\t[set_left_to_" + value + "_#] !(state_c=someoneIsModified & who_c=me_bit_#) -> write : (state_c'=someoneIsModified) & (who_c'=me_bit_#);\n"

			s += "\t[read_#] state_c=someoneIsModified & who_c=me_bit_# -> tick : true;\n"
			s += "\t[read_#] state_c=someoneIsModified & who_c!=me_bit_# -> read : (state_c'=someoneIsShared) & (who_c'=min(full,max(who_c+me_bit_#, empty)));\n"
			s += "\t[read_#] state_c=someoneIsShared & mod(floor(who_c/me_bit_#),2)=1 -> tick : true;\n"
			s += "\t[read_#] state_c=someoneIsShared & mod(floor(who_c/me_bit_#),2)=0 -> read : (who_c'=min(full,max(who_c+me_bit_#, empty)));\n"
			s += "\n"
		s = s.replace('#', str(p))

	s += "endmodule\n"
	s += "\n"

	s += generateCacheLabels()

	return s

def generateCacheLabels() :
	s = ""

	for p in range(1, processCount+1) :
		s += "label \"invalid_#\"  = ((state_c=someoneIsModified | state_c=someoneIsShared) & mod(floor(who_c/me_bit_#),2)=0);\n"
		s += "label \"modified_#\" = (state_c=someoneIsModified & who_c=me_bit_#);\n"
		s += "label \"shared_#\"   = (state_c=someoneIsShared   & mod(floor(who_c/me_bit_#),2)=1);\n"
		s = s.replace('#', str(p))

	return s

# ### correctness props ### ###################################################
def generateCorrectnessProperties(processCount) :

	s = ""

	s += "const double error=1.0E-6;\n"
	s += "\n"

	s += "// deadlock-freedom\n"
	for i in range(1, processCount+1) :
		s += "P>=1 [G F l_" + str(i) +"=l_between_0]\n"
	s += "\n"

	s += "// consistency of the barrier\n"
	for p in range(1, processCount+1) :
		s += "P<=0 [F (l_" + str(p) + "=l_between_0 & ("
		for q in everyProcessButMyself(p, processCount) :
			s += "l_" + str(q) + "=l_after_0|"
		s += "false))]\n"
	s += "\n"

	s += "// ### cache properties ###\n"
	s += "\n"

	s += "// one and only one process can be in modified state at a time\n"
	s += "P<=0 [F (state_c=someoneIsModified & !("
	for p in range(1, processCount+1) :
		s += "who_c=me_bit_" + str(p) + "|"
	s += "false))];\n"
	s += "\n"

	s += "// if one cacheline is shared, at least one other is too\n"
	for p in range(1, processCount+1) :
		s += "P<=0 [F (\"shared_" + str(p) + "\" & !("
		for q in everyProcessButMyself(p, processCount) :
			s += "\"shared_" + str(q) + "\"|"
		s += "false))]\n"
	s += "\n"

	s += "// every cache state can be reached\n"
	for p in range(1, processCount+1) :
		s += "P>=1 [F (\"modified_" + str(p) + "\")]\n"
		s += "P>=1 [F (\"shared_" + str(p) + "\")]\n"
		s += "P>=1 [F (\"invalid_" + str(p) + "\")]\n"
	s += "\n"

	s += "// steady state probs for cache states are equal for all processes\n"
	for state in ["modified_", "shared_"]:
		#invalid_ is implicitely correct if the others are
		for p in range(1, processCount) :
				s += "((S=? [\""+ state + str(p) + "\"] - S=? [\"" + state + str(p+1) + "\"]) <= error) | (error*-1 <= (S=? [\"" + state + str(p) + "\"] - S=? [\"" + state + str(p+1) + "\"]))\n"
	s += "\n"

	return s

# ### helper ### ##############################################################
def everyProcessButMyself (p, processCount) :
	l = []
	for j in range(1, processCount+1):
		if p != j:
			l += [j]
	return l

def forMe(p, processCount) :
	#me and all but one other
	l = []
	for fromWhom in range(1, processCount+1) :
		if fromWhom != p :
			s = ""
			for forWhom in range(1, processCount+1) :
				if forWhom != fromWhom :
					s += str(forWhom)
			l += [s]
	return l

# #############################################################################
helpMessage = \
"""
 gen.py [OPTIONS] [outfile-prefix]

  -h, --help          print help message
  -n <nr>             set process count
  --work  <ticks>     set tick count for a work period [default 1]
  --read  <ticks>     set tick count for a cache read  [default 50]
  --write <ticks>     set tick count a cache write     [default 100]
"""

if __name__ == "__main__":

	processCount = 0
	filePrefix = modelFileName = correctnessPropertiesFileName = ""

	workTicks  = 1
	readTicks  = 50
	writeTicks = 100
	oneLoop = False

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
		elif sys.argv[i] == "--one-loop":
			oneLoop = True
		elif sys.argv[i].startswith("--") :
			print ("unknown parameter: " + sys.argv[i])
			exit(-1)
		elif filePrefix == "":
			filePrefix = sys.argv[i]
			modelFileName = filePrefix + ".pm"
			correctnessPropertiesFileName = filePrefix + "-correctness.props"
		else :
			print ("unknown parameter: " + sys.argv[i])
			exit(-1)
		i += 1

	if len(filePrefix) == 0 :
		print(helpMessage)
		exit(0)

	assert processCount >= 2
	assert workTicks    >= 0
	assert readTicks    >= 1
	assert writeTicks   >= 1

	modelString = generateModel(processCount, workTicks, readTicks, writeTicks, oneLoop)

	correctnessPropertiesString = generateCorrectnessProperties(processCount)

	f = open(modelFileName, 'w')
	f.write(modelString)
	f.close()

	f = open(correctnessPropertiesFileName, 'w')
	f.write(correctnessPropertiesString)
	f.close()

