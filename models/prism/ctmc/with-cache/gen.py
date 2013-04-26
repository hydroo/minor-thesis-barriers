#! /usr/bin/env python3

import sys

def generateModel(processCount, workTicks, readTicks, writeTicks) :

	s = ""

	s += generateModelType()
	s += "\n"

	s += generateGlobalConstants(processCount)
	s += "\n"

	s += generateGlobalVariables()
	s += "\n"

	s += generateCache(processCount)
	s += "\n"

	for p in range(1, processCount+1) :
		s += generateProcess(p, processCount, workTicks > 0)
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

	return s

def generateGlobalVariables() :
	return ""

def generateProcess(p, processCount, useWorkPeriod) :

	s = ""

	s += "module process_#\n"

	empty = str(0)
	full = str((2**processCount)-1)
	possibleValues = [str(i) for i in range(int(empty), int(full)+1)]

	s += "\tl_# : [0..11] init 0;\n"
	s += "\tcp_# : [empty..full] init empty;\n"
	s += "\tleft__# : bool init false;\n"
	s += "\tentry_# : [empty..full] init empty;\n"
	s += "\texit__# : [empty..full] init empty;\n"
	s += "\n"

	others = "".join([ str(i) for i in everyProcessButMyself(p, processCount)])

	s += "\t[read_#] l_#=0 -> (l_#'=1) & (cp_#'=entry_#);\n"
	s += "\n"

	s += "\t[] l_#=1 & mod(floor(cp_#/me_bit_#),2)=1 -> tick : (l_#'=2);\n"
	for value in possibleValues:
		s += "\t[set_entry_to_" + value + "_at_" + others + "] l_#=1 & mod(floor(cp_#/me_bit_#),2)=0 & cp_#=" + value + "-me_bit_# -> (l_#'=2) & (entry_#'=" + value + ") & (cp_#'=" + value + ");\n"
	s += "\n"

	s += "\t[read_#] l_#=2 & (  cp_# != full & left__# = false ) -> (l_#'=0);\n"
	s += "\t[read_#] l_#=2 & (!(cp_# != full & left__# = false)) -> (l_#'=3);\n"
	s += "\n"

	s += "\t[set_left__to_true_at_" + others + "] l_#=3 -> (l_#'=4) & (left__#'=true);\n"

	if useWorkPeriod :
		s += "\t[set_exit__to_0_at_" + others + "]    l_#=4 -> (l_#'=5) & (exit__#'=empty);\n"
		s += "\n"
		s += "\n"
		s += "\t[] l_#=5 -> work : (l_#'=6);\n"
	else :
		s += "\t[set_exit__to_0_at_" + others + "]    l_#=4 -> (l_#'=6) & (exit__#'=empty);\n"
		s += "\n"
		s += "\n"
		s += "\t// work period\n"

	s += "\n"
	s += "\n"

	s += "\t[read_#] l_#=6 -> (l_#'=7) & (cp_#'=exit__#);\n"

	s += "\n"

	s += "\t[] l_#=7 & mod(floor(cp_#/me_bit_#),2)=1 -> tick : (l_#'=8);\n"
	for value in possibleValues:
		s += "\t[set_exit__to_" + value + "_at_" + others + "] l_#=7 & mod(floor(cp_#/me_bit_#),2)=0 & cp_#=" + value + "-me_bit_# -> (l_#'=8) & (exit__#'=" + value + ") & (cp_#'=" + value + ");\n"
	s += "\n"

	s += "\t[read_#] l_#=8 & (  cp_# != full & left__# = true ) -> (l_#'=6);\n"
	s += "\t[read_#] l_#=8 & (!(cp_# != full & left__# = true)) -> (l_#'=9);\n"
	s += "\n"

	s += "\t[set_left__to_false_at_" + others + "] l_#=9   -> (l_#'=10) & (left__#'=false);\n"

	if useWorkPeriod :
		s += "\t[set_entry_to_0_at_" + others + "]     l_#=10  -> (l_#'=11) & (entry_#'=empty);\n"
		s += "\n"
		s += "\n"
		s += "\t[] l_#=11 -> work : (l_#'=0);\n"
	else :
		s += "\t[set_entry_to_0_at_" + others + "]     l_#=10  -> (l_#'=0) & (entry_#'=empty);\n"
		s += "\n"
		s += "\n"
		s += "\t// work period\n"

	s += "\n"
	s += "\n"

	s += generateSyncTransitionsForLocalVariables(p, processCount, "entry_", possibleValues)
	s += generateSyncTransitionsForLocalVariables(p, processCount, "exit__", possibleValues)
	s += generateSyncTransitionsForLocalVariables(p, processCount, "left__", ["false", "true"])

	s += "endmodule\n"

	return s.replace('#', str(p))

def generateSyncTransitionsForLocalVariables(p, processCount, prefix, l) :
	s = ""
	for value in l :
		for forWhom in forMe(p, processCount) :
			s += "\t[set_" + prefix + "to_" + value + "_at_" + forWhom + "] true -> (" + prefix + "#'=" + value + ");\n"
	return s

def generateRewards() :
	s = ""
	s += "rewards \"time\"\n"
	s += "\ttrue : 1;\n"
	s += "endrewards\n"
	return s

def generateLabels(processCount) :
	return ""

# ### cache ### ###############################################################

def generateCache(processCount) :
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
		bit = 2**(p-1)
		others = "".join([ str(i) for i in everyProcessButMyself (p, processCount)])
		for variable in ["entry", "exit_"] :
			for value in possibleValues :
				s += "\t[set_" + variable + "_to_" + value + "_at_" + others + "]  (state_c=someoneIsModified & who_c=me_bit_#) -> tick : true;\n"
				s += "\t[set_" + variable + "_to_" + value + "_at_" + others + "] !(state_c=someoneIsModified & who_c=me_bit_#) -> write : (state_c'=someoneIsModified) & (who_c'=me_bit_#);\n"

		for value in ["false", "true"] :
			s += "\t[set_left__to_" + value + "_at_" + others + "]  (state_c=someoneIsModified & who_c=me_bit_#) -> tick : true;\n"
			s += "\t[set_left__to_" + value + "_at_" + others + "] !(state_c=someoneIsModified & who_c=me_bit_#) -> write : (state_c'=someoneIsModified) & (who_c'=me_bit_#);\n"

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
		bit = 2**(p-1)
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

	s += "// synchronized local variables have the same values\n"
	for variable in ["entry_", "exit__", "left__"] :
		for i in range(1, processCount) :
			s += "P<=0 [F " + variable + str(i) + "  != " + variable + str(i+1) + "]\n"
	s += "\n"


	s += "// deadlock-freedom\n"
	for i in range(1, processCount+1) :
		s += "P>=1 [G F l_" + str(i) +"=3]\n"
	s += "\n"

	s += "// consistency of the barrier\n"
	for p in range(1, processCount+1) :
		s += "P<=0 [F (l_" + str(p) + "=3 & ("
		for q in everyProcessButMyself(p, processCount) :
			s += "l_" + str(q) + "=9|"
		s += "false))]\n"
	s += "\n"

	s += "// ### cache properties ###\n"
	s += "\n"

	s += "// one and only one process can be in modified state at a time\n"
	s += "P<=0 [F (state_c=someoneIsModified & !("
	for p in range(1, processCount+1) :
		bit = 2**(p-1)
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
		else:
			filePrefix = sys.argv[i]
			modelFileName = filePrefix + ".pm"
			correctnessPropertiesFileName = filePrefix + "-correctness.props"
		i += 1

	if len(filePrefix) == 0 :
		print(helpMessage)
		exit(0)

	assert processCount >= 2
	assert workTicks    >= 0
	assert readTicks    >= 1
	assert writeTicks   >= 1

	modelString = generateModel(processCount, workTicks, readTicks, writeTicks)

	correctnessPropertiesString = generateCorrectnessProperties(processCount)

	f = open(modelFileName, 'w')
	f.write(modelString)
	f.close()

	f = open(correctnessPropertiesFileName, 'w')
	f.write(correctnessPropertiesString)
	f.close()

