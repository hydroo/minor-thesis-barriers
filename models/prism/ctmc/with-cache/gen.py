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
		s += generateProcess(p, processCount)
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

	s += "const double base_rate = 2500.0;\n"
	s += "const double tick      = base_rate / 1.0;\n"
	s += "const double work      = tick / work_ticks;\n"
	s += "const double read      = tick / read_ticks;\n"
	s += "const double write     = tick / write_ticks;\n"

	return s

def generateGlobalVariables() :
	return ""

def generateProcess(p, processCount) :

	s = ""

	s += "module process_" + str(p) + "\n"

	me_bit = 2**(p-1)
	empty = str(0)
	full = str((2**processCount)-1)
	possibleValues = [str(i) for i in range(int(empty), int(full)+1)]

	s += generateLocalVariable("l_", "[0..11]", "0")
	s += generateLocalVariable("cp_", "[" + empty + ".." + full + "]", empty)
	s += generateLocalVariable("exit_", "[" + empty + ".."+ full + "]", empty)
	s += generateLocalVariable("entry_", "[" + empty + ".."+ full + "]", empty)
	s += generateLocalVariable("left_", "bool", "false");
	s += "\n"

	others = everyProcessButMyself(p, processCount, "")

	s += "\t[read_#] l_#=0 -> (l_#'=1) & (cp_#'=entry_#);\n"
	s += "\n"

	s += "\t[] l_#=1 & mod(floor(cp_#/me_bit_#),2)=1 -> (l_#'=2);\n"
	for value in possibleValues:
		s += "\t[set_entry_to_" + value + "_at_" + others + "] l_#=1 & mod(floor(cp_#/me_bit_#),2)=0 & cp_#=" + value + "-me_bit_# -> (l_#'=2) & (entry_#'=" + value + ") & (cp_#'=" + value + ");\n"
	s += "\n"

	s += "\t[read_#] l_#=2 & (  cp_# != full & left_# = false ) -> (l_#'=0);\n"
	s += "\t[read_#] l_#=2 & (!(cp_# != full & left_# = false)) -> (l_#'=3);\n"
	s += "\n"

	s += "\t[set_exit_to_0_at_" + others + "]    l_#=3 -> (l_#'=4) & (exit_#'=empty);\n"
	s += "\t[set_left_to_true_at_" + others + "] l_#=4 -> (l_#'=5) & (left_#'=true);\n"

	s += "\n"
	s += "\n"

	s += "\t[] l_#=5 -> work : (l_#'=6);\n"

	s += "\n"
	s += "\n"

	s += "\t[read_#] l_#=6 -> (l_#'=7) & (cp_#'=exit_#);\n"
	s += "\n"

	s += "\t[] l_#=7 & mod(floor(cp_#/me_bit_#),2)=1 -> (l_#'=8);\n"
	for value in possibleValues:
		s += "\t[set_exit_to_" + value + "_at_" + others + "] l_#=7 & mod(floor(cp_#/me_bit_#),2)=0 & cp_#=" + value + "-me_bit_# -> (l_#'=8) & (exit_#'=" + value + ") & (cp_#'=" + value + ");\n"
	s += "\n"

	s += "\t[read_#] l_#=8 & (  cp_# != full & left_# = true ) -> (l_#'=6);\n"
	s += "\t[read_#] l_#=8 & (!(cp_# != full & left_# = true)) -> (l_#'=9);\n"
	s += "\n"

	s += "\t[set_entry_to_0_at_" + others + "]    l_#=9  -> (l_#'=10) & (entry_#'=empty);\n"
	s += "\t[set_left_to_false_at_" + others + "] l_#=10 -> (l_#'=11) & (left_#'=false);\n"

	s += "\n"
	s += "\n"

	s += "\t[] l_#=11 -> work : (l_#'=0);\n"

	s += "\n"
	s += "\n"
	s += generateSyncTransitionsForLocalVariables(p, processCount, "entry_", possibleValues)
	s += generateSyncTransitionsForLocalVariables(p, processCount, "exit_", possibleValues)
	s += generateSyncTransitionsForLocalVariables(p, processCount, "left_", ["false", "true"])

	s += "endmodule\n"

	return s.replace('#', str(p))

def generateLocalVariable(prefix, dataType, init) :
	return "\t" + prefix + "#" + " : " + dataType + " init " + init + ";\n"

def generateSyncTransitionsForLocalVariables(p, processCount, prefix, l) :
	s = ""
	for value in l :
		for forWhom in forMe(p, processCount) :
			s += "\t[set_" + prefix + "to_" + value + "_at_" + forWhom + "] true -> (" + prefix + "#'="+value + ");\n"
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

	s += "const int allAreInvalid     = 0;\n"
	s += "const int someoneIsModified = 1;\n"
	s += "const int someoneIsShared   = 2;\n"
	s += "\n"


	s += "module cache\n"

	s += "\tstate : [allAreInvalid..someoneIsShared] init allAreInvalid;\n"
	s += "\twho   : [empty..full] init empty;\n"
	s += "\n"

	for p in range(1,processCount+1) :
		me_bit = 2**(p-1)
		others = everyProcessButMyself (p, processCount, '')
		for variable in ["entry", "exit"] :
			for value in possibleValues :
				s += "\t[set_" + variable + "_to_" + value + "_at_" + others + "]  (state=someoneIsModified & who=" + str(me_bit) + ") -> tick : true;\n"
				s += "\t[set_" + variable + "_to_" + value + "_at_" + others + "] !(state=someoneIsModified & who=" + str(me_bit) + ") -> write : (state'=someoneIsModified) & (who'=" + str(me_bit) + ");\n"

		for value in ["false", "true"] :
			s += "\t[set_left_to_" + value + "_at_" + others + "]  (state=someoneIsModified & who= " + str(me_bit) + ") -> tick : true;\n"
			s += "\t[set_left_to_" + value + "_at_" + others + "] !(state=someoneIsModified & who= " + str(me_bit) + ") -> write : (state'=someoneIsModified) & (who'=" + str(me_bit) + ");\n"

		s += "\t[read_" + str(p) + "] state=allAreInvalid -> read : (state'=someoneIsShared) & (who'=" + str(me_bit) + ");\n"
		s += "\t[read_" + str(p) + "] state=someoneIsModified & who=" + str(me_bit) + " -> tick : true;\n"
		s += "\t[read_" + str(p) + "] state=someoneIsModified & who!=" + str(me_bit) + " -> read : (state'=someoneIsShared) & (who'=min(full,max(who+" + str(me_bit) + ", empty)));\n"
		s += "\t[read_" + str(p) + "] state=someoneIsShared & mod(floor(who/" + str(me_bit) + "),2)=1 -> tick : true;\n"
		s += "\t[read_" + str(p) + "] state=someoneIsShared & mod(floor(who/" + str(me_bit) + "),2)=0 -> read : (who'=min(full,max(who+" + str(me_bit)+ ", empty)));\n"

		s += "\n"

	# todo

	s += "endmodule\n"

	s += generateCacheLabels()

	return s

def generateCacheLabels() :
	return ""

# ### helper ### ##############################################################
def everyProcessButMyself (p, processCount, delimiter) :
	s = ""
	for j in range(1, processCount+1):
		if p != j:
			s += str(j)
			if j < processCount :
				s += delimiter
	return s

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

  -h, --help                    print help message
  -p <nr>, --processes <nr>     set process count
  --work      <ticks>           set tick count for a work period [default 1]
  --read      <ticks>           set tick count for a cache read  [default 50]
  --write     <ticks>           set tick count a cache write     [default 100]
"""

if __name__ == "__main__":

	processCount = 0
	modelFileName = ""

	workTicks  = 1
	readTicks  = 50
	writeTicks = 100

	if len(sys.argv) < 2 :
		print(helpMessage)
		exit(0)

	i = 1
	while i < len(sys.argv):
		if sys.argv[i] == "-h" or sys.argv[i] == "--help":
			print (helpMessage)
			exit(0)
		elif sys.argv[i] == "-p" or sys.argv[i] == "--processes":
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
			modelFileName = sys.argv[i]
		i += 1

	assert processCount >= 2
	assert workTicks    >= 1
	assert readTicks    >= 1
	assert writeTicks   >= 1

	modelString = generateModel(processCount, workTicks, readTicks, writeTicks)

	f = sys.stdout
	if modelFileName != "":
		f = open(modelFileName, 'w')

	f.write(modelString)

