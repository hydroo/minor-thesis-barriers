#! /usr/bin/env python3

#import os
import sys

helpMessage = \
"""
 gen-model.py [OPTIONS] [outfile]

  -h, --help        print help message
  -p <nr>           set process count
  --work <ticks>    set tick count for a work period
  --read <ticks>    set tick count for a cache read
  --write <ticks>   set tick count a cache write
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
		elif sys.argv[i] == "-p":
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

	f = sys.stdout
	if modelFileName != "":
		f = open(modelFileName, 'w')


	f.write("ctmc\n")
	f.write("\n")

	for i in range(1, processCount+1) :
		f.write("const int me_" + str(i) + " = " + str(i) + ";\n")
	
	f.write("\n")

	for i in range(1, processCount+1) :
		f.write("const int me_bit_" + str(i) + " = " + str(1<<(i-1)) + "; // 2**" + str(i-1) + "\n")

	f.write("\n")
	f.write("const int empty = 0;\n")
	f.write("const int full  = ")
	for i in range(1, processCount+1) :
		f.write("me_bit_" + str(i) + " + ")
	f.write("0;\n")

	f.write("\n")

	f.write("const int modified = 0;\n")
	f.write("const int shared   = 1;\n");
	f.write("const int invalid  = 2;\n");

	f.write("\n")

	f.write("const int work_ticks  = " + str(workTicks) + ";\n")
	f.write("const int read_ticks  = " + str(readTicks) + ";\n")
	f.write("const int write_ticks = " + str(writeTicks) + ";\n")

	f.write("\n")

	f.write("const double base_rate = 2500.0;\n")
	f.write("const double tick      = base_rate / 1.0;\n")
	f.write("const double work      = tick / work_ticks;\n")
	f.write("const double read      = tick / read_ticks;\n")
	f.write("const double write     = tick / write_ticks;\n")

	f.write("\n")

	# ### actual process module ### #

	f.write("module process_1\n")
	f.write("	l_1 : [0..11] init 0;\n")
	f.write("	cp_1 : [empty..full] init empty;\n")
	f.write("	mesi_1 : [0..2] init invalid;\n")
	f.write("	exit_1 : [empty..full] init empty;\n")
	f.write("	entry_1 : [empty..full] init empty;\n")
	f.write("	left_1 : bool init false;\n")

	f.write("\n")

	f.write("	//process")

	f.write("\n")

	f.write("	[read_1]  l_1=0 & mesi_1 =invalid -> read : (l_1'=1) & (cp_1'=entry_1) & (mesi_1'=shared);\n")
	f.write("	[read_1]  l_1=0 & mesi_1!=invalid -> tick : (l_1'=1) & (cp_1'=entry_1);\n")

	f.write("	[]        l_1=1 & mod(floor(cp_1/me_bit_1),2)=1 -> tick : (l_1'=2);\n")


	full = (2**processCount) - 1
	otherProcesses = ""
	for i in range(2, processCount+1):
		otherProcesses += str(i)

	for value in range(1, full+1):
		f.write("	[set_entry_" + str(value) + "_" + otherProcesses + "] l_1=1 & mesi_1!=modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=" + str(value) + "-me_bit_1 -> write : (l_1'=2) & (entry_1'=" + str(value) + ") & (mesi_1'=modified);\n")
		f.write("	[set_entry_" + str(value) + "_" + otherProcesses + "] l_1=1 & mesi_1 =modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=" + str(value) + "-me_bit_1 -> tick  : (l_1'=2) & (entry_1'=" + str(value) + ");\n")

	f.write("\n")

	f.write("	[read_1]  l_1=2 & mesi_1 =invalid & (  cp_1 != full & left_1 = false ) -> read : (l_1'=0) & (mesi_1'=shared);\n")
	f.write("	[read_1]  l_1=2 & mesi_1!=invalid & (  cp_1 != full & left_1 = false ) -> tick : (l_1'=0);\n")
	f.write("	[read_1]  l_1=2 & mesi_1 =invalid & (!(cp_1 != full & left_1 = false)) -> read : (l_1'=3) & (mesi_1'=shared);\n")
	f.write("	[read_1]  l_1=2 & mesi_1!=invalid & (!(cp_1 != full & left_1 = false)) -> tick : (l_1'=3);\n")

	f.write("\n")

	f.write("	[set_exit_0_" + otherProcesses + "]    l_1=3 & mesi_1!=modified -> write : (l_1'=4) & (exit_1'=empty) & (mesi_1'=modified);\n")
	f.write("	[set_exit_0_" + otherProcesses + "]    l_1=3 & mesi_1 =modified -> tick  : (l_1'=4) & (exit_1'=empty);\n")
	f.write("	[set_left_true_" + otherProcesses + "] l_1=4 & mesi_1!=modified -> write : (left_1'=true) & (l_1'=5)  & (mesi_1'=modified);\n")
	f.write("	[set_left_true_" + otherProcesses + "] l_1=4 & mesi_1 =modified -> tick  : (left_1'=true) & (l_1'=5);\n")

	f.write("\n")
	f.write("\n")

	f.write("	[]        l_1=5 -> work : (l_1'=6);\n")

	f.write("\n")
	f.write("\n")


	f.write("	[read_1]  l_1=6 & mesi_1 =invalid -> read : (l_1'=7) & (cp_1'=exit_1) & (mesi_1'=shared);\n")
	f.write("	[read_1]  l_1=6 & mesi_1!=invalid -> tick : (l_1'=7) & (cp_1'=exit_1);\n")
	f.write("	[]        l_1=7 & mod(floor(cp_1/me_bit_1),2)=1 -> tick : (l_1'=8);\n")

	f.write("\n")

	for value in range(1, full+1):
		f.write("	[set_exit_" + str(value) + "_23] l_1=7 & mesi_1!=modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=" + str(value) + "-me_bit_1 -> write : (l_1'=8) & (exit_1'=" + str(value) + ") & (mesi_1'=modified);\n")
		f.write("	[set_exit_" + str(value) + "_23] l_1=7 & mesi_1 =modified & mod(floor(cp_1/me_bit_1),2)=0 & cp_1=" + str(value) + "-me_bit_1 -> tick  : (l_1'=8) & (exit_1'=" + str(value) + ");\n")

	f.write("\n")

	f.write("	[read_1]  l_1=8 & mesi_1 =invalid & (  cp_1 != full & left_1 = true ) -> read : (l_1'=6) & (mesi_1'=shared);\n")
	f.write("	[read_1]  l_1=8 & mesi_1!=invalid & (  cp_1 != full & left_1 = true ) -> tick : (l_1'=6);\n")
	f.write("	[read_1]  l_1=8 & mesi_1 =invalid & (!(cp_1 != full & left_1 = true)) -> read : (l_1'=9) & (mesi_1'=shared);\n")
	f.write("	[read_1]  l_1=8 & mesi_1!=invalid & (!(cp_1 != full & left_1 = true)) -> tick : (l_1'=9);\n")

	f.write("\n")

	f.write("	[set_entry_0_23]    l_1=9  & mesi_1!=modified -> write : (l_1'=10) & (entry_1'=empty) & (mesi_1'=modified);\n")
	f.write("	[set_entry_0_23]    l_1=9  & mesi_1 =modified -> tick  : (l_1'=10) & (entry_1'=empty);\n")
	f.write("	[set_left_false_23] l_1=10 & mesi_1!=modified -> write : (l_1'=11) & (left_1'=false)  & (mesi_1'=modified);\n")
	f.write("	[set_left_false_23] l_1=10 & mesi_1 =modified -> tick  : (l_1'=11) & (left_1'=false);\n")

	f.write("\n")
	f.write("\n")

	f.write("	[]        l_1=11 -> work : (l_1'=0);\n")

	f.write("	//cacheline\n")

#	[read_2]  mesi_1=invalid  -> (mesi_1'=invalid);
#	[read_3]  mesi_1=invalid  -> (mesi_1'=invalid);
#
#	[read_2]  mesi_1=shared   -> (mesi_1'=shared);
#	[read_3]  mesi_1=shared   -> (mesi_1'=shared);
#
#	[read_2]  mesi_1=modified -> (mesi_1'=shared);
#	[read_3]  mesi_1=modified -> (mesi_1'=shared);
#
#	[set_left_false_12]  true -> (left_1'=false)  & (mesi_1'=invalid);
#	[set_left_false_13]  true -> (left_1'=false)  & (mesi_1'=invalid);
#	[set_left_true_12]   true -> (left_1'=true)   & (mesi_1'=invalid);
#	[set_left_true_13]   true -> (left_1'=true)   & (mesi_1'=invalid);
#
#	[set_entry_0_12]     true -> (entry_1'=empty) & (mesi_1'=invalid);
#	[set_entry_0_13]     true -> (entry_1'=empty) & (mesi_1'=invalid);
#	[set_entry_1_12]     true -> (entry_1'=1)     & (mesi_1'=invalid);
#	[set_entry_1_13]     true -> (entry_1'=1)     & (mesi_1'=invalid);
#	[set_entry_2_12]     true -> (entry_1'=2)     & (mesi_1'=invalid);
#	[set_entry_2_13]     true -> (entry_1'=2)     & (mesi_1'=invalid);
#	[set_entry_3_12]     true -> (entry_1'=3)     & (mesi_1'=invalid);
#	[set_entry_3_13]     true -> (entry_1'=3)     & (mesi_1'=invalid);
#	[set_entry_4_12]     true -> (entry_1'=4)     & (mesi_1'=invalid);
#	[set_entry_4_13]     true -> (entry_1'=4)     & (mesi_1'=invalid);
#	[set_entry_5_12]     true -> (entry_1'=5)     & (mesi_1'=invalid);
#	[set_entry_5_13]     true -> (entry_1'=5)     & (mesi_1'=invalid);
#	[set_entry_6_12]     true -> (entry_1'=6)     & (mesi_1'=invalid);
#	[set_entry_6_13]     true -> (entry_1'=6)     & (mesi_1'=invalid);
#	[set_entry_7_12]     true -> (entry_1'=full)  & (mesi_1'=invalid);
#	[set_entry_7_13]     true -> (entry_1'=full)  & (mesi_1'=invalid);
#
#	[set_exit_0_12]      true -> (exit_1'=empty)  & (mesi_1'=invalid);
#	[set_exit_0_13]      true -> (exit_1'=empty)  & (mesi_1'=invalid);
#	[set_exit_1_12]      true -> (exit_1'=1)      & (mesi_1'=invalid);
#	[set_exit_1_13]      true -> (exit_1'=1)      & (mesi_1'=invalid);
#	[set_exit_2_12]      true -> (exit_1'=2)      & (mesi_1'=invalid);
#	[set_exit_2_13]      true -> (exit_1'=2)      & (mesi_1'=invalid);
#	[set_exit_3_12]      true -> (exit_1'=3)      & (mesi_1'=invalid);
#	[set_exit_3_13]      true -> (exit_1'=3)      & (mesi_1'=invalid);
#	[set_exit_4_12]      true -> (exit_1'=4)      & (mesi_1'=invalid);
#	[set_exit_4_13]      true -> (exit_1'=4)      & (mesi_1'=invalid);
#	[set_exit_5_12]      true -> (exit_1'=5)      & (mesi_1'=invalid);
#	[set_exit_5_13]      true -> (exit_1'=5)      & (mesi_1'=invalid);
#	[set_exit_6_12]      true -> (exit_1'=6)      & (mesi_1'=invalid);
#	[set_exit_6_13]      true -> (exit_1'=6)      & (mesi_1'=invalid);
#	[set_exit_7_12]      true -> (exit_1'=full)   & (mesi_1'=invalid);
#	[set_exit_7_13]      true -> (exit_1'=full)   & (mesi_1'=invalid);

	f.write("endmodule\n")

	# ### duplicating ### #


	# ### appendix ### #

	f.write("\n")

	f.write("rewards \"time\"\n")
	f.write("	true : 1;\n")
	f.write("endrewards\n")

	f.write("\n")

	for i in range(1, processCount+1) :
		f.write("label \"modified_" + str(i) + "\" = mesi_" + str(i) + "=modified;\n")
		f.write("label \"shared_" + str(i) + "\"   = mesi_" + str(i) + "=shared;\n")
		f.write("label \"invalid_" + str(i) + "\"  = mesi_" + str(i) + "=invalid;\n")
		f.write("\n")



	
