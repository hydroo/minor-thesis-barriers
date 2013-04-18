#! /usr/bin/env python3

# work only up until 9 processes!!!!

import sys

helpMessage = \
"""
 gen-correctness-queries.py [OPTIONS] [outfile]

  -h, --help        print help message
  -p <nr>           set process count

  --oneloop         omit the second loop
"""

if __name__ == "__main__":

	processCount = 0
	queryFileName = ""

	oneLoop = False

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
		elif sys.argv[i] == "--write":
			writeTicks = int(sys.argv[i+1])
			i += 1
		elif sys.argv[i] == "--oneloop":
			oneLoop = True
		else:
			queryFileName = sys.argv[i]
		i += 1

	assert processCount >= 2

	def allBut (i) :
		group = []
		for j in range(1, processCount+1):
			if i != j:
				group += [j]
		return group

	f = sys.stdout
	if queryFileName != "":
		f = open(queryFileName, 'w')


	f.write("const double error=1.0E-6;\n")

	f.write("\n")

	f.write("// cache properties\n")
	for i in range(1, processCount+1) :
		f.write("P<=0 [G (\"modified_" + str(i) + "\" & \"modified_" + str((i % processCount) + 1) + "\")]\n")

	f.write("\n")

	for i in range(1, processCount+1) :
		f.write("P<=0 [G (\"shared_" + str(i) + "\" & !(")
		for j in allBut(i) :
			f.write("\"shared_" + str(j) + "\"|")
		f.write("false))]\n")
	
	f.write("\n")
	
	for i in range(1, processCount+1) :
		f.write("P>=1  [F (\"modified_" + str(i) + "\")]\n")
		f.write("P>=1  [F (\"shared_" + str(i) + "\")]\n")
		f.write("P>=1  [F (\"invalid_" + str(i) + "\")]\n")

	f.write("\n")
	
	for what in ["modified_", "shared_"]:
		#invalid_ is implicitely correct if the others are
		for i in range(1, processCount) :
				f.write("((S=? [ \""+ what + str(i) + "\" ] - S=? [ \"" + what + str(i+1) + "\" ]) <= error) | (error*-1 <= (S=? [ \"" + what + str(i) + "\" ] - S=? [ \"" + what + str(i+1) + "\" ]))\n")
		f.write("\n")
	

	for what in ["left_", "entry_"]:
		for i in range(1, processCount) :
			f.write("P<=0 [F " + what + str(i) + "  != " + what + str(i+1) + "]\n")
		f.write("\n")

	if oneLoop == False:
		what = "exit_"
		for i in range(1, processCount) :
			f.write("P<=0 [F " + what + str(i) + "  != " + what + str(i+1) + "]\n")
		f.write("\n")

	if oneLoop == False :
		f.write("//non-blocking\n")
		for i in range(1, processCount+1) :
			f.write("P>=1 [G F l_" + str(i) +"=11]\n")
