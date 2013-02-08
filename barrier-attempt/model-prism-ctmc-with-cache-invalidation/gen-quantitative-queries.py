#! /usr/bin/env python3

# work only up until 9 processes!!!!

import sys

helpMessage = \
"""
 gen-quantitative-queries.py [OPTIONS] [outfile]

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

	f = sys.stdout
	if queryFileName != "":
		f = open(queryFileName, 'w')


	loc = 5
	if oneLoop == True :
		loc = 4

	f.write("// how long does it take for one process to get behind the first barrier\n")
	f.write("P=? [F<=time (")
	for i in range(1, processCount+1) :
		f.write("l_" + str(i) + ">=" + str(loc) + "|")
	f.write("false)]\n")

	f.write("\n")

	f.write("//excpected number of ticks\n")
	f.write("base_rate * R{\"time\"}=? [F (")
	for i in range(1, processCount+1) :
		f.write("l_" + str(i) + ">=" + str(loc) + "|" )
	f.write("false)]\n")

	f.write("\n")

	f.write("// how long does it take for all processes to get behind the first barrier\n")
	f.write("P=? [F<=time (")
	for i in range(1, processCount+1) :
		f.write("l_" + str(i) + ">=" + str(loc) + "&" )
	f.write("true)]\n")

	f.write("\n")

	f.write("//excpected number of ticks\n")
	f.write("base_rate * R{\"time\"}=? [F (")
	for i in range(1, processCount+1) :
		f.write("l_" + str(i) + ">=" + str(loc) + "&" )
	f.write("true)]\n")

	f.write("\n")

	f.write("// how longshared does it take from one process being behind the entry barrier to all processes being behind it\n")
	f.write("clrP=? [F<=time (")
	for i in range(1, processCount+1) :
		f.write("l_" + str(i) + ">=" + str(loc) + "&" )
	f.write("true), (")
	for i in range(1, processCount+1) :
		for j in range(1, processCount+1) :
			if i == j :
				comp = "="
			else :
				comp = "<"
			f.write("l_" + str(j) + comp + str(loc) + "&")
		f.write("true)|(")
	f.write("false)]\n")

	f.write("\n")

	f.write("//expected number of ticks\n")
	f.write("base_rate * clraR{\"time\"}=? [F (")
	for i in range(1, processCount+1) :
		f.write("l_" + str(i) + ">=" + str(loc) + "&" )
	f.write("true), (")
	for i in range(1, processCount+1) :
		for j in range(1, processCount+1) :
			if i == j :
				comp = "="
			else :
				comp = "<"
			f.write("l_" + str(j) + comp + str(loc) + "&")
		f.write("true)|(")
	f.write("false)]\n")

	f.write("\n")

	f.write("// in which state is the cache and how much of the time?\n")
	f.write("S=? [\"modified_1\"]\n")
	f.write("S=? [\"shared_1\"]\n")
	f.write("S=? [\"invalid_1\"]\n")

	f.write("\n");
	f.write("\n");

	f.write("const double time=ticks/base_rate;\n")
	f.write("const double ticks;\n")

