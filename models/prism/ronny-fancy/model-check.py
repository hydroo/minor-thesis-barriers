#! /usr/bin/env python3

import os
import subprocess
import sys

def modelFileName(filePrefix) :
	return filePrefix + ".pm"

def quantitativePropertiesFileName(filePrefix) :
	return filePrefix + "-quantitative.props"

def correctnessPropertiesFileName(filePrefix) :
	return filePrefix + "-correctness.props"

def call(command, debug=False) :
	p = subprocess.Popen(command, shell=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
	if debug == True :
		print(p.stdout.readlines())
	p.wait()

def readResults() :
	f = open("model-check.tmp", 'r')
	s = f.readlines()
	f.close()
	return s

def modelCheck(filePrefix, propertyNr, debug=False) :
	call("prism %s %s -exportresults %s -prop %d -maxiters 1000000" % (modelFileName(filePrefix), quantitativePropertiesFileName(filePrefix), "model-check.tmp", propertyNr), debug)
	s = readResults()
	return s[1].replace('\n', '')

def finalize(debug=False) :
	if debug==False :
		os.unlink("model-check.tmp")
		os.unlink("model-check.pm")
		os.unlink("model-check-correctness.props")
		os.unlink("model-check-quantitative.props")

# ############################################################################

if __name__ == "__main__":

	debug=False
	
	filePrefix = "model-check"
	threadCounts = [3, 2]
	work = 100

	A   =  1
	Ae  =  2
	B   =  3
	Be  =  4
	C   =  5
	Ce  =  6
	D   =  7
	De  =  8

	Ac  =  9
	Ace = 10
	Bc  = 11
	Bce = 12
	Cc  = 13
	Cce = 14
	Dc  = 15
	Dce = 16

	Xse = 17
	Xfe = 18

	#print("#   last-in-until-last out   last-in-until-first-out")
	#print("# n De-Be                    Ce-Be")
	#for n in threadCounts :
	#	call("./gen.py -n %d --work %d %s" % (n, work, filePrefix))
	#	be = float(modelCheck(filePrefix, Be, debug))
	#	ce = float(modelCheck(filePrefix, Ce, debug))
	#	de = float(modelCheck(filePrefix, De, debug))
	#	print(n, "%4.3f %4.3f" % (de - be, ce - be))

	#print("")

	#print("# cumulative (stacked diagram)")
	#print("# n all-work   one-works   one-done   all-done")
	#print("# n Ac         Bc          Cc         Dc")
	#for n in threadCounts :
	#	call("./gen.py -n %d --work %d %s" % (n, work, filePrefix))
	#	ace = float(modelCheck(filePrefix, Ace, debug))
	#	bce = float(modelCheck(filePrefix, Bce, debug))
	#	cce = float(modelCheck(filePrefix, Cce, debug))
	#	dce = float(modelCheck(filePrefix, Dce, debug))
	#	print(n, "%4.3f   %4.3f   %4.3f   %4.3f" % (ace, bce-ace, cce-bce, dce-cce))

	#print("")

	print("# remote transfers")
	print("# n succeeded failed")
	print("# n Xs        Xf")
	for n in threadCounts :
		call("./gen.py -n %d --work %d %s" % (n, work, filePrefix))
		xse = float(modelCheck(filePrefix, Xse, debug))
		xfe = float(modelCheck(filePrefix, Xfe, debug))
		print("  %d %4.3f   %4.3f" % (n, xse, xfe))

	finalize(debug)
