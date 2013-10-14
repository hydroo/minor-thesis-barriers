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
	call("prism %s %s -exportresults %s -prop %d" % (modelFileName(filePrefix), quantitativePropertiesFileName(filePrefix), "model-check.tmp", propertyNr), debug)
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
	threadCounts = [2, 3, 4]
	work = 100

	A   =  1
	Ae  =  2
	B   =  3
	Be  =  4
	C   =  5
	Ce  =  6
	D   =  7
	De  =  8

	DBe =  9
	DCe = 10

	Ap  = 11
	Ape = 12
	Dp  = 13
	Dpe = 14
	Ep  = 15
	Epe = 16
	Fp  = 17
	Fpe = 18

	Ac  = 19
	Ace = 20
	Bc  = 21
	Bce = 22
	Cc  = 23
	Cce = 24
	Dc  = 25
	Dce = 26
	Ec  = 27
	Ece = 28

	print("# last in until last out")
	print("# n De-Be")
	for n in threadCounts :
		call("./gen.py -n %d --work %d %s" % (n, work, filePrefix))
		be = float(modelCheck(filePrefix, Be, debug))
		ce = float(modelCheck(filePrefix, Ce, debug))
		de = float(modelCheck(filePrefix, De, debug))
		print(n, "%4.3f %4.3f" % (ce - be, de - be))
		
	print("")

	#print("# first out until last out")
	#print("# n De-Ce")
	#for n in threadCounts :
	#	call("./gen.py -n %d --work %d %s" % (n, work, filePrefix))
	#	ce = float(modelCheck(filePrefix, Ce, debug))
	#	de = float(modelCheck(filePrefix, De, debug))
	#	print(n, "%.3f" % (de - ce))

	#print("# percentage writing vs reading")
	#print("# n Epe Fpe")
	#for n in threadCounts :
	#	call("./gen.py -n %d --work %d %s" % (n, work, filePrefix))
	#	epe = float(modelCheck(filePrefix, Epe, debug))
	#	fpe = float(modelCheck(filePrefix, Fpe, debug))
	#	sum_ = epe + fpe
	#	print(n, "%4.3f %4.3f" % (epe / sum_, fpe / sum_))

	#print("# cumulative (stacked diagram)")
	#print("# n all-work one-works writing reading one-done all-done")
	#print("# n Ac       Bc        Ec      Fc      Cc       Dc")
	#for n in threadCounts :
	#	call("./gen.py -n %d --work %d %s" % (n, work, filePrefix))
	#	ace = float(modelCheck(filePrefix, Ace, debug))
	#	bce = float(modelCheck(filePrefix, Bce, debug))
	#	ece = float(modelCheck(filePrefix, Ece, debug))
	#	cce = float(modelCheck(filePrefix, Cce, debug))
	#	dce = float(modelCheck(filePrefix, Dce, debug))
	#	print(n, "%4.3f %4.3f %4.3f %4.3f %4.3f %4.3f" % (ace, bce-ace, ece-bce, 0 , dce-ece, 0))

	finalize(debug)
