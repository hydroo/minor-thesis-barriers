#! /usr/bin/env python3

import math
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
	call("prism %s %s -exportresults %s -prop %d -maxiters 100000 -gaussseidel -sparse -cuddmaxmem 4194304 -gsmax 10240 -sbmax 10240" % (modelFileName(filePrefix), quantitativePropertiesFileName(filePrefix), "model-check.tmp", propertyNr), debug)
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
	#threadCounts = [8, 7, 6, 5, 4, 3, 2]
	threadCounts = [4, 3, 2]
	work = 1

	# sascha queries
	A     =  1
	Ae    =  2
	B     =  3
	Be    =  4
	C     =  5
	Ce    =  6
	D     =  7
	De    =  8

	#cumulative
	Ac    =  9
	Ace   = 10
	Bc    = 11
	Bce   = 12

	# round queries

	Roc   = 13
	Roce  = 14
	Rac   = 15
	Race  = 16

	Cc    = 13
	Cce   = 14
	Dc    = 15
	Dce   = 16

	#print("#   last-in-until-last out   last-in-until-first-out")
	#print("# n De-Be                    Ce-Be")
	#for n in threadCounts :
	#	call("./gen.py -n %d --work %d %s" % (n, work, filePrefix))
	#	ae = float(modelCheck(filePrefix, Ae, debug))
	#	be = float(modelCheck(filePrefix, Be, debug))
	#	ce = float(modelCheck(filePrefix, Ce, debug))
	#	de = float(modelCheck(filePrefix, De, debug))
	#	#print(n, "%4.3f %4.3f" % (de - be, ce - be))
	#	print(n, "%4.3f %4.3f %4.3f %4.3f" % (ae, be, ce, de))

	#print("")

	print("# cumulative one (stacked diagram)")
	print("# n all-work   one-works   one-done   all-done")
	print("# n Ac         Bc          Cc         Dc")
	for n in threadCounts :
		off = 4*math.ceil(math.log(n, 2))
		lastRound = math.ceil(math.log(n, 2)) - 1
		call("./gen.py -n %d --work %d %s" % (n, work, filePrefix))
		ace = float(modelCheck(filePrefix, Ace       , debug))
		bce = float(modelCheck(filePrefix, Bce       , debug))
		cce = float(modelCheck(filePrefix, Cce + off, debug))
		dce = float(modelCheck(filePrefix, Dce + off, debug))
		
		print(n, "%4.3f   %4.3f   %4.3f   %4.3f" % (ace, bce - ace, cce - bce, dce - cce))

	#print("")

	#print("# cumulative one (stacked diagram)")
	#print("# n all-work   [rounds-all]+   all-done")
	#print("# n Ac         [Race]+         Dc")
	#for n in threadCounts :
	#	off = 4*math.ceil(math.log(n, 2))
	#	lastRound = math.ceil(math.log(n, 2)) - 1

	#	call("./gen.py -n %d --work %d %s" % (n, work, filePrefix))

	#	ace = float(modelCheck(filePrefix, Ace, debug))
	#	bce = float(modelCheck(filePrefix, Bce, debug))

	#	ro = []
	#	ra = []
	#	for r in range(0, math.ceil(math.log(n, 2))) :
	#		ro.append(float(modelCheck(filePrefix, Roce + 4*r, debug)))
	#		ra.append(float(modelCheck(filePrefix, Race + 4*r, debug)))

	#	cce = float(modelCheck(filePrefix, Cce + off, debug))
	#	dce = float(modelCheck(filePrefix, Dce + off, debug))
	#	
	#	print(n, "%4.3f   " % ace, end="")
	#	for r in range(0, math.ceil(math.log(n, 2))) :
	#		if r == 0:
	#			print("%4.3f   " % (ra[r] - ace), end="")
	#		else :
	#			print("%4.3f   " % (ra[r] - ra[r-1]), end="")
	#	print("%4.3f" % (dce - ra[lastRound]))

	finalize(debug)
