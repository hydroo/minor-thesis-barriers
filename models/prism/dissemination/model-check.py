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
	threadCounts = [8, 7, 6, 5, 4, 3, 2]
	works = [100, 1000]

	# sascha queries
	A     =  1
	Ae    =  2
	B     =  3
	Be    =  4
	C     =  5
	Ce    =  6
	D     =  7
	De    =  8

	# cumulative
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

	# operation counting queries
	Al    = 17
	Ale   = 18
	Ar    = 19
	Are   = 20
	Bl    = 21
	Ble   = 22
	Br    = 23
	Bre   = 24
	Cl    = 25
	Cle   = 26
	Cr    = 27
	Cre   = 28
	Dl    = 29
	Dle   = 30
	Dr    = 31
	Dre   = 32

	Rol   = 33
	Role  = 34
	Ror   = 35
	Rore  = 36
	Ral   = 37
	Rale  = 38
	Rar   = 39
	Rare  = 40

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

	#print("# cumulative one (stacked diagram)")
	#print("# n all-work   one-works   one-done   all-done")
	#print("# n Ac         Bc          Cc         Dc")
	#for n in threadCounts :
	#	off = 4*math.ceil(math.log(n, 2))
	#	lastRound = math.ceil(math.log(n, 2)) - 1
	#	call("./gen.py -n %d --work %d %s" % (n, work, filePrefix))
	#	ace = float(modelCheck(filePrefix, Ace       , debug))
	#	bce = float(modelCheck(filePrefix, Bce       , debug))
	#	cce = float(modelCheck(filePrefix, Cce + off, debug))
	#	dce = float(modelCheck(filePrefix, Dce + off, debug))
	#
	#	print(n, "%4.3f   %4.3f   %4.3f   %4.3f" % (ace, bce - ace, cce - bce, dce - cce))

	#print("")

	#for work in works:
	#	print("# cumulative one (stacked diagram)")
	#	print("# n all-work   one-works   [rounds-all]+   all-done")
	#	print("# n Ac         Bc          [Race]+         Dc")
	#	for n in threadCounts :
	#		off = 4*math.ceil(math.log(n, 2))
	#		lastRound = math.ceil(math.log(n, 2)) - 1

	#		call("./gen.py -n %d --work %d %s" % (n, work, filePrefix))

	#		ace = float(modelCheck(filePrefix, Ace, debug))
	#		bce = float(modelCheck(filePrefix, Bce, debug))

	#		ro = []
	#		ra = []
	#		for r in range(0, math.ceil(math.log(n, 2))) :
	#			ro.append(float(modelCheck(filePrefix, Roce + 4*r, debug)))
	#			ra.append(float(modelCheck(filePrefix, Race + 4*r, debug)))

	#		cce = float(modelCheck(filePrefix, Cce + off, debug))
	#		dce = float(modelCheck(filePrefix, Dce + off, debug))
	#
	#		print(n, "%4.3f    %4.3f  " % (ace, bce-ace), end="")
	#		for r in range(0, math.ceil(math.log(n, 2))) :
	#			if r == 0:
	#				print("%4.3f   " % (ra[r] - bce), end="")
	#			else :
	#				print("%4.3f   " % (ra[r] - ra[r-1]), end="")
	#		print("%4.3f" % (dce - ra[lastRound]))

	#print("")

	basePower = 11
	ghz = 2.5
	baseMicroJoulePerCycle = basePower / ghz / 1000.0

	microJoulePerLocalOperation = 0.002    # choosen through measuring and modelling work=10 cycles and looking at the numbers
	microJoulePerRemoteOperation = 0.2     # super shitty estimate

	## energy without rounds
	#for work in works :
	#	print("# work=%d" % work)
	#	#print("# number of operations")
	#	#print("# n       Al      Ar|      Bl      Br|      Cl      Cr|      Dl      Dr")
	#	#print("# micro Joule per phase accumulated")
	#	#print("# n      A      B      C      D")
	#	print("# Watt per phase")
	#	print("# n      A      B      C      D overall")
	#	for n in threadCounts :
	#		off = 4*math.ceil(math.log(n, 2))
	#
	#		call("./gen.py -n %d --work %d %s" % (n, work, filePrefix))

	#		ace = float(modelCheck(filePrefix, Ace       , debug))
	#		bce = float(modelCheck(filePrefix, Bce       , debug))
	#		cce = float(modelCheck(filePrefix, Cce + off, debug))
	#		dce = float(modelCheck(filePrefix, Dce + off, debug))

	#		ale = float(modelCheck(filePrefix, Ale + off, debug))
	#		ble = float(modelCheck(filePrefix, Ble + off, debug))
	#		cle = float(modelCheck(filePrefix, Cle + off, debug))
	#		dle = float(modelCheck(filePrefix, Dle + off, debug))

	#		are = float(modelCheck(filePrefix, Are + off, debug))
	#		bre = float(modelCheck(filePrefix, Bre + off, debug))
	#		cre = float(modelCheck(filePrefix, Cre + off, debug))
	#		dre = float(modelCheck(filePrefix, Dre + off, debug))

	#		aj = ale*microJoulePerLocalOperation + are*microJoulePerRemoteOperation + ace*baseMicroJoulePerCycle
	#		bj = ble*microJoulePerLocalOperation + bre*microJoulePerRemoteOperation + bce*baseMicroJoulePerCycle
	#		cj = cle*microJoulePerLocalOperation + cre*microJoulePerRemoteOperation + cce*baseMicroJoulePerCycle
	#		dj = dle*microJoulePerLocalOperation + dre*microJoulePerRemoteOperation + dce*baseMicroJoulePerCycle

	#		aw       = ( aj     * 1000.0) / ((ace)     / ghz)
	#		bw       = ((bj-aj) * 1000.0) / ((bce-ace) / ghz)
	#		cw       = ((cj-bj) * 1000.0) / ((cce-bce) / ghz)
	#		dw       = ((dj-cj) * 1000.0) / ((dce-cce) / ghz)
	#		overallw = ( dj     * 1000.0) / ( dce      / ghz)

	#		#print(" ", n, "%8.2f %7.2f %8.2f %7.2f %8.2f %7.2f %8.2f %7.2f" % (ale, are, ble-ale, bre-are, cle-ble, cre-bre, dle-cle, dre-cre))
	#		#print(" ", n, "%6.2f %6.2f %6.2f %6.2f" % (aj, bj-aj, cj-bj, dj-cj))
	#		print(" ", n, "%6.2f %6.2f %6.2f %6.2f %8.2f" % (aw, bw, cw, dw, overallw))

	#print("")

	# energy with rounds

	for work in works :
		#print("# work=%d" % work)
		#print("# number of operations")
		#print("# n       Al      Ar|     Bl      Br|     Rxl     Rxr")
		print("# micro Joule per phase accumulated")
		print("# n      A      B     Rx")
		#print("# Watt per phase")
		#print("# n      A      B     Rx overall")
		for n in threadCounts :
			off = 4*math.ceil(math.log(n, 2))
			lastRound = math.ceil(math.log(n, 2)) - 1

			call("./gen.py -n %d --work %d %s" % (n, work, filePrefix))

			ace = float(modelCheck(filePrefix, Ace       , debug))
			bce = float(modelCheck(filePrefix, Bce       , debug))
			race = []
			for r in range(0, math.ceil(math.log(n, 2))) :
				race.append(float(modelCheck(filePrefix, Race + 4*r, debug)))
			dce = float(modelCheck(filePrefix, Dce + off, debug))

			ale = float(modelCheck(filePrefix, Ale + off, debug))
			ble = float(modelCheck(filePrefix, Ble + off, debug))
			rale = []
			for r in range(0, math.ceil(math.log(n, 2))) :
				rale.append(float(modelCheck(filePrefix, Rale + off + 8*r, debug)))
			dle = float(modelCheck(filePrefix, Dle + off, debug))

			are = float(modelCheck(filePrefix, Are + off, debug))
			bre = float(modelCheck(filePrefix, Bre + off, debug))
			rare = []
			for r in range(0, math.ceil(math.log(n, 2))) :
				rare.append(float(modelCheck(filePrefix, Rare + off + 8*r, debug)))
			dre = float(modelCheck(filePrefix, Dre + off, debug))

			aj = ale*microJoulePerLocalOperation + are*microJoulePerRemoteOperation + ace*baseMicroJoulePerCycle
			bj = ble*microJoulePerLocalOperation + bre*microJoulePerRemoteOperation + bce*baseMicroJoulePerCycle
			raj = []
			for r in range(0, math.ceil(math.log(n, 2))) :
				raj.append(rale[r]*microJoulePerLocalOperation + rare[r]*microJoulePerRemoteOperation + race[r]*baseMicroJoulePerCycle)
			dj = dle*microJoulePerLocalOperation + dre*microJoulePerRemoteOperation + dce*baseMicroJoulePerCycle


			aw       = ( aj     * 1000.0) / ((ace)     / ghz)
			bw       = ((bj-aj) * 1000.0) / ((bce-ace) / ghz)
			raw = []
			for r in range(0, math.ceil(math.log(n, 2))) :
				if r == 0 :
					preaj, preace = bj, bce
				else :
					preaj, preace = raj[r-1], race[r-1]
				raw.append(((raj[r]-preaj) * 1000.0) / ((race[r] - preace) / ghz))
			overallw = ( dj     * 1000.0) / ( dce      / ghz)

			#print(" ", n, "%8.2f %7.2f %8.2f %7.2f " % (ale, are, ble, bre), end="")
			#for r in range(0, math.ceil(math.log(n, 2))) :
			#	if r == 0:
			#		print("%8.2f %7.2f" % (rale[r] - ble, rare[r] - bre), end="")
			#	else :
			#		print("%8.2f %7.2f" % (rale[r] - rale[r-1], rare[r] - rare[r-1]), end="")
			#print()

			print(" ", n, "%6.2f %6.2f " % (aj, bj), end="")
			for r in range(0, math.ceil(math.log(n, 2))) :
				if r == 0:
					print("%6.2f" % (raj[r] - bj), end="")
				else :
					print("%6.2f" % (raj[r] - raj[r-1]), end="")
			print()

			#print(" ", n, "%6.2f %6.2f " % (aw, bw), end="")
			#for r in range(0, math.ceil(math.log(n, 2))) :
			#	print("%6.2f" % (raw[r]), end="")
			#print("%8.2f" % overallw)

	finalize(debug)
