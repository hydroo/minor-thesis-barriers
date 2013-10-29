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
	call("prism %s %s -exportresults %s -prop %d -maxiters 1000000 -cuddmaxmem 4194304" % (modelFileName(filePrefix), quantitativePropertiesFileName(filePrefix), "model-check.tmp", propertyNr), debug)
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
	works = [100, 1000]

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

	# operation counting queries
	Al    = 19
	Ale   = 20
	Ar    = 21
	Are   = 22
	Bl    = 23
	Ble   = 24
	Br    = 25
	Bre   = 26
	Cl    = 27
	Cle   = 28
	Cr    = 29
	Cre   = 30
	Dl    = 31
	Dle   = 32
	Dr    = 33
	Dre   = 34

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

	#print("# remote transfers")
	#print("# n succeeded failed")
	#print("# n Xs        Xf")
	#for n in threadCounts :
	#	call("./gen.py -n %d --work %d %s" % (n, work, filePrefix))
	#	xse = float(modelCheck(filePrefix, Xse, debug))
	#	xfe = float(modelCheck(filePrefix, Xfe, debug))
	#	print("  %d %4.3f   %4.3f" % (n, xse, xfe))

	#print("")

	basePower = 11
	ghz = 2.5
	baseMicroJoulePerCycle = basePower / ghz / 1000.0

	microJoulePerLocalOperation = 0.002    # choosen through measuring and modelling work=10 cycles and looking at the numbers
	microJoulePerRemoteOperation = 0.2     # super shitty estimate

	# energy
	for work in works :
		print("# work=%d" % work)
		print("# number of operations")
		#print("# n       Al      Ar|      Bl      Br|      Cl      Cr|      Dl      Dr")
		#print("# micro Joule per phase accumulated")
		#print("# n      A      B      C      D")
		#print("# Watt per phase")
		#print("# n      A      B      C      D overall")
		for n in threadCounts :
			off = 4*math.ceil(math.log(n, 2))

			call("./gen.py -n %d --work %d %s" % (n, work, filePrefix))

			ace = float(modelCheck(filePrefix, Ace, debug))
			bce = float(modelCheck(filePrefix, Bce, debug))
			cce = float(modelCheck(filePrefix, Cce, debug))
			dce = float(modelCheck(filePrefix, Dce, debug))

			ale = float(modelCheck(filePrefix, Ale, debug))
			ble = float(modelCheck(filePrefix, Ble, debug))
			cle = float(modelCheck(filePrefix, Cle, debug))
			dle = float(modelCheck(filePrefix, Dle, debug))

			are = float(modelCheck(filePrefix, Are, debug))
			bre = float(modelCheck(filePrefix, Bre, debug))
			cre = float(modelCheck(filePrefix, Cre, debug))
			dre = float(modelCheck(filePrefix, Dre, debug))

			aj = ale*microJoulePerLocalOperation + are*microJoulePerRemoteOperation + ace*baseMicroJoulePerCycle
			bj = ble*microJoulePerLocalOperation + bre*microJoulePerRemoteOperation + bce*baseMicroJoulePerCycle
			cj = cle*microJoulePerLocalOperation + cre*microJoulePerRemoteOperation + cce*baseMicroJoulePerCycle
			dj = dle*microJoulePerLocalOperation + dre*microJoulePerRemoteOperation + dce*baseMicroJoulePerCycle

			aw       = ( aj     * 1000.0) / ((ace)     / ghz)
			bw       = ((bj-aj) * 1000.0) / ((bce-ace) / ghz)
			cw       = ((cj-bj) * 1000.0) / ((cce-bce) / ghz)
			dw       = ((dj-cj) * 1000.0) / ((dce-cce) / ghz)
			overallw = ( dj     * 1000.0) / ( dce      / ghz)

			#print(" ", n, "%8.2f %7.2f %8.2f %7.2f %8.2f %7.2f %8.2f %7.2f" % (ale, are, ble-ale, bre-are, cle-ble, cre-bre, dle-cle, dre-cre))
			#print(" ", n, "%6.2f %6.2f %6.2f %6.2f" % (aj, bj-aj, cj-bj, dj-cj))
			print(" ", n, "%6.2f %6.2f %6.2f %6.2f %8.2f" % (aw, bw, cw, dw, overallw))

	finalize(debug)
