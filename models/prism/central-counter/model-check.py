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
	threadCounts = [4, 3, 2]
	works = [10, 100, 1000]

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
	Ec  = 17
	Ece = 18

	Al  = 19
	Ale = 20
	As  = 21
	Ase = 22
	Bl  = 23
	Ble = 24
	Bs  = 25
	Bse = 26
	Cl  = 27
	Cle = 28
	Cs  = 29
	Cse = 30
	Dl  = 31
	Dle = 32
	Ds  = 33
	Dse = 34
	El  = 35
	Ele = 36
	Es  = 37
	Ese = 38

	#print("#   last-in-until-last out   last-in-until-first-out")
	#print("# n De-Be                    Ce-Be")
	#for n in threadCounts :
	#	call("./gen.py -n %d --work %d %s" % (n, work, filePrefix))
	#	be = float(modelCheck(filePrefix, Be, debug))
	#	ce = float(modelCheck(filePrefix, Ce, debug))
	#	de = float(modelCheck(filePrefix, De, debug))
	#	print(n, "%4.3f %4.3f" % (de - be, ce - be))
	#
	#print("")

	#print("# percentage writing vs reading")
	#print("# n Epe Fpe")
	#for n in threadCounts :
	#	call("./gen.py -n %d --work %d %s" % (n, work, filePrefix))
	#	epe = float(modelCheck(filePrefix, Epe, debug))
	#	fpe = float(modelCheck(filePrefix, Fpe, debug))
	#	sum_ = epe + fpe
	#	print(n, "%4.3f %4.3f" % (epe / sum_, fpe / sum_))

	#print("")

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

	#print("")

	basePower = 11
	perThreadPowerCc = 4
	perThreadPowerRs = 6
	ghz = 2.5

	baseNanoJoulePerCycle = basePower / ghz

	nanoJoulePerLocalOperation = 2    # choosen through measuring and modelling work=10 cycles and looking at the numbers
	nanoJoulePerSharedOperation = 200 # super shitty estimate

	for work in works :

		print("# work=%d" % work)
		#print("# operations (absolute values)")
		#print("# n     Al     As|    Bl     Bs|    El     Es|    Cl     Cs|    Dl     Ds      Cc-nJ Rs-nJ base-nJ")
		#print("#                                                                              w/o Base-nJ     ")
		print("# energy (absolute values in micro Joule)")
		print("# n      A      B      E      C      D")
		for n in threadCounts :
			call("./gen.py -n %d --work %d %s" % (n, work, filePrefix))
			ale = float(modelCheck(filePrefix, Ale, debug))
			ble = float(modelCheck(filePrefix, Ble, debug))
			ele = float(modelCheck(filePrefix, Ele, debug))
			cle = float(modelCheck(filePrefix, Cle, debug))
			dle = float(modelCheck(filePrefix, Dle, debug))

			ase = float(modelCheck(filePrefix, Ase, debug))
			bse = float(modelCheck(filePrefix, Bse, debug))
			ese = float(modelCheck(filePrefix, Ese, debug))
			cse = float(modelCheck(filePrefix, Cse, debug))
			dse = float(modelCheck(filePrefix, Dse, debug))

			ace = float(modelCheck(filePrefix, Ace, debug))
			bce = float(modelCheck(filePrefix, Bce, debug))
			ece = float(modelCheck(filePrefix, Ece, debug))
			cce = float(modelCheck(filePrefix, Cce, debug))
			dce = float(modelCheck(filePrefix, Dce, debug))

			#nanoJoulePerCycleCc = (perThreadPowerCc*n) / ghz
			#nanoJoulePerCycleRs = (perThreadPowerRs*n) / ghz
			#djBase = dce * baseNanoJoulePerCycle
			#djReferenceCc = dce * (nanoJoulePerCycleCc)
			#djReferenceRs = dce * (nanoJoulePerCycleRs)

			#print(" ", n, "%6.1f %6.1f|%6.1f %6.1f|%6.1f %6.1f|%6.1f %6.1f|%6.1f %6.1f      %5.0f %5.0f %7.0f" % (ale, ase, ble, bse, ele, ese, cle, cse , dle, dse, djReferenceCc, djReferenceRs, djBase))


			aj = ale*nanoJoulePerLocalOperation + ase*nanoJoulePerSharedOperation + ace*baseNanoJoulePerCycle
			bj = ble*nanoJoulePerLocalOperation + bse*nanoJoulePerSharedOperation + bce*baseNanoJoulePerCycle
			ej = ele*nanoJoulePerLocalOperation + ese*nanoJoulePerSharedOperation + ece*baseNanoJoulePerCycle
			cj = cle*nanoJoulePerLocalOperation + cse*nanoJoulePerSharedOperation + cce*baseNanoJoulePerCycle
			dj = dle*nanoJoulePerLocalOperation + dse*nanoJoulePerSharedOperation + dce*baseNanoJoulePerCycle

			#print(" ", n, "%6.0f %6.0f %6.0f %6.0f %6.0f" % (aj, bj-aj, ej-bj, cj-ej , dj-cj))
			print(" ", n, "%6.3f %6.3f %6.3f %6.3f %6.3f" % (aj / 1000.0, (bj-aj) / 1000.0, (ej-bj) / 1000.0, (cj-ej) / 1000.0 , (dj-cj) / 1000.0))

	finalize(debug)
