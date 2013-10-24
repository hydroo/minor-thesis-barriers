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

def modelCheck(filePrefix, propertyNr, cycles=None, debug=False) :
	if cycles == None :
		call("prism %s %s -exportresults %s -prop %d -maxiters 1000000 -cuddmaxmem 4194304" % (modelFileName(filePrefix), quantitativePropertiesFileName(filePrefix), "model-check.tmp", propertyNr), debug)
	else :
		call("prism %s %s -exportresults %s -const ticks=%d -prop %d -maxiters 1000000 -cuddmaxmem 4194304" % (modelFileName(filePrefix), quantitativePropertiesFileName(filePrefix), "model-check.tmp", cycles, propertyNr), debug)

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
	#	be = float(modelCheck(filePrefix, Be, None, debug))
	#	ce = float(modelCheck(filePrefix, Ce, None, debug))
	#	de = float(modelCheck(filePrefix, De, None, debug))
	#	print(n, "%4.3f %4.3f" % (de - be, ce - be))
	#
	#print("")

	#print("# percentage writing vs reading")
	#print("# n Epe Fpe")
	#for n in threadCounts :
	#	call("./gen.py -n %d --work %d %s" % (n, work, filePrefix))
	#	epe = float(modelCheck(filePrefix, Epe, None, debug))
	#	fpe = float(modelCheck(filePrefix, Fpe, None, debug))
	#	sum_ = epe + fpe
	#	print(n, "%4.3f %4.3f" % (epe / sum_, fpe / sum_))

	#print("")

	#print("# cumulative (stacked diagram)")
	#print("# n all-work one-works writing reading one-done all-done")
	#print("# n Ac       Bc        Ec      Fc      Cc       Dc")
	#for n in threadCounts :
	#	call("./gen.py -n %d --work %d %s" % (n, work, filePrefix))
	#	ace = float(modelCheck(filePrefix, Ace, None, debug))
	#	bce = float(modelCheck(filePrefix, Bce, None, debug))
	#	ece = float(modelCheck(filePrefix, Ece, None, debug))
	#	cce = float(modelCheck(filePrefix, Cce, None, debug))
	#	dce = float(modelCheck(filePrefix, Dce, None, debug))
	#	print(n, "%4.3f %4.3f %4.3f %4.3f %4.3f %4.3f" % (ace, bce-ace, ece-bce, 0 , dce-ece, 0))

	#print("")

	basePower = 11
	perThreadPowerCc = 4
	perThreadPowerRs = 6
	ghz = 2.5

	baseNanoJoulePerCycle = basePower / ghz

	nanoJoulePerLocalOperation = 2    # choosen through measuring and modelling work=10 cycles and looking at the numbers
	nanoJoulePerSharedOperation = 200 # super shitty estimate

	#for work in works :
	#	print("# work=%d" % work)
	#	#print("# operations (absolute values)")
	#	#print("# n     Al     As|    Bl     Bs|    El     Es|    Cl     Cs|    Dl     Ds      Cc-nJ Rs-nJ base-nJ")
	#	#print("#                                                                              w/o Base-nJ     ")
	#	print("# energy (absolute values in micro Joule)")
	#	print("# n      A      B      E      C      D")
	#	for n in threadCounts :
	#		call("./gen.py -n %d --work %d %s" % (n, work, filePrefix))
	#		ale = float(modelCheck(filePrefix, Ale, None, debug))
	#		ble = float(modelCheck(filePrefix, Ble, None, debug))
	#		ele = float(modelCheck(filePrefix, Ele, None, debug))
	#		cle = float(modelCheck(filePrefix, Cle, None, debug))
	#		dle = float(modelCheck(filePrefix, Dle, None, debug))

	#		ase = float(modelCheck(filePrefix, Ase, None, debug))
	#		bse = float(modelCheck(filePrefix, Bse, None, debug))
	#		ese = float(modelCheck(filePrefix, Ese, None, debug))
	#		cse = float(modelCheck(filePrefix, Cse, None, debug))
	#		dse = float(modelCheck(filePrefix, Dse, None, debug))

	#		ace = float(modelCheck(filePrefix, Ace, None, debug))
	#		bce = float(modelCheck(filePrefix, Bce, None, debug))
	#		ece = float(modelCheck(filePrefix, Ece, None, debug))
	#		cce = float(modelCheck(filePrefix, Cce, None, debug))
	#		dce = float(modelCheck(filePrefix, Dce, None, debug))

	#		#nanoJoulePerCycleCc = (perThreadPowerCc*n) / ghz
	#		#nanoJoulePerCycleRs = (perThreadPowerRs*n) / ghz
	#		#djBase = dce * baseNanoJoulePerCycle
	#		#djReferenceCc = dce * (nanoJoulePerCycleCc)
	#		#djReferenceRs = dce * (nanoJoulePerCycleRs)

	#		#print(" ", n, "%6.1f %6.1f|%6.1f %6.1f|%6.1f %6.1f|%6.1f %6.1f|%6.1f %6.1f      %5.0f %5.0f %7.0f" % (ale, ase, ble, bse, ele, ese, cle, cse , dle, dse, djReferenceCc, djReferenceRs, djBase))

	#		aj = ale*nanoJoulePerLocalOperation + ase*nanoJoulePerSharedOperation + ace*baseNanoJoulePerCycle
	#		bj = ble*nanoJoulePerLocalOperation + bse*nanoJoulePerSharedOperation + bce*baseNanoJoulePerCycle
	#		ej = ele*nanoJoulePerLocalOperation + ese*nanoJoulePerSharedOperation + ece*baseNanoJoulePerCycle
	#		cj = cle*nanoJoulePerLocalOperation + cse*nanoJoulePerSharedOperation + cce*baseNanoJoulePerCycle
	#		dj = dle*nanoJoulePerLocalOperation + dse*nanoJoulePerSharedOperation + dce*baseNanoJoulePerCycle

	#		#print(" ", n, "%6.0f %6.0f %6.0f %6.0f %6.0f" % (aj, bj-aj, ej-bj, cj-ej , dj-cj))
	#		print(" ", n, "%6.3f %6.3f %6.3f %6.3f %6.3f" % (aj / 1000.0, (bj-aj) / 1000.0, (ej-bj) / 1000.0, (cj-ej) / 1000.0 , (dj-cj) / 1000.0))

	#print("")

	#for work in works :
	#	print("# work=%d" % work)
	#	print("# n cycle  power (Watt)")
	#	for n in threadCounts :
	#		call("./gen.py -n %d --work %d %s" % (n, work, filePrefix))
	#		dce = float(modelCheck(filePrefix, Dce, None, debug))
	#		dle = float(modelCheck(filePrefix, Dle, None, debug))
	#		dse = float(modelCheck(filePrefix, Dse, None, debug))
	#		startCycle = 0
	#		endCycle   = dce
	#		step       = (int((endCycle - startCycle) / 10**math.floor((math.log(endCycle - startCycle, 10)))) * 10**math.floor((math.log(endCycle - startCycle, 10)))) / 10
	#		#print (startCycle, endCycle, step)

	#		djLast = 0.0
	#		i = startCycle
	#		while i <= endCycle :

	#			dl = float(modelCheck(filePrefix, Dl, i, debug))
	#			ds = float(modelCheck(filePrefix, Ds, i, debug))

	#			dj = dl*nanoJoulePerLocalOperation + ds*nanoJoulePerSharedOperation + i*baseNanoJoulePerCycle

	#			print(" ", n, "%5d" % i, "%6.3f" % ((dj - djLast) / (step / ghz)))

	#			i += step
	#			djLast = dj

	#		overall = (dle*nanoJoulePerLocalOperation + dse*nanoJoulePerSharedOperation + dce*baseNanoJoulePerCycle) / (dce / ghz)

	#		print(" ", n, "overall %6.3f" % overall)

	#print("")

	for work in works :
		print("# work=%d" % work)
		print("# energy (Watt per phase)")
		print("# n      D      C      E      B      A overall")
		for n in threadCounts :
			call("./gen.py -n %d --work %d %s" % (n, work, filePrefix))
			ale = float(modelCheck(filePrefix, Ale, None, debug))
			ble = float(modelCheck(filePrefix, Ble, None, debug))
			ele = float(modelCheck(filePrefix, Ele, None, debug))
			cle = float(modelCheck(filePrefix, Cle, None, debug))
			dle = float(modelCheck(filePrefix, Dle, None, debug))

			ase = float(modelCheck(filePrefix, Ase, None, debug))
			bse = float(modelCheck(filePrefix, Bse, None, debug))
			ese = float(modelCheck(filePrefix, Ese, None, debug))
			cse = float(modelCheck(filePrefix, Cse, None, debug))
			dse = float(modelCheck(filePrefix, Dse, None, debug))

			ace = float(modelCheck(filePrefix, Ace, None, debug))
			bce = float(modelCheck(filePrefix, Bce, None, debug))
			ece = float(modelCheck(filePrefix, Ece, None, debug))
			cce = float(modelCheck(filePrefix, Cce, None, debug))
			dce = float(modelCheck(filePrefix, Dce, None, debug))

			aj = ale*nanoJoulePerLocalOperation + ase*nanoJoulePerSharedOperation + ace*baseNanoJoulePerCycle
			bj = ble*nanoJoulePerLocalOperation + bse*nanoJoulePerSharedOperation + bce*baseNanoJoulePerCycle
			ej = ele*nanoJoulePerLocalOperation + ese*nanoJoulePerSharedOperation + ece*baseNanoJoulePerCycle
			cj = cle*nanoJoulePerLocalOperation + cse*nanoJoulePerSharedOperation + cce*baseNanoJoulePerCycle
			dj = dle*nanoJoulePerLocalOperation + dse*nanoJoulePerSharedOperation + dce*baseNanoJoulePerCycle

			aw = (aj)    / ((ace)     / ghz)
			bw = (bj-aj) / ((bce-ace) / ghz)
			ew = (ej-bj) / ((ece-bce) / ghz)
			cw = (cj-ej) / ((cce-ece) / ghz)
			dw = (dj-cj) / ((dce-cce) / ghz)

			print(" ", n, "%6.1f %6.1f %6.1f %6.1f %6.1f %7.1f" % (dw, cw, ew, bw, aw, dj / (dce / ghz)))

	finalize(debug)
