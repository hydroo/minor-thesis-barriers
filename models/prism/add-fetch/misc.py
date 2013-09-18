# works around the problem that global variables cannot be assigned a value in a synchronized transition
# by making it a local variable with transitions for assigning values
def generatePseudoGlobalVariable(name, typee, init, values, threadCount) :

	s = ""

	s += "module " + name + "_variable\n"
	s += "\t" + name + " : " + typee + " init " + init + ";\n"

	for p in range(0, threadCount) :
		for value in values :
			s += "\t[" + name + "_set_to_" + value + "_#] true -> (" + name + "'=" + value + ");\n"
		s = s.replace('#', str(p))

	s += "endmodule\n"

	return s

