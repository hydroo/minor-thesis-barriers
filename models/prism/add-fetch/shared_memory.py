import misc

# returns prism-model-string, prism-correctness-prop-string
def generatePrerequisites(threadCount, readTicks, writeTicks) :

	s = ""
	t = ""

	for i in range(0, threadCount) :
		s += "const me_" + str(i) + " = " + str(i) + "; "
	s += "\n"
	for i in range(0, threadCount) :
		s += "const me_bit_" + str(i) + " = " + str(2**i) + "; "
	
	s += "\n"

	s += "const empty = 0; "
	s += "const full  = "
	for i in range(0, threadCount) :
		s += "me_bit_" + str(i) + " + "
	s += "0;\n"

	s += "\n"

	s += "const someoneIsModified   = 0;\n"
	s += "const someoneDoesAtomicOp = 1;\n"
	s += "const someAreShared       = 2;\n"

	s += "\n"

	s += "const read_ticks         = " + str(readTicks) + ";\n"
	s += "const write_ticks        = " + str(writeTicks) + ";\n"
	s += "const atomic_begin_ticks = write_ticks;\n"

	s += "\n"

	s += "const double read         = tick / read_ticks;\n"
	s += "const double write        = tick / write_ticks;\n"
	s += "const double atomic_begin = tick / atomic_begin_ticks;\n"

	return s, t

# returns prism-model-string, prism-correctness-prop-string
def generateVariable(name, typee, init, values, threadCount, debug) :

	s = ""

	s += misc.generatePseudoGlobalVariable(name, typee, init, values, threadCount)

	s += "\n"

	s += "module var_shared\n"

	s += "\tvar_state : [someoneIsModified..someAreShared] init someoneIsModified;\n"
	s += "\tvar_who   : [empty..full] init empty;\n"
	if debug == True:
		s += "\tvar_error : bool init false;"

	s += "\n"

	for p in range(0,threadCount) :
		s += "\n"
		for value in values :
			s += "\t[var_set_to_" + value + "_#] (var_state =someoneIsModified   & var_who =me_bit_#)          -> tick         : true;\n"
			s += "\t[var_set_to_" + value + "_#] (var_state =someoneDoesAtomicOp & var_who =me_bit_#)          -> tick         : true;\n"
			s += "\t[var_set_to_" + value + "_#] (var_state =someoneIsModified   & var_who!=me_bit_#)          -> write        : (var_who'=me_bit_#);\n"
			s += "\t[var_set_to_" + value + "_#] (var_state =someAreShared)                                    -> write        : (var_state'=someoneIsModified) & (var_who'=me_bit_#);\n"

		s += "\n"

		s += "\t[var_read_#] var_state=someoneIsModified   & var_who =me_bit_#                 -> tick         : true;\n"
		s += "\t[var_read_#] var_state=someoneDoesAtomicOp & var_who =me_bit_#                 -> tick         : true;\n"
		s += "\t[var_read_#] var_state=someoneIsModified   & var_who!=me_bit_#                 -> read         : (var_state'=someAreShared) & (var_who'=min(full,max(var_who+me_bit_#, empty)));\n"
		s += "\t[var_read_#] var_state=someAreShared       & mod(floor(var_who/me_bit_#),2)=1  -> tick         : true;\n"
		s += "\t[var_read_#] var_state=someAreShared       & mod(floor(var_who/me_bit_#),2)=0  -> read         : (var_who'=min(full,max(var_who+me_bit_#, empty)));\n"

		s += "\n"

		s += "\t[var_atomic_begin_#] (var_state =someoneIsModified   & var_who =me_bit_#)      -> tick         : (var_state'=someoneDoesAtomicOp);\n"
		s += "\t[var_atomic_begin_#] (var_state =someoneIsModified   & var_who!=me_bit_#)      -> atomic_begin : (var_state'=someoneDoesAtomicOp) & (var_who'=me_bit_#);\n"
		s += "\t[var_atomic_begin_#] (var_state =someAreShared)                                -> atomic_begin : (var_state'=someoneDoesAtomicOp) & (var_who'=me_bit_#);\n"
		s += "\t[var_atomic_end_#]   (var_state =someoneDoesAtomicOp & var_who =me_bit_#)      -> tick         : (var_state'=someoneIsModified);\n"

		if debug == True :
			s += "\t[var_atomic_begin_#] (var_state =someoneDoesAtomicOp & var_who =me_bit_#)      ->                (var_error'=true);\n"
			s += "\t[var_atomic_end_#]   (var_state =someoneDoesAtomicOp & var_who!=me_bit_#)      ->                (var_error'=true);\n"
			s += "\t[var_atomic_end_#]   (var_state!=someoneDoesAtomicOp)                          ->                (var_error'=true);\n"

		s = s.replace('#', str(p))

	s += "endmodule\n"
	s += "\n"

	# labels
	for p in range(0, threadCount) :
		s += "label \"var_invalid_#\"   = ((var_state=someoneIsModified   | var_state=someAreShared) & mod(floor(var_who/me_bit_#),2)=0);\n"
		s += "label \"var_modified_#\"  =  (var_state=someoneIsModified   & var_who=me_bit_#);\n"
		s += "label \"var_atomic_op_#\" =  (var_state=someoneDoesAtomicOp & var_who=me_bit_#);\n"
		s += "label \"var_shared_#\"    =  (var_state=someAreShared       & mod(floor(var_who/me_bit_#),2)=1);\n"
		s = s.replace('#', str(p))

	# correctness props
	t = ""

	t += "P<=0 [F (var_state=someoneIsModified   &  " + " & ".join(["var_who!=0"] + [ "var_who!=me_bit_%d" % i for i in range(0, threadCount) ]) + ")]; // one or zero threads can be in modified state at a time\n"

	t += "P<=0 [F (var_state=someoneDoesAtomicOp &               " + " & ".join([ "var_who!=me_bit_%d" % i for i in range(0, threadCount) ]) + ")]; // one and only one thread can be in atomic op state at a time\n"

	t += "\n"
	t += "P<=0 [F (var_state=someAreShared       & (" + " | ".join(["var_who =0"] + [ "var_who =me_bit_%d" % i for i in range(0, threadCount)]) + "))]; // if a cache copy is shared, at least one other is too\n"

	if debug == True :
		t += "\n"
		t += "P<=0 [F (var_error=true)]; // if a cache copy is shared, at least one other is too\n"


	s = s.replace("var_", name + "_")
	t = t.replace("var_", name + "_")

	return s, t

# returns prism-model-string
def generateRewards() :
	s = ""
	#s += "rewards \"time\"\n"
	#s += "\ttrue : 1;\n"
	#s += "endrewards\n"
	return s

