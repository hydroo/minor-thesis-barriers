"Yet Another Python Templating Utility, Version 1.2"

import os
import re
import sys
import fileinput
from collections import Counter
from copier import Copier
from ast import literal_eval

USAGE = 'Usage: python ' + os.path.basename(sys.argv[0]) + ' [<var>=<value> ...] [-f <input-file>]'
HELP = ('-?', '--?', '-help', '--help')
REX = re.compile('\$([^\$]+)\$')
RBE = re.compile('\+\+')
REN = re.compile('--')
RCO = re.compile('~~')

def process_cmd_args(args) :
	template, variables = read_template_and_variables(args)	
	lines = [line for line in template]
	variables = parse_variables(variables)
	return lines, variables

def read_template_and_variables(args) :
	if len(args) > 1 and args[-2] == '-f' :
		if not os.path.exists(args[-1]) :
			raise ValueError('<input-file> apparently does not exist')
		template = fileinput.input(args[-1:])
		variables = args[1:-2]
	else :
		template = fileinput.input([])
		variables = args[1:]
	return template, variables

def parse_variables(variables):
	variables = [tuple(var.split('=',1)) for var in variables]
	variable_names = []
	try:
		for (name, value) in variables :
			if name == '' :
				raise ValueError
			variable_names.append(name)
	except ValueError:
		raise ValueError('variable not in format <name>=<value>')
	for (name, n) in Counter(variable_names).iteritems() :
		if n > 1 :
			raise ValueError('ambiguous variable ' + name)
	return {name : literal_or_string(value) for (name, value) in variables}

def literal_or_string(s) :
	try:
		return literal_eval(s)
	except SyntaxError:
		return s


for each in sys.argv:
	if each in HELP :
		print USAGE
		sys.exit()

try:
	template, variables = process_cmd_args(sys.argv)
except Exception as e:
	print >> sys.stderr, e
	sys.exit(1)

cop = Copier(dict=variables, regex=REX, restat=RBE, restend=REN, recont=RCO)
cop.copy(template)