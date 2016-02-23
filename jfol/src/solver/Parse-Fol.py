#!/usr/bin/python
import sys
import waxeye
import _parser   #_parser.py for FOL
import fileinput
import string

binary_symbols = {"and": "AND", "or": "OR", "implies": "IMP", "equivalent": "EQUIV"}

#####################################################################
p = _parser.Parser()
def parse(it):
        original_string = it
        ast = p.parse(it)
        if isinstance(ast,waxeye.ParseError):
                print "ERROR: Failed parse of line:"
                print original_string
                print ast #waxeye outputs error msg if parse fails
                exit()
        return ast

#Named expressions store the name as a sequence of chars, beginning
#with the first index of their "children" list.
def last_name_index(ast):
        
        for i,v in enumerate(ast.children):
                if not isinstance(v,str):
                        return i
        return False

#A termlist always has a term at its first child.
#It MAY have another termlist as its second child.
def SchemizeTermList(ast):
        out = Schemize(ast.children[0])
        
        if len(ast.children) == 2:
                return out + SchemizeTermList(ast.children[1])
        return out
        
def Schemize(ast):
        if ast.type == "sentence":
                return Schemize(ast.children[0])

        if ast.type == "expression":
                if ast.children[0].type == "negation":
                        return "(neg " + Schemize(ast.children[1]) + ")"
                return Schemize(ast.children[0])

        if ast.type == "relation" or ast.type == "function":
                if ast.type == "relation":
                        f = "relation"
                if ast.type == "function":
                        f = "function"
                
                name_last = last_name_index(ast)
                name =  ''.join(ast.children[:name_last])
                return "(" + ast.type + " '" + name + " " + SchemizeTermList(ast.children[name_last]) + ")"
        
        if ast.type == "constant":
                return "(constant '" + ''.join(ast.children) + ") "
        
        if ast.type == "variable":
                return "(variable '" + ''.join(ast.children) + ") "

        if ast.type == "universal" or ast.type == "existential":
                return "(" + ast.type + " '" + ''.join(ast.children[0].children) + " " + Schemize(ast.children[1]) + ")"

        if ast.type == "binary":
                return "(binary '" + binary_symbols[  ''.join(ast.children[1].children).lower() ] + " " + Schemize(ast.children[0]) + " " + Schemize(ast.children[2]) + " )"
        
#####################################################################


def parse_input():
	premises   = []
	conclusion = [] #vector...?
	current_source = premises

	#a for axiom. Treated no differently than premises.
	directives = {'a': premises, 'p': premises , 'c': conclusion}

	#transform the input
	line_number = -1
	for line in fileinput.input(): #This support both regular stdin AND $1 filename??
		line_number += 1
		if line[0] == '#':
			if len(line) > 1 and directives.has_key(line[1]):
				current_source = directives[line[1]]
			else:
				print "ERROR: line " + str(line_number) + " contains an invalid directive:"
				print line
				print "The only valid directives are: " + str(directives.keys())
				exit()
		else:
			if current_source == conclusion and len(current_source) == 1:
				print "ERROR: more than one conclusion?"
				exit()
			current_source.append(string.strip(line)) #remove surrounding whitespace..

	if len(conclusion) != 1:
		print "ERROR: No conclusion?"
		exit()

	#Parse every sentence
	#...Apparently I can't do this with a for loop on [conclusion,premises]....
	conclusion = [ Schemize(parse(x)) for x in conclusion ]
	premises   = [ Schemize(parse(x)) for x in premises   ]

	output = ""

	print "OK!"

	for p in conclusion:
		output += "\"" + p + "\"   "

	for p in premises:
		output += "\"" + p + "\"   "
                
	sys.stdout.write(output + "\n")


parse_input()
