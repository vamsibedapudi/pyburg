"""
cyburg -- A python 3 implementation of iburg which is originally written in c
This is the root file
Usage: python3 cyburg.py [-T | -I | -p prefix | -maxcost=ddd ]... [ [ input ] output
"""

import sys
import math
import globals
from util import *
from gram import *

table =globals.table
nts = globals.nts
terms = globals.terms
rules = globals.rules
TERM = globals.TERM
NONTERM = globals.NONTERM


infp = None
outfp = None
Iflag = 0
Tflag = 0
maxcost = 32767
prefix = "prefix"
errcnt = 0



def yywarn(msg, *args):
	"""
	prints warnings to the stdout along with the lineno
	"""
	print("line %d: warning: " % globals.yylineno + msg % args)

def yyerror(msg, *args):
	"""
	prints errors to the stdout along with the lineno
	"""
	print("line %d: " % globals.yylineno +msg % args)
	global errcnt
	errcnt += 1

def copyheader():
	"""
	copy the header of the input file to output file
	"""
	prev_pos = infp.tell()
	buf = infp.readline()
	if not buf:
		return
	while (buf == "%{\n" or buf == "%{\r\n"):
		globals.yylineno += 1
		while True:
			buf = infp.readline()
			if not buf:
				print("unterminated %{...%}")
				return
			globals.yylineno += 1
			if (buf == "%}\n" or buf == "%}\r\n"):
				break
			outfp.write(buf)
		prev_pos = infp.tell()
		buf = infp.readline()
		if not buf:
			return
	infp.seek(prev_pos)

def yyparse():
	"""
	parses the tree grammar and stores all the terms, nts and rules
	"""
	globals.yylineno += 1
	ppercent = 0
	data = ""
	while True:
		buf = infp.readline()
		if not buf:
			break
		# %% should be in a single line
		if "%%" in buf:
			if (buf != "%%\n" and buf != "%%"):
				print("Other characters in %% line will be ignored")
			if ppercent:
				break
			else:
				ppercent += 1
		data += buf
	import ply.lex as lex
	import ply.yacc as yacc
	lexer = lex.lex()
	globals.parser = yacc.yacc()
	# print(data)
	globals.parser.parse(data)

def copyfooter():
	"""
	copy the footer of the input file to output file
	"""
	global yylineno
	outfp.write("\n")
	while True:
		buf = infp.readline()
		if not buf:
			return
		globals.yylineno += 1
		outfp.write(buf)

def getntnumber():
	globals.ntnumber += 1
	return globals.ntnumber

def declared(name):
	if name in table.keys():
		return table[name]
	else:
		return None

def term(name,esn):
	"""create a new terminal name with external symbol number esn"""
	p = declared(name)
	if p:
		yyerror("redefinition of terminal '%s'", name)
	else:
		p = Term(name)
	p.esn = esn
	p.kind = TERM
	p.arity = -1
	table[name] = p
	for term in terms:
		if term.esn == esn:
			yyerror("duplicate external symbol number '%s=%d'\n",p.name, p.esn)
	terms.append(p)
	return p

def nonterm(name):
	"""create a new terminal name, if necessary"""
	p = declared(name)
	if p:
		p = table[name]
		if p.kind == NONTERM:
			return p
		elif p.kind == TERM:
			yyerror("'%s' is a terminal",name)
	else:
		p = Nonterm(name)
	p.number = getntnumber()
	p.kind = NONTERM
	table[name] = p
	if (p.number == 1):
		# global start
		globals.start = p;
	nts.append(p)
	return p

def tree(name,left=None,right=None):
	"""create & initialize a tree node with the given fields"""
	arity = 0
	if left :
		arity += 1
	if right:
		arity += 1
	if not declared(name):
		if arity > 0:
			yyerror("undefined terminal '%s'", name)
			p = term(name, -1)
		elif arity == 0:
			p = nonterm(name)
	else:
		p = table[name]
		if (p.kind == NONTERM and arity > 0):
			yyerror("`%s' is a non-terminal and arity > 0", name)
			p = term(name, -1)
	if (p.kind == TERM and p.arity == -1):
		p.arity = arity
	if (p.kind == TERM and arity != p.arity):
		yyerror("inconsistent arity for terminal '%s'", name)
	t = Tree()
	t.op = p
	t.left = left
	t.right = right

	t.nterms = (p.kind == TERM)
	if left is not None:
		t.nterms += left.nterms
	if right is not None:
		t.nterms += right.nterms

	return t

def rule(lhs,rhs,ern,cost):
	"""create & initialize a rule with the given fields"""
	r = Rule()
	p = rhs.op
	nt = nonterm(lhs)
	r.lhs = nt
	nt.rules.append(r);	

	r.packed = len(nt.rules)
	r.rhs = rhs
	r.ern = ern
	r.cost = cost

	if (p.kind == TERM):
		p.rules.append(r)
	elif (p.kind == NONTERM and rhs.left is None and rhs.right is None):
		p.chain.append(r)
	for rule in rules:
		if (rule.ern == r.ern):
			yyerror("duplicate external rule number '%d'", r.ern);
	rules.append(r)
	return r

def printf(msg, *args):
	"""prints formatted output"""
	class Count:
		counter=-1
	counter = Count()
	def getArg(counter = counter):
		counter.counter += 1
		return args[counter.counter]
	i=0
	while i < len(msg):
		if msg[i] == '~':
			i += 1
			if msg[i] == 'd':
				outfp.write(str(getArg()))
			elif msg[i] == 's':
				outfp.write(getArg())
			elif msg[i] == 'P':
				outfp.write(prefix+'_')
			elif msg[i] == 'T':
				t = getArg()
				printf("~S", t.op)
				if (t.left and t.right):
					printf("(~T,~T)", t.left, t.right)
				elif (t.left):
					printf("(~T)", t.left)

			elif msg[i] == 'R':
				r = getArg()
				printf("~S: ~T", r.lhs, r.rhs)
			elif msg[i] == 'S':
				p = getArg()
				outfp.write(p.name)
			elif (msg[i] == '1' or msg[i] == '2' or msg[i] == '3' or msg[i] == '4' or msg[i] == '5'): 
				count = int(msg[i])
				for j in range(0,count):
					outfp.write('\t')
			else:
				outfp.write("~"+msg[i])
		else:
			outfp.write(msg[i])
		i += 1

		
def reach(t):
	""" mark all non-terminals in tree t as reachable"""
	p = t.op
	if p.kind == NONTERM:
		if not p.reached:
			ckreach(p)
	if t.left:
		reach(t.left)
	if t.right:
		reach(t.right)


def ckreach(p):
	"""mark all non-terminals reachable from p"""
	p.reached = 1
	for r in p.rules:
		reach(r.rhs)


def emitheader():
	"""emit initial definitions"""
	printf('''try:
	MAX_COST # exists
except NameError:
	MAX_COST = 1e16\n\n''')

	printf('''try :
	trace
except NameError:
	def trace(p, rule, cost, bestcost):
		sys.stdout.write("%s matched %s with cost %d vs. %d\\n" % (p,rule.name, cost, bestcost))\n\n''')

def emitdefs():
	"""emit non-terminal defines and data structures"""
	printf("~PMAX_NT = ~d;\n\n", globals.ntnumber)
	for p in nts:
		printf("~P~S_NT = ~d\n", p, p.number-1)

	# if Iflag:
	# 	printf("\n~Pntname[] = [")
	# 	for p in nts:
	# 		printf("~1\"~S\",\n", p)
	# 	printf("\n];\n\n")


def emitnts():
	printf("\n~Pnts = {\n\n")
	for p in nts:
		printf("~1~d : \"~S\",\n", p.number-1, p)
	printf("}\n\n")	

def emitterms():
	printf("\n~Pterms = {\n\n")
	for p in terms:
		printf("~1~d : \"~S\",\n", p.esn, p)
	printf("}\n\n")


def computents(t):
	"""fill in ret with burm_nts vector for tree t"""
	ret = ""
	if t:
		p = t.op;
		if p.kind == NONTERM:
			ret += "%s_%s_NT, "%(prefix, p.name)
		ret += computents(t.left) 
		ret += computents(t.right)
	return ret;

def emitrules():
	printf('''class Rule:
	def __init__(self, value, lhs, rhs, nts, cost):
		self.value = value # entire rule as a string in its original format
		self.lhs = lhs # ntnumber of lhs
		self.rhs = rhs # string of rhs
		self.nts = nts # all nts in rhs
		self.cost = cost # cost of the rule\n''')

	printf("\n~Prules = {\n\n")
	for r in rules:
		nts = "["+computents(r.rhs)+ "]"
		printf("~1~d : Rule(\"~R\", ~d, \"~T\", ~s , ~d),\n", r.ern, r, r.lhs.number-1, r.rhs, nts ,r.cost )
	printf("}\n\n")

def emitfuncs():
	printf('''# gives the best rule to apply for that non-terminal
def getrule(p, goalnt):
	assert goalnt in nts.keys(), "Bad goal nonterminal %d in getrule\\n" % goalnt
	assert p, "Bad Node argument to getrule\\n"
	ruleno = p.rule[goalnt];
	assert ruleno in rules.keys(), "Bad rule number %d for non-terminal %d in getrule\\n" % (ruleno, goalnt)
	return rules[ruleno]\n\n''')


def emitnode():
	"""emit the definition of the state structure"""
	printf('''class Node:

	def __init__(self):
		self.value = None # esn
		self.children = [] #child nodes
		self.cost = [ MAX_COST for i in range(MAX_NT)]
		self.rule = [ -1 for i in range(MAX_NT)]

	def label(self):
		for child in self.children:
			assert child, "Bad Child for Node %d in tree\\n"% self.value
			child.label()
		self.match()\n\n''')


def emitrecord(prefix, r, cost):
	"""emit code that tests for a winning match of rule r"""
	if Tflag: printf("~s~Ptrace(self, ~d, cost + ~d, p.cost[~P~S_NT])\n",prefix, r.ern, cost, r.lhs)	

	printf("~sif (", prefix);
	
	printf("cost + ~d < self.cost[~P~S_NT]): # ~R\n", cost, r.lhs, r)
	printf("~s~1self.cost[~P~S_NT] = cost + ~d;\n",prefix, r.lhs, cost)
	printf("~s~1self.rule[~P~S_NT] = ~d;\n",prefix, r.lhs, r.ern);
	if len(r.lhs.chain):printf("~s~1self.closure_~S(cost + ~d);\n", prefix, r.lhs, cost);
	printf("\n");

def emitclosure():
	"""emit the closure functions"""
	for p in nts:
		if len(p.chain):
			printf("~1def closure_~S(self, cost): \n", p);
			for r in p.chain:
				emitrecord("\t\t", r, r.cost)
	printf("\n")

def emitstate():
	printf('''\tdef match(self):
		if self.value is None: assert 0, "No value in node\\n"\n''')

	for p in terms:
		emitcase(p)

	printf('''\t\telse: assert 0, "Bad operator %d in match\\n" % self.value\n\n''')






def emitcase(p):
	"""emit one case in function state"""
	if p.kind==NONTERM:
		print("Internal Error: emitcase being called for a non terminal %s"%p.name)
		return
	
	printf("\n~2elif self.value == ~d: # ~S\n", p.esn, p)

	printf('''\n~3assert len(self.children) == ~d, " Invalid arity supplied to %d"%self.value\n''', p.arity)
	if p.arity == 0 or p.arity == -1: pass
	elif p.arity==1:
		printf('''~3l = self.children[0]
			assert l, "Left Child is None for %d"%self.value\n''')
	elif p.arity==2:
		printf('''~3l = self.children[0]
			assert l, "Left Child is None for %d"%self.value\n''')
		printf('''~3r = self.children[1]
			assert r, "Right Child is None for %d"%self.value\n''')
	else: print("Arity exceeds for ~S",p)
	printf("\n")

	for r in reversed(p.rules):
		if r.rhs.nterms <= 1:
			printf("~3if (~1# ~R\n", r);
			printf("~4True # No terminals\n")
			printf("~3):\n~4c = ");
		else:
			printf("~3if (~1# ~R\n", r);
			if r.rhs.left: emittest(r.rhs.left, "self.children[0]", "and" if r.rhs.right else "");
			if r.rhs.right: emittest(r.rhs.right, "self.children[1]", "");
			printf("~3):\n~4c = ");
		if r.rhs.left: emitcost(r.rhs.left,  "l");
		if r.rhs.right: emitcost(r.rhs.right,  "r");
		printf("~d;\n", r.cost);
		emitrecord("\t\t\t\t", r, 0);


def emitcost(t, v):
	"""emit cost computation for tree t"""
	p = t.op
	if p.kind == TERM:
		if t.left:
			emitcost(t.left, "%s.children[0]" %  v)
		if t.right:
			emitcost(t.right, "%s.children[0]" % v)
	else:
		printf("~s.cost[~P~S_NT] + ", v, p)


def emittest(t, v, suffix):
	"""emit clause for testing a match"""
	if t is None:
		print("Internal Error, Empty Tree Passed to emittest\n")
		return

	p = t.op
	if p.kind == TERM:
		printf("~4~s.value == ~d ~s # ~S\n", v, p.esn, "and" if t.nterms>1 else suffix, p);
		if t.left: emittest(t.left,"%s.children[0]"%v, "and" if t.right and t.right.nterms else suffix)
		if t.right: emittest(t.right,"%s.children[1]"%v, suffix)




# def emitstate(terms, start, ntnumber):
# 	"""emit state function"""
# 	printf("STATE_TYPE %Pstate(int op, STATE_TYPE left, STATE_TYPE right) {\n%1int c;\n"
# "%1struct %Pstate *p, *l = (struct %Pstate *)left,\n"
# "%2*r = (struct %Pstate *)right;\n\n%1assert(sizeof (STATE_TYPE) >= sizeof (void *));\n%1");
# 	printf("{\n%2p = ALLOC(sizeof *p);\n"
# "%2%Passert(p, PANIC(\"ALLOC returned NULL in %Pstate\\n\"));\n"
# "%2p->op = op;\n%2p->left = l;\n%2p->right = r;\n%2p->rule.%P%S = 0;\n", start);
# 	for i in range(1,ntnumber+1):
# 		printf("%2p->cost[%d] =\n", i);
# 	printf("%3%d;\n%1}\n%1switch (op) {\n", maxcost);
# 	for p in terms:
# 		emitcase(p)
# 	printf("%1default:\n"
# "%2%Passert(0, PANIC(\"Bad operator %%d in %Pstate\\n\", op));\n%1}\n"
# "%1return (STATE_TYPE)p;\n}\n\n")




def computekids(t, v, kidnum):
	"""compute paths to kids in tree t"""
	p = t.op;
	ret = ""
	if p.kind == NONTERM:
		ret += "\t\tkids[%d] = %s;\n"% (kidnum.count , v)
		kidnum.count+=1
	elif p.arity > 0:
		ret += computekids(t.left, "LEFT_CHILD(%s)" % v, kidnum);
		if p.arity == 2:
			ret += computekids(t.right, "RIGHT_CHILD(%s)" % v, kidnum)
	return ret

def emitkids():
	"""emit burm_kids"""
	class KidCount:
		count=0
	existing = {}
	for r in rules:
		out = computekids(r.rhs, "p", KidCount())
		if existing.get(out) is None:
			existing[out] = [r]
		else:
			existing[out].append(r)

	printf('''#  returns nodes to be matched and the non-terminals to which they must be  further to matched based on the rule applied to the current node
def getmatchedkids(p, rule):\n
	kids = []
	ruleno = rule.number
	assert p, PANIC("Bad Node argument tree in kids\\n");
	if ruleno is None: assert 0, "No rulenumber associated with rule"\n''')

	for out,rulesList in existing.items():
		printf('''~1elif(\n''')
		for r in reversed(rulesList):
			printf("%1case %d: /* %R */\n", r.ern, r)
		printf("~2):\n")
		printf("~2~s\n", out)
	printf("%1default:\n%2%Passert(0, PANIC(\"Bad external rule number %%d in %Pkids\\n\", eruleno));\n%1}\n%1return kids;\n}\n\n");



def main():
	"""main function"""
	global infp,outfp,Iflag,Tflag
	for i in range(1,len(sys.argv)):
		arg = sys.argv[i]
		if sys.argv[i] == "-I":
			Iflag = 1
		elif sys.argv[i] == "-T":
			Tflag = 1
		elif sys.argv[i][0:9] == "-maxcost=":
			maxcost = int(sys.argv[i][9:])
		elif sys.argv[i][0:2] == "-p" and len(sys.argv[i])>2:
			prefix = sys.argv[i][2:]
		elif sys.argv[i][0:2] == "-p" and i+1 < len(sys.argv):
			i = i+1
			prefix = sys.argv[i]
		elif sys.argv[i][0] == '-' and len(sys.argv[i])>1:
			print("usage: python3 %s [-T | -I | -p prefix | -maxcost=ddd ]... [ [ input ] output " % (sys.argv[0]))
			exit(1)
		elif infp is None:
			if sys.argv[i] == "-":
				infp = sys.stdin
			else:
				try:
					infp = open(sys.argv[i], "r")
				except:
					print("%s: can't read '%s' " % (sys.argv[0], sys.argv[i]))
					exit(1)
		elif outfp is None:
			if sys.argv[i] == "-":
				outfp = sys.stdout
			else:
				try:
					outfp = open(arg, "w")
				except:
					print("%s: can't write '%s' " % (sys.argv[0], sys.argv[i]))
					exit(1)
	if infp is None:
		infp = sys.stdin
	if outfp is None:
		outfp = sys.stdout

	copyheader()
	yyparse()

	def sortUsingesn(term):
		return term.esn
	def sortUsingntnumber(nt):
		return nt.number
	def sortUsingern(rule):
		return rule.ern
	terms.sort(key = sortUsingesn)
	nts.sort(key = sortUsingntnumber)
	rules.sort(key = sortUsingern)

	if globals.start:
		ckreach(globals.start)

	for p in nts:
		if not p.reached:
			printf("can't reach non-terminal `%s'\n", p.name);

	emitheader();

	emitdefs();

	emitnts();

	emitterms();

	emitrules();

	emitkids();

	emitfuncs();

	emitnode();

	emitclosure();

	emitstate();


	# printf("/* emitnts(rules, nrules) - started */\n");
	# emitnts(rules);
	# printf("/* emitnts(rules, nrules) - ended */\n\n");

	# printf("/* emitterms(terms) - started */\n");
	# emitterms(terms);
	# printf("/* emitterms(terms) - ended */\n\n");

	# printf("/* emitstring(rules) - started */\n");
	# if Iflag:
	# 	emitstring(rules);
	# printf("/* emitstring(rules) - ended */\n\n");

	# printf("/* emitrule(nts) - started */\n");
	# emitrule(nts);
	# printf("/* emitrule(nts) - ended */\n\n");

	# printf("/* emitclosure(nts) - started */\n");
	# emitclosure(nts);
	# printf("/* emitclosure(nts) - ended */\n\n");


	# printf("/* emitstate(nts) - started */\n");
	# if (globals.start):
	# 	emitstate(terms, globals.start, globals.ntnumber);
	# printf("/* emitstate(nts) - ended */\n\n");

	
	# printf("#ifdef STATE_LABEL\n");
	# printf("/* emitlabel(start) - started */\n");
	# if (globals.start):
	# 	emitlabel(globals.start);
	# printf("/* emitlabel(start) - ended */\n\n");

	# printf("/* emitkids(rules, nrules) - started */\n");
	# emitkids(rules);
	# printf("/* emitkids(rules, nrules) - ended */\n\n");
	
	# printf("/* emitfuncs() - started */\n");
	# emitfuncs();
	# printf("/* emitfuncs(); - ended */\n\n");

	# printf("#endif\n");


	# printf("/* footer of the input file - started */\n");
	# copyfooter()
	# printf("/* footer of the input file - ended */\n\n");

	return errcnt > 0;

				
  
if __name__== "__main__":
	main()