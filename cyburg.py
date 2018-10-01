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
prefix = "burm"
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
		if msg[i] == '%':
			i += 1
			if msg[i] == 'd':
				outfp.write("%d" % getArg())
			elif msg[i] == 's':
				outfp.write(getArg())
			elif msg[i] == 'P':
				outfp.write("%s_" % prefix)
			elif msg[i] == 'T':
				t = getArg()
				printf("%S", t.op)
				if (t.left and t.right):
					printf("(%T,%T)", t.left, t.right)
				elif (t.left):
					printf("(%T)", t.left)

			elif msg[i] == 'R':
				r = getArg()
				printf("%S: %T", r.lhs, r.rhs)
			elif msg[i] == 'S':
				p = getArg()
				outfp.write(p.name)
			elif (msg[i] == '1' or msg[i] == '2' or msg[i] == '3' or msg[i] == '4' or msg[i] == '5'): 
				count = int(msg[i])
				for j in range(0,count):
					outfp.write('\t')
			else:
				outfp.write("%"+msg[i])
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
	printf("#include <limits.h>\n#include <stdlib.h>\n");
	printf("#ifndef STATE_TYPE\n#define STATE_TYPE int\n#endif\n");
	printf("#ifndef ALLOC\n#define ALLOC(n) malloc(n)\n#endif\n"
"#ifndef %Passert\n#define %Passert(x,y) if (!(x)) { y; abort(); }\n#endif\n\n")
	if Tflag:
		printf("static NODEPTR_TYPE %Pnp;\n\n")

def emitdefs(nts, ntnumber):
	"""emit non-terminal defines and data structures"""
	for p in nts:
		printf("#define %P%S_NT %d\n", p, p.number)
	printf("int %Pmax_nt = %d;\n\n", ntnumber)

	if Iflag:
		printf("char *%Pntname[] = {\n%10,\n")
		for p in nts:
			printf("%1\"%S\",\n", p);
		printf("%10\n};\n\n");

def emitstruct(nts, ntnumber):
	"""emit the definition of the state structure"""
	printf("struct %Pstate {\n%1int op;\n%1struct %Pstate *left, *right;\n"
"%1short cost[%d];\n%1struct {\n", ntnumber + 1)
	for nonterm in nts:
		n = len(nonterm.rules)
		printf("%2unsigned %P%S:%d;\n", nonterm, math.floor(math.log(n,2))+1)
	printf("%1} rule;\n};\n\n")

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

def emitnts(rules):
	"""emit burm_nts ragged array"""
	existing = {}
	i=0
	for r in rules:
		out = computents(r.rhs)
		if existing.get(out) is None:
			printf("static short %Pnts_%d[] = { %s0 };\n", i, out);
			existing[out] = (i)
			i += 1
	printf("\nshort *%Pnts[] = {\n");
	j=0
	for r in rules:
		while j < r.ern:
			printf("%10,%1/* %d */\n", j);
			j+=1
		printf("%1%Pnts_%d,%1/* %d */\n", existing[computents(r.rhs)] , j);
		j+=1
	printf("};\n\n");

def emitterms(terms):
	"""emit terminal data structures"""
	printf("char %Parity[] = {\n");
	j=0
	for p in terms:
		while j < p.esn:
			printf("%10,%1/* %d */\n", j);
			j+=1
		if p.arity < 0:
			printf("%1%d,%1/* %d=%S */\n", 0 ,j , p)
		else:
			printf("%1%d,%1/* %d=%S */\n", p.arity, j, p)
		j+=1
	printf("};\n\n");
	if Iflag:
		printf("char *%Popname[] = {\n");
		j=0
		for p in terms:
			while j < p.esn:
				printf("%1/* %d */%10,\n", j)
				j+=1
			printf("%1/* %d */%1\"%S\",\n", j, p)
			j+=1
		printf("};\n\n");
	

def emitstring(rules):
	"""emit array of rules and costs"""

	printf("short %Pcost[][4] = {\n");
	j=0
	for r in rules:
		while j < r.ern:
			printf("%1{ 0 },%1/* %d */\n", j)
			j+=1
		printf("%1{ %d },%1/* %d = %R */\n", r.cost, j, r)
		j+=1
	printf("};\n\nchar *%Pstring[] = {\n")
	j=0
	for r in rules:
		while j < r.ern:
			printf("%1/* %d */%10,\n", j)
			j+=1
		printf("%1/* %d */%1\"%R\",\n", j, r)
		j+=1

	printf("};\n\n")

def emitrule(nts):
	"""emit decoding vectors and burm_rule"""
	for p in nts:
		printf("static short %Pdecode_%S[] = {\n%10,\n", p)
		for r in p.rules:
			printf("%1%d,\n", r.ern)
		printf("};\n\n")
	printf("int %Prule(STATE_TYPE state, int goalnt) {\n"
"%1%Passert(goalnt >= 1 && goalnt <= %d, PANIC(\"Bad goal nonterminal %%d in %Prule\\n\", goalnt));\n"
"%1if (!state)\n%2return 0;\n%1switch (goalnt) {\n", globals.ntnumber);
	for p in nts:
		printf("%1case %P%S_NT:"
"%1return %Pdecode_%S[((struct %Pstate *)state)->rule.%P%S];\n", p, p, p);
	printf("%1default:\n%2%Passert(0, PANIC(\"Bad goal nonterminal %%d in %Prule\\n\", goalnt));\n%1}\n%1return 0;\n}\n\n");

def emitrecord(prefix, r, cost):
	"""emit code that tests for a winning match of rule r"""
	printf("%sif (", prefix);
	
	if Tflag: printf("%Ptrace(%Pnp, %d, c + %d, p->cost[%P%S_NT]), ",r.ern, cost, r.lhs);
	
	printf("c + %d < p->cost[%P%S_NT]) {\n%s%1p->cost[%P%S_NT] = c + %d;\n%s%1p->rule.%P%S = %d;\n",
		cost, r.lhs, prefix, r.lhs, cost, prefix, r.lhs,r.packed);
	
	if len(r.lhs.chain):printf("%s%1%Pclosure_%S(p, c + %d);\n", prefix, r.lhs, cost);
	
	printf("%s}\n", prefix);


def emitclosure(nts):
	"""emit the closure functions"""
	for p in nts:
		if len(p.chain):
			printf("static void %Pclosure_%S(struct %Pstate *, int);\n", p);
	printf("\n")
	for p in nts:
		if len(p.chain):
			printf("static void %Pclosure_%S(struct %Pstate *p, int c) {\n", p);
			for r in p.chain:
				emitrecord("\t", r, r.cost)
			printf("}\n\n")
	printf("\n")


def emittest(t, v, suffix, hasParent=False):
	"""emit clause for testing a match"""
	if t is None:
		print("Internal Error, Empty Tree Passed to emittest\n")
		return

	p = t.op
	if p.kind == TERM:
		if hasParent: printf("%3 && %s->op == %d%s/* %S */\n", v, p.esn,suffix, p);
		else: printf("%3%s->op == %d%s/* %S */\n", v, p.esn,suffix, p);
		if t.left: emittest(t.left,"%s->left"%v, suffix, True);
		if t.right: emittest(t.right,"%s->right"%v, suffix, True);


def emitcase(p):
	"""emit one case in function state"""
	if p.kind==NONTERM:
		print("Internal Error: emitcase being called for a non terminal %s"%p.name)
		return
	
	printf("%1case %d: /* %S */\n", p.esn, p)
	if p.arity == 0 or p.arity == -1: pass
	elif p.arity==1: printf("%2assert(l);\n")
	elif p.arity==2: printf("%2assert(l && r);\n")
	else: printf("Arity exeeds for %S",p)

	for r in reversed(p.rules):
		if r.rhs.nterms <= 1:
			printf("%2{%1/* %R */\n%3c = ", r);
		else:
			printf("%2if (%1/* %R */\n", r);
			if r.rhs.left: emittest(r.rhs.left, "l", " ");
			if r.rhs.right: emittest(r.rhs.right, "r", " ");
			printf("%2) {\n%3c = ");
		if r.rhs.left: emitcost(r.rhs.left,  "l");
		if r.rhs.right: emitcost(r.rhs.right,  "r");
		printf("%d;\n", r.cost);
		emitrecord("\t\t\t", r, 0);
		printf("%2}\n");
	printf("%2break;\n");


def emitcost(t, v):
	"""emit cost computation for tree t"""
	p = t.op
	if p.kind == TERM:
		if t.left:
			emitcost(t.left, "%s->left" %  v)
		if t.right:
			emitcost(t.right, "%s->right" % v)
	else:
		printf("%s->cost[%P%S_NT] + ", v, p)


def emitstate(terms, start, ntnumber):
	"""emit state function"""
	printf("STATE_TYPE %Pstate(int op, STATE_TYPE left, STATE_TYPE right) {\n%1int c;\n"
"%1struct %Pstate *p, *l = (struct %Pstate *)left,\n"
"%2*r = (struct %Pstate *)right;\n\n%1assert(sizeof (STATE_TYPE) >= sizeof (void *));\n%1");
	printf("{\n%2p = ALLOC(sizeof *p);\n"
"%2%Passert(p, PANIC(\"ALLOC returned NULL in %Pstate\\n\"));\n"
"%2p->op = op;\n%2p->left = l;\n%2p->right = r;\n%2p->rule.%P%S = 0;\n", start);
	for i in range(1,ntnumber+1):
		printf("%2p->cost[%d] =\n", i);
	printf("%3%d;\n%1}\n%1switch (op) {\n", maxcost);
	for p in terms:
		emitcase(p)
	printf("%1default:\n"
"%2%Passert(0, PANIC(\"Bad operator %%d in %Pstate\\n\", op));\n%1}\n"
"%1return (STATE_TYPE)p;\n}\n\n")


def emitlabel(start):
	"""emit the labelling functions"""
	printf("static void %Plabel1(NODEPTR_TYPE p) {\n"
"%1%Passert(p, PANIC(\"NULL tree in %Plabel\\n\"));\n"
"%1switch (%Parity[OP_LABEL(p)]) {\n"
"%1case 0:\n")
	if Tflag:
		printf("%2%Pnp = p;\n");
	printf("%2STATE_LABEL(p) = %Pstate(OP_LABEL(p), 0, 0);\n%2break;\n"
"%1case 1:\n%2%Plabel1(LEFT_CHILD(p));\n");
	if Tflag:
		printf("%2%Pnp = p;\n");
	printf("%2STATE_LABEL(p) = %Pstate(OP_LABEL(p),\n"
"%3STATE_LABEL(LEFT_CHILD(p)), 0);\n%2break;\n"
"%1case 2:\n%2%Plabel1(LEFT_CHILD(p));\n%2%Plabel1(RIGHT_CHILD(p));\n");
	if Tflag:
		printf("%2%Pnp = p;\n")
	printf("%2STATE_LABEL(p) = %Pstate(OP_LABEL(p),\n"
"%3STATE_LABEL(LEFT_CHILD(p)),\n%3STATE_LABEL(RIGHT_CHILD(p)));\n%2break;\n"
"%1}\n}\n\n")
	printf(
"STATE_TYPE %Plabel(NODEPTR_TYPE p) {\n%1%Plabel1(p);\n"
"%1return ((struct %Pstate *)STATE_LABEL(p))->rule.%P%S ? STATE_LABEL(p) : 0;\n"
"}\n\n", start)


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

def emitkids(rules):
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

	printf("NODEPTR_TYPE *%Pkids(NODEPTR_TYPE p, int eruleno, NODEPTR_TYPE kids[]) {\n"
"%1%Passert(p, PANIC(\"NULL tree in %Pkids\\n\"));\n"
"%1%Passert(kids, PANIC(\"NULL kids in %Pkids\\n\"));\n"
"%1switch (eruleno) {\n");
	for out,rulesList in existing.items():	
		for r in reversed(rulesList):
			printf("%1case %d: /* %R */\n", r.ern, r)
		printf("%s%2break;\n", out)
	printf("%1default:\n%2%Passert(0, PANIC(\"Bad external rule number %%d in %Pkids\\n\", eruleno));\n%1}\n%1return kids;\n}\n\n");


def emitfuncs():
	"""emit functions to access node fields"""
	printf("int %Pop_label(NODEPTR_TYPE p) {\n"
"%1%Passert(p, PANIC(\"NULL tree in %Pop_label\\n\"));\n"
"%1return OP_LABEL(p);\n}\n\n");
	printf("STATE_TYPE %Pstate_label(NODEPTR_TYPE p) {\n"
"%1%Passert(p, PANIC(\"NULL tree in %Pstate_label\\n\"));\n"
"%1return STATE_LABEL(p);\n}\n\n");
	printf("NODEPTR_TYPE %Pchild(NODEPTR_TYPE p, int index) {\n"
"%1%Passert(p, PANIC(\"NULL tree in %Pchild\\n\"));\n"
"%1switch (index) {\n%1case 0:%1return LEFT_CHILD(p);\n"
"%1case 1:%1return RIGHT_CHILD(p);\n%1}\n"
"%1%Passert(0, PANIC(\"Bad index %%d in %Pchild\\n\", index));\n%1return 0;\n}\n\n")


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


	printf("/* yyparse() - started */\n");
	yyparse()
	printf("/* yyparse() - ended */\n\n");

	def sortUsingesn(term):
		return term.esn
	def sortUsingntnumber(nt):
		return nt.number
	def sortUsingern(rule):
		return rule.ern
	terms.sort(key = sortUsingesn)
	nts.sort(key = sortUsingntnumber)
	rules.sort(key = sortUsingern)

	printf("/* ckreach check for start - started */\n");
	if globals.start:
		ckreach(globals.start)
	printf("/* ckreach check for start - ended */\n\n");

	# start is None if not global???
	# print(globals.start.name)

	printf("/* checking reach of all nts - started */\n");
	for p in nts:
		if not p.reached:
			printf("can't reach non-terminal `%s'\n", p.name);
	printf("/* checking reach of all nts - ended */\n\n");

	printf("/* emidheader() - started */\n");
	emitheader();
	printf("/* emitheader() - ended */\n\n");

	printf("/* emitdefs(nts, ntnumber) - started */\n");
	emitdefs(nts, globals.ntnumber);
	printf("/* emitdefs(nts, ntnumber) - ended */\n\n");

	printf("/* emitstruct(nts, ntnumber) - started */\n");
	emitstruct(nts, globals.ntnumber);
	printf("/* emitstruct(nts, ntnumber) - ended */\n\n");

	printf("/* emitnts(rules, nrules) - started */\n");
	emitnts(rules);
	printf("/* emitnts(rules, nrules) - ended */\n\n");

	printf("/* emitterms(terms) - started */\n");
	emitterms(terms);
	printf("/* emitterms(terms) - ended */\n\n");

	printf("/* emitstring(rules) - started */\n");
	if Iflag:
		emitstring(rules);
	printf("/* emitstring(rules) - ended */\n\n");

	printf("/* emitrule(nts) - started */\n");
	emitrule(nts);
	printf("/* emitrule(nts) - ended */\n\n");

	printf("/* emitclosure(nts) - started */\n");
	emitclosure(nts);
	printf("/* emitclosure(nts) - ended */\n\n");


	printf("/* emitstate(nts) - started */\n");
	if (globals.start):
		emitstate(terms, globals.start, globals.ntnumber);
	printf("/* emitstate(nts) - ended */\n\n");

	
	printf("#ifdef STATE_LABEL\n");
	printf("/* emitlabel(start) - started */\n");
	if (globals.start):
		emitlabel(globals.start);
	printf("/* emitlabel(start) - ended */\n\n");

	printf("/* emitkids(rules, nrules) - started */\n");
	emitkids(rules);
	printf("/* emitkids(rules, nrules) - ended */\n\n");
	
	printf("/* emitfuncs() - started */\n");
	emitfuncs();
	printf("/* emitfuncs(); - ended */\n\n");

	printf("#endif\n");


	printf("/* footer of the input file - started */\n");
	copyfooter()
	printf("/* footer of the input file - ended */\n\n");

	return errcnt > 0;

				
  
if __name__== "__main__":
	main()