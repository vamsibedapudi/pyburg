import sys
try:
	MAX_COST # exists
except NameError:
	MAX_COST = 1e16

try :
	trace
except NameError:
	def trace(p, rule, cost, bestcost):
		sys.stdout.write("%s matched %s with cost %d vs. %d\n" % (p,rule.name, cost, bestcost))

MAX_NT = 4;

stm_NT = 0
loc_NT = 1
reg_NT = 2
con_NT = 3

nts = {

	0 : "stm",
	1 : "loc",
	2 : "reg",
	3 : "con",
}


terms = {

	1 : "MOVE",
	2 : "MEM",
	3 : "PLUS",
	4 : "NAME",
	6 : "CONST",
}

class Rule:
	def __init__(self, value, lhs, rhs, nts, number, cost):
		self.value = value # entire rule as a string in its original format
		self.lhs = lhs # ntnumber of lhs
		self.rhs = rhs # string of rhs
		self.nts = nts # all nts in rhs
		self.number = number # Rule number
		self.cost = cost # cost of the rule

rules = {

	1 : Rule("stm: MOVE(MEM(loc),reg)", 0, "MOVE(MEM(loc),reg)", [loc_NT, reg_NT, ] , 1, 4),
	2 : Rule("reg: PLUS(con,reg)", 2, "PLUS(con,reg)", [con_NT, reg_NT, ] , 2, 3),
	3 : Rule("reg: PLUS(reg,reg)", 2, "PLUS(reg,reg)", [reg_NT, reg_NT, ] , 3, 2),
	4 : Rule("reg: PLUS(MEM(loc),reg)", 2, "PLUS(MEM(loc),reg)", [loc_NT, reg_NT, ] , 4, 4),
	5 : Rule("reg: MEM(loc)", 2, "MEM(loc)", [loc_NT, ] , 5, 4),
	6 : Rule("reg: con", 2, "con", [con_NT, ] , 6, 2),
	7 : Rule("loc: reg", 1, "reg", [reg_NT, ] , 7, 0),
	8 : Rule("loc: NAME", 1, "NAME", [] , 8, 0),
	9 : Rule("loc: PLUS(NAME,reg)", 1, "PLUS(NAME,reg)", [reg_NT, ] , 9, 0),
	10 : Rule("con: CONST", 3, "CONST", [] , 10, 0),
}

class Node:

	def __init__(self):
		self.value = None # esn
		self.children = [] #child nodes
		self.cost = [ MAX_COST for i in range(MAX_NT)]
		self.rule = [ -1 for i in range(MAX_NT)]

	def label(self):
		for child in self.children:
			assert child, "Bad Child for Node %d in tree\n"% self.value
			child.label()
		self.match()

	def closure_reg(self, cost):
		if (cost + 0 < self.cost[loc_NT]): # loc: reg
			self.cost[loc_NT] = cost + 0;
			self.rule[loc_NT] = 7;

	def closure_con(self, cost):
		if (cost + 2 < self.cost[reg_NT]): # reg: con
			self.cost[reg_NT] = cost + 2;
			self.rule[reg_NT] = 6;
			self.closure_reg(cost + 2);


	def match(self):
		if self.value is None: assert 0, "No value in node\n"

		elif self.value == 1: # MOVE

			assert len(self.children) == 2, " Invalid arity supplied to %d"%self.value
			l = self.children[0]
			assert l, "Left Child is None for %d"%self.value
			r = self.children[1]
			assert r, "Right Child is None for %d"%self.value

			if (	# stm: MOVE(MEM(loc),reg)
					self.children[0].value == 2  # MEM
				):

				cost = l.children[0].cost[loc_NT] + r.cost[reg_NT] + 4;
				if (cost + 0 < self.cost[stm_NT]): # stm: MOVE(MEM(loc),reg)
					self.cost[stm_NT] = cost + 0;
					self.rule[stm_NT] = 1;


		elif self.value == 2: # MEM

			assert len(self.children) == 1, " Invalid arity supplied to %d"%self.value
			l = self.children[0]
			assert l, "Left Child is None for %d"%self.value

			if (	# reg: MEM(loc)
					True # No terminals
				):

				cost = l.cost[loc_NT] + 4;
				if (cost + 0 < self.cost[reg_NT]): # reg: MEM(loc)
					self.cost[reg_NT] = cost + 0;
					self.rule[reg_NT] = 5;
					self.closure_reg(cost + 0);


		elif self.value == 3: # PLUS

			assert len(self.children) == 2, " Invalid arity supplied to %d"%self.value
			l = self.children[0]
			assert l, "Left Child is None for %d"%self.value
			r = self.children[1]
			assert r, "Right Child is None for %d"%self.value

			if (	# loc: PLUS(NAME,reg)
					self.children[0].value == 4  # NAME
				):

				cost = r.cost[reg_NT] + 0;
				if (cost + 0 < self.cost[loc_NT]): # loc: PLUS(NAME,reg)
					self.cost[loc_NT] = cost + 0;
					self.rule[loc_NT] = 9;

			if (	# reg: PLUS(MEM(loc),reg)
					self.children[0].value == 2  # MEM
				):

				cost = l.children[0].cost[loc_NT] + r.cost[reg_NT] + 4;
				if (cost + 0 < self.cost[reg_NT]): # reg: PLUS(MEM(loc),reg)
					self.cost[reg_NT] = cost + 0;
					self.rule[reg_NT] = 4;
					self.closure_reg(cost + 0);

			if (	# reg: PLUS(reg,reg)
					True # No terminals
				):

				cost = l.cost[reg_NT] + r.cost[reg_NT] + 2;
				if (cost + 0 < self.cost[reg_NT]): # reg: PLUS(reg,reg)
					self.cost[reg_NT] = cost + 0;
					self.rule[reg_NT] = 3;
					self.closure_reg(cost + 0);

			if (	# reg: PLUS(con,reg)
					True # No terminals
				):

				cost = l.cost[con_NT] + r.cost[reg_NT] + 3;
				if (cost + 0 < self.cost[reg_NT]): # reg: PLUS(con,reg)
					self.cost[reg_NT] = cost + 0;
					self.rule[reg_NT] = 2;
					self.closure_reg(cost + 0);


		elif self.value == 4: # NAME

			assert len(self.children) == 0, " Invalid arity supplied to %d"%self.value

			if (	# loc: NAME
					True # No terminals
				):

				cost = 0;
				if (cost + 0 < self.cost[loc_NT]): # loc: NAME
					self.cost[loc_NT] = cost + 0;
					self.rule[loc_NT] = 8;


		elif self.value == 6: # CONST

			assert len(self.children) == 0, " Invalid arity supplied to %d"%self.value

			if (	# con: CONST
					True # No terminals
				):

				cost = 0;
				if (cost + 0 < self.cost[con_NT]): # con: CONST
					self.cost[con_NT] = cost + 0;
					self.rule[con_NT] = 10;
					self.closure_con(cost + 0);

		else: assert 0, "Bad operator %d in match\n" % self.value

# gives the best rule to apply for that non-terminal
def getrule(p, goalnt):
	assert goalnt in nts.keys(), "Bad goal nonterminal %d in getrule\n" % goalnt
	assert p, "Bad Node argument to getrule\n"
	ruleno = p.rule[goalnt];
	assert ruleno in rules.keys(), "Bad rule number %d for non-terminal %d in getrule\n" % (ruleno, goalnt)
	return rules[ruleno]

#  returns nodes to be matched and the non-terminals to which they must be  further to matched based on the rule applied to the current node
def getmatchedkids(p, rule):

	kids = []
	ruleno = rule.number
	assert p, "Bad Node argument tree in kids\n";

	if ruleno is None: assert 0, "No rulenumber associated with rule\n"

	elif(
			ruleno == 8 or # loc: NAME
			ruleno == 10 # con: CONST
		):

		pass

	elif(
			ruleno == 9 # loc: PLUS(NAME,reg)
		):

		kids.append((p.children[1], rule.nts[0]));

	elif(
			ruleno == 2 or # reg: PLUS(con,reg)
			ruleno == 3 # reg: PLUS(reg,reg)
		):

		kids.append((p.children[0], rule.nts[0]));
		kids.append((p.children[1], rule.nts[1]));

	elif(
			ruleno == 5 # reg: MEM(loc)
		):

		kids.append((p.children[0], rule.nts[0]));

	elif(
			ruleno == 1 or # stm: MOVE(MEM(loc),reg)
			ruleno == 4 # reg: PLUS(MEM(loc),reg)
		):

		kids.append((p.children[0].children[0], rule.nts[0]));
		kids.append((p.children[1], rule.nts[1]));

	elif(
			ruleno == 6 or # reg: con
			ruleno == 7 # loc: reg
		):

		kids.append((p, rule.nts[0]));

	else: assert 0, "Bad external rule number %d in getmatchedkids\n"%ruleno

	return kids



MOVE=1
MEM=2
PLUS=3
NAME=4
CONST=6

"""initializes tree required for labelling from user defined ast tree
user defined ast tree class must contain functions getValue()and getChildren() which return
    value of the root of the tree and the list of children trees respectively"""
def initializeNode(P):
    node = Node(P.getValue())
    for child in P.getChildren():
        node.children.append(initialize(child))
    return node


def dumpcover(p, goalnt, indent):
    rule = getrule(p, goalnt)
    sys.stdout.write("\t"*indent)
    sys.stdout.write("%s\n"% rule.value)

    for kid, nt in getmatchedkids(p, rule):
        dumpcover(kid, nt, indent + 1)


def tree(value, l=None, r=None):
    p = Node()
    p.value = value
    if l: p.children.append(l)
    if r: p.children.append(r)
    return p


def main():
    p = tree(MOVE,
        tree(MEM, tree(NAME, 0, 0), 0),
        tree(PLUS,
            tree(MEM, tree(PLUS,
                tree(NAME, 0, 0),
                tree(MEM, tree(NAME, 0, 0), 0)), 0),
            tree(CONST, 0, 0) ) );
    p.label()
    dumpcover(p, 0, 0)
    return 0;

if __name__== "__main__":
    main()

