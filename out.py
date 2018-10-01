try:
	MAX_COST # exists
except NameError:
	MAX_COST = 1e16

try :
	trace
except NameError:
	def trace(p, rule, cost, bestcost):
		sys.stdout.write("%s matched %s with cost %d vs. %d\n" % (p,rule.name, cost, bestcost))

prefix_MAX_NT = 4;

prefix_stm_NT = 0
prefix_loc_NT = 1
prefix_reg_NT = 2
prefix_con_NT = 3

prefix_nts = {

	0 : "stm",
	1 : "loc",
	2 : "reg",
	3 : "con",
}


prefix_terms = {

	1 : "MOVE",
	2 : "MEM",
	3 : "PLUS",
	4 : "NAME",
	6 : "CONST",
}

class Rule:
	def __init__(self, value, lhs, rhs, nts, cost):
		self.value = value # entire rule as a string in its original format
		self.lhs = lhs # ntnumber of lhs
		self.rhs = rhs # string of rhs
		self.nts = nts # all nts in rhs
		self.cost = cost # cost of the rule

prefix_rules = {

	1 : Rule("stm: MOVE(MEM(loc),reg)", 0, "MOVE(MEM(loc),reg)", [prefix_loc_NT, prefix_reg_NT, ] , 4),
	2 : Rule("reg: PLUS(PLUS(PLUS(con,reg),reg),PLUS(con,PLUS(con,reg)))", 2, "PLUS(PLUS(PLUS(con,reg),reg),PLUS(con,PLUS(con,reg)))", [prefix_con_NT, prefix_reg_NT, prefix_reg_NT, prefix_con_NT, prefix_con_NT, prefix_reg_NT, ] , 3),
	3 : Rule("reg: PLUS(reg,reg)", 2, "PLUS(reg,reg)", [prefix_reg_NT, prefix_reg_NT, ] , 2),
	4 : Rule("reg: PLUS(MEM(loc),reg)", 2, "PLUS(MEM(loc),reg)", [prefix_loc_NT, prefix_reg_NT, ] , 4),
	5 : Rule("reg: MEM(loc)", 2, "MEM(loc)", [prefix_loc_NT, ] , 4),
	6 : Rule("reg: con", 2, "con", [prefix_con_NT, ] , 2),
	7 : Rule("loc: reg", 1, "reg", [prefix_reg_NT, ] , 0),
	8 : Rule("loc: NAME", 1, "NAME", [] , 0),
	9 : Rule("loc: PLUS(NAME,reg)", 1, "PLUS(NAME,reg)", [prefix_reg_NT, ] , 0),
	10 : Rule("con: CONST", 3, "CONST", [] , 0),
}

# gives the best rule to apply for that non-terminal
def getrule(p, goalnt):
	assert goalnt in nts.keys(), "Bad goal nonterminal %d in getrule\n" % goalnt
	assert p, "Bad Node argument to getrule\n"
	ruleno = p.rule[goalnt];
	assert ruleno in rules.keys(), "Bad rule number %d for non-terminal %d in getrule\n" % (ruleno, goalnt)
	return rules[ruleno]

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
		if (cost + 0 < self.cost[prefix_loc_NT]): # loc: reg
			self.cost[prefix_loc_NT] = cost + 0;
			self.rule[prefix_loc_NT] = 7;

	def closure_con(self, cost): 
		if (cost + 2 < self.cost[prefix_reg_NT]): # reg: con
			self.cost[prefix_reg_NT] = cost + 2;
			self.rule[prefix_reg_NT] = 6;
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
				children[0].value == 2 # MEM
			):
				c = l.children[0].cost[prefix_loc_NT] + r.cost[prefix_reg_NT] + 4;
				if (cost + 0 < self.cost[prefix_stm_NT]): # stm: MOVE(MEM(loc),reg)
					self.cost[prefix_stm_NT] = cost + 0;
					self.rule[prefix_stm_NT] = 1;


		elif self.value == 2: # MEM

			assert len(self.children) == 1, " Invalid arity supplied to %d"%self.value
			l = self.children[0]
			assert l, "Left Child is None for %d"%self.value

			if (	# reg: MEM(loc)
				True # No checks for any terminal
			):
				c = l.cost[prefix_loc_NT] + 4;
				if (cost + 0 < self.cost[prefix_reg_NT]): # reg: MEM(loc)
					self.cost[prefix_reg_NT] = cost + 0;
					self.rule[prefix_reg_NT] = 5;
					self.closure_reg(cost + 0);


		elif self.value == 3: # PLUS

			assert len(self.children) == 2, " Invalid arity supplied to %d"%self.value
			l = self.children[0]
			assert l, "Left Child is None for %d"%self.value
			r = self.children[1]
			assert r, "Right Child is None for %d"%self.value

			if (	# loc: PLUS(NAME,reg)
				children[0].value == 4 # NAME
			):
				c = r.cost[prefix_reg_NT] + 0;
				if (cost + 0 < self.cost[prefix_loc_NT]): # loc: PLUS(NAME,reg)
					self.cost[prefix_loc_NT] = cost + 0;
					self.rule[prefix_loc_NT] = 9;

			if (	# reg: PLUS(MEM(loc),reg)
				children[0].value == 2 # MEM
			):
				c = l.children[0].cost[prefix_loc_NT] + r.cost[prefix_reg_NT] + 4;
				if (cost + 0 < self.cost[prefix_reg_NT]): # reg: PLUS(MEM(loc),reg)
					self.cost[prefix_reg_NT] = cost + 0;
					self.rule[prefix_reg_NT] = 4;
					self.closure_reg(cost + 0);

			if (	# reg: PLUS(reg,reg)
				True # No checks for any terminal
			):
				c = l.cost[prefix_reg_NT] + r.cost[prefix_reg_NT] + 2;
				if (cost + 0 < self.cost[prefix_reg_NT]): # reg: PLUS(reg,reg)
					self.cost[prefix_reg_NT] = cost + 0;
					self.rule[prefix_reg_NT] = 3;
					self.closure_reg(cost + 0);

			if (	# reg: PLUS(PLUS(PLUS(con,reg),reg),PLUS(con,PLUS(con,reg)))
				children[0].value == 3 # PLUS
				 and children[0].children[0].value == 3 # PLUS
				children[1].value == 3 # PLUS
				 and children[1].children[1].value == 3 # PLUS
			):
				c = l.children[0].children[0].cost[prefix_con_NT] + l.children[0].children[0].cost[prefix_reg_NT] + l.children[0].cost[prefix_reg_NT] + r.children[0].cost[prefix_con_NT] + r.children[0].children[0].cost[prefix_con_NT] + r.children[0].children[0].cost[prefix_reg_NT] + 3;
				if (cost + 0 < self.cost[prefix_reg_NT]): # reg: PLUS(PLUS(PLUS(con,reg),reg),PLUS(con,PLUS(con,reg)))
					self.cost[prefix_reg_NT] = cost + 0;
					self.rule[prefix_reg_NT] = 2;
					self.closure_reg(cost + 0);


		elif self.value == 4: # NAME

			assert len(self.children) == 0, " Invalid arity supplied to %d"%self.value

			if (	# loc: NAME
				True # No checks for any terminal
			):
				c = 0;
				if (cost + 0 < self.cost[prefix_loc_NT]): # loc: NAME
					self.cost[prefix_loc_NT] = cost + 0;
					self.rule[prefix_loc_NT] = 8;


		elif self.value == 6: # CONST

			assert len(self.children) == 0, " Invalid arity supplied to %d"%self.value

			if (	# con: CONST
				True # No checks for any terminal
			):
				c = 0;
				if (cost + 0 < self.cost[prefix_con_NT]): # con: CONST
					self.cost[prefix_con_NT] = cost + 0;
					self.rule[prefix_con_NT] = 10;
					self.closure_con(cost + 0);

		else: assert 0, "Bad operator %d in match\n" % self.value

