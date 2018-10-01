
try:
	MAX_COST # exists
except NameError:
	MAX_COST = 1e16

try :
	trace
except NameError:
	def trace(p, rule, cost, bestcost):
		sys.stdout.write("%s matched %s with cost %d vs. %d\n" % (p,rule.name, cost, bestcost))

MAX_NT = 4

stm_NT = 0
#..........

nts nts[stm_NT] and terms =>term[esn] 

rule  [ern]
string, lhs,rhs,nt groups



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
	assert p, "Bad Node argument tree in kids\n"
	if ruleno is None: assert 0, "No rulenumber associated with rule"

	elif(
		ruleno == 4 # reg: PLUS(MEM(loc),reg)\
		or ruleno == 1 # stm: MOVE(MEM(loc),reg)
	):
		kids.append((p.getchild(0).getchild(0), rule.nts[0]))
		kids.append((p.getchild(1), rule.nts[1]))

	else: assert 0, "Bad external rule number %d in getmatchedkids\n"%ruleno
	return kids




def Rule:
	def __init__(self,string,lhs,rhs,nts,cost):
		self.string = ""
		self.lhs = lhs # ntnumber of lhs
		self.rhs = rhs # string of rhs
		self.nts = nts # all nts in rhs
		self.cost = cost # cost of the rule


class Node:

	def __init__(self):
		self.value = None # esn
		self.children = [] #child nodes
		self.cost = [ MAX_COST for i in range(MAX_NT)]
		self.rule = [ -1 for i in range(MAX_NT)]

	def label(self):
		for child in self.children:
			assert child, "Bad Child for Node %d in tree\n" % self.value
			child.label()
		self.match()


	def closure_reg(self, c):
		burm_trace(p, 7, c + 0, p.cost[burm_loc_NT])
		if (c + 0 < self.cost[burm_loc_NT]): #loc: reg
			p.cost[burm_loc_NT] = c + 0;
			p.rule[burm_loc_NT] = 7;



	def match(self):

		if self.value is None: assert 0, "No value in node"

		elif self.value == 1: # MOVE /
			assert len(self.children) == 2, " Invalid arity supplied to %d"%self.value

			l = self.getchild(0)
			assert l, "Left Child is None for %d"%self.value

			r = self.getchild(1)
			assert r, "Right Child is None for %d"%self.value

			if (	# reg: PLUS(PLUS(con,reg),reg)
				l.value == 3 # PLUS
			):
				c = l.left.cost[burm_con_NT] + l.right.cost[burm_reg_NT] + r.cost[burm_reg_NT] + 3;
				burm_trace(self, 2, c + 0, self.cost[burm_reg_NT])
				if (c + 0 < self.cost[burm_reg_NT]): # reg: PLUS(PLUS(con,reg),reg)
					self.cost[burm_reg_NT] = c + 0;
					self.rule[burm_reg_NT] = 2;
					self.burm_closure_reg(c + 0);


	case 2: / MEM /
		assert(l);
		{	/ reg: MEM(loc) /
			c = l->cost[burm_loc_NT] + 4;
			if (burm_trace(burm_np, 5, c + 0, p->cost[burm_reg_NT]), c + 0 < p->cost[burm_reg_NT]) {
				p->cost[burm_reg_NT] = c + 0;
				p->rule.burm_reg = 4;
				p.closure_reg(c + 0);
			}
		}
		break;
	case 3: / PLUS /
		assert(l && r);
		if (	/ loc: PLUS(NAME,reg) /
			l->op == 4 / NAME /
		) {
			c = r->cost[burm_reg_NT] + 0;
			if (burm_trace(burm_np, 9, c + 0, p->cost[burm_loc_NT]), c + 0 < p->cost[burm_loc_NT]) {
				p.cost[burm_loc_NT] = c + 0;
				p.rule = 11;
			}
		}
		if (	/ reg: PLUS(MEM(loc),reg) /
			l->op == 2 / MEM /
		) {
			c = l->left->cost[burm_loc_NT] + r->cost[burm_reg_NT] + 4;
			if (burm_trace(burm_np, 4, c + 0, p->cost[burm_reg_NT]), c + 0 < p->cost[burm_reg_NT]) {
				p->cost[burm_reg_NT] = c + 0;
				p->rule.burm_reg = 3;
				burm_closure_reg(p, c + 0);
			}
		}
		{	/ reg: PLUS(reg,reg) /
			c = l->cost[burm_reg_NT] + r->cost[burm_reg_NT] + 2;
			if (burm_trace(burm_np, 3, c + 0, p->cost[burm_reg_NT]), c + 0 < p->cost[burm_reg_NT]) {
				p->cost[burm_reg_NT] = c + 0;
				p->rule.burm_reg = 2;
				burm_closure_reg(p, c + 0);
			}
		}
		{	/ reg: PLUS(con,reg) /
			c = l->cost[burm_con_NT] + r->cost[burm_reg_NT] + 3;
			if (burm_trace(burm_np, 2, c + 0, p->cost[burm_reg_NT]), c + 0 < p->cost[burm_reg_NT]) {
				p->cost[burm_reg_NT] = c + 0;
				p->rule.burm_reg = 1;
				burm_closure_reg(p, c + 0);
			}
		}
		break;
	case 4: / NAME /
		{	/ loc: NAME /
			c = 0;
			if (burm_trace(burm_np, 8, c + 0, p->cost[burm_loc_NT]), c + 0 < p->cost[burm_loc_NT]) {
				p->cost[burm_loc_NT] = c + 0;
				p->rule.burm_loc = 2;
			}
		}
		break;
	case 6: / CONST /
		{	/ con: CONST */
			c = 0;
			if (burm_trace(burm_np, 10, c + 0, p->cost[burm_con_NT]), c + 0 < p->cost[burm_con_NT]) {
				p->cost[burm_con_NT] = c + 0;
				p->rule.burm_con = 1;
				burm_closure_con(p, c + 0);
			}
		}
		break;
	else: assert 0, "Bad operator %d in burm_state\n" % self.value:


"""initializes tree required for labelling from user defined ast tree
user defined ast tree class must contain functions getValue()and getChildren() which return 
	value of the root of the tree and the list of children trees respectively"""
def initializeNode(P):
	node = Node(P.getValue())
	for child in P.getChildren():
		node.children.append(initialize(child))
	return node
