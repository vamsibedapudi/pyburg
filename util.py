import globals

class Term:		# terminals:
	def __init__(self,name):
		self.name = name;		# terminal name
		self.kind = globals.TERM;		# TERM
		self.esn = None;			# external symbol number
		self.arity = None;		# operator arity
		self.rules = [];		# rules whose pattern starts with term

class Nonterm:	# non-terminals:
	def __init__(self,name):
		self.name = name;		# non-terminal name
		self.kind = globals.NONTERM;		# NONTERM
		self.number = None;		# identifying number
		# self.lhscount = 0;	# # times nt appears in a rule lhs
		self.reached = 0;		# 1 iff reached from start non-terminal
		self.rules = [];		# rules w/non-terminal on lhs
		self.chain = [];		# chain rules w/non-terminal on rhs

class Tree:			# tree patterns:
	def __init__(self):
		self.op = None;			# a terminal or non-terminal
		self.left = None;		# operands
		self.right = None;		# operands
		self.nterms = 0;		# number of terminal nodes in this tree

class Rule:		# rules:
	def __init__(self):
		self.lhs = None			# lefthand side non-terminal
		self.rhs = None		# rule pattern
		self.ern = None			# external rule number
		self.packed = None		# packed external rule number
		self.cost = None			# associated cost