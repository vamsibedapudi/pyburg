
import sys
import globals
from pyburg import *

tokens = ('TERMINAL', 'START', 'PPERCENT', 'INT', 'ID')
literals = "\n(),;=:"



t_START = r'%start'
t_PPERCENT = r'%%'
t_ignore = ' \f\t\r'

def t_TERMINAL(t):
	r'%term'
	return t

def t_NEWLINE(t):
	r'\n'
	t.type = '\n'
	globals.yylineno += 1
	t.lineno = globals.yylineno
	return t

def t_INT(t):
    r'\d+'
    try:
        t.value = int(t.value)
    except ValueError:
        print("Integer value too large %d", t.value)
        t.value = 0
    return t
def t_ID(t):
    r'[a-zA-Z_][a-zA-Z_0-9]*'
    return t
def t_error(t):
    print("Illegal character '%s'" % t.value[0])
    t.lexer.skip(1)


def p_spec1(p):
	"spec : decls PPERCENT rules"
	globals.yylineno = 0
	# print("Parsed successfully")

def p_spec2(p):
	"spec : decls"
	globals.yylineno = 0

def p_decls1(p):
	"decls : empty"

def p_decls2(p):
	"decls : decls decl"

def p_decl1(p):
	"decl : TERMINAL blist '\\n'"


def p_decl2(p):
	"decl : START lhs '\\n'"
	if (nonterm(p[2]).number != 1):
		yyerror("redeclaration of the start symbol");

def p_decl3(p):
	"decl : '\\n'"

def p_decl4(p):
	"decl : error '\\n'"
	globals.parser.errok()


def p_blist1(p):
	"blist : empty"

def p_blist2(p):
	"blist : blist ID '=' INT"
	term(p[2],p[4])
	# print("Terms:")
	# print(len(burg.terms))

def p_rules1(p):
	"rules : empty"

def p_rules2(p):
	"rules : rules lhs ':' tree '=' INT cost ';' '\\n'"
	rule(p[2], p[4],p[6], p[7])

def p_rules3(p):
	"rules : rules '\\n'"

def p_rules4(p):
	"rules : rules error '\\n'"
	globals.parser.errok()

def p_lhs(p):
	"lhs : ID"
	p[0] = p[1]
	nonterm(p[1])

def p_treelist1(p):
	"treelist : treelist ',' tree"
	p[0] = p[1]+ [p[3]]

def p_treelist2(p):
	"treelist : tree"
	p[0] = [p[1]]

def p_tree1(p):
	"tree : ID"
	p[0] = tree(p[1], [])

def p_tree2(p):
	"tree : ID '(' treelist ')'"
	p[0] = tree(p[1], p[3])

def p_cost1(p):
	"cost : empty"
	p[0] = 0

def p_cost2(p):
	"cost : '(' INT ')'"
	if (p[2] > maxcost):
		yyerror("%d exceeds maximum cost of %d\n", p[2], maxcost)
		p[0] = maxcost
	else:
		p[0] = p[2]

def p_empty(p):
    "empty :"
    pass

def p_error(t):
	if t:
		yyerror("Syntax error at '%s'" % t.value)
	else:
         yyerror("Syntax error at EOF")



# if __name__== "__main__":

# 	import ply.lex as lex
# 	import ply.yacc as yacc

# 	lexer = lex.lex()
# 	globals.parser = yacc.yacc()

# 	f = open(sys.argv[1],'r')
# 	data = ""
# 	for line in f:
# 		data += line
# 	# print(data)
# 	# lexer.input(data)
# 	# while True:
# 	# 	tok = lexer.token()
# 	# 	if not tok:
# 	# 		break
# 	# 	print(tok)
# 	globals.parser.parse(data)