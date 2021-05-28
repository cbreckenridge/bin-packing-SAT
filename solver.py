# Main file for getting satisfiable assignment of bin packing instance
# Christine Breckenridge

from pysmt.shortcuts import Symbol, And, Or, Solver, Iff, Implies, Not

# Variables:
# e_i_x_y = true if edge x,y in G_i
# c_i_x_a = true if item x is in clique a
# p_i_x_y_a = true if items x & y are both in clique a
# u_i_a = true if clique a is not empty

# d = dimension
# n = # of cliques
# O = set of items
# S^i = set of all infeasible sets in dim i
# C = container

# Simple example for testing
x1 = (1,2)
x2 = (3,1)
x3 = (2,1)
O = (x1,x2,x3)
C = (4,6)
n = len(O)
d = len(x1)



def var_string(*vargs):
	"""Returns string representation of a variable"""
	vargs = [str(i) for i in vargs]
	if vargs[0] == "c":
		if len(vargs) == 4:
			return "_".join(vargs)
	elif vargs[0] == "e":
		if len(vargs) == 4:
			return "_".join(vargs)
	elif vargs[0] == "p":
		if len(vargs) == 5:
			return "_".join(vargs)
	elif vargs[0] == "u":
		if len(vargs) == 3:
			return "_".join(vargs)
	else:
		print(f"Error unknown var base: {vargs[0]}")
		raise ValueError
		return
	print(f"Incorrect # of args: {len(vargs)} for base {vargs[0]}")
	raise Exception

def var_symbol(*vargs):
	"""Gets the string represntation and returns a Symbol"""
	try:
		string_rep = var_string(*vargs)
		return Symbol(string_rep)
	except Exception as e:
		raise e

# Set 1: All objects are packed
# for x in O, 1 <= i <= d
# c_i_x_1 or ... or c_i_x_n

set_1 = []
for x_i in range(1,n+1):
	for i in range(1,d+1):
		set_1.append(Or([var_symbol("c",i,x_i,j) for j in range(1,n+1)]))

set_1 = And(set_1)
print(set_1)

# Set 2: Consecutive linear ordering
# for x in O, 1 <= i <= d, 1 <= a < b-1 < n
# (c_i_x_a and c_i_x_b) implies c_i_x_(a+1)

set_2 = []
for x_i in range(1,n+1):
	for i in range(1,d+1):
		for a in range(1,n):
			for b in range(a+2,n+1):
				set_2.append(Implies(And(var_symbol("c",i,x_i,a), var_symbol("c",i,x_i,b)),
										var_symbol("c",i,x_i,a+1)))
set_2 = And(set_2)
print(set_2)

# Set 3: No-overlap constraint
# for x,y in O
# !e_1_x_y or ... or !e_d_x_y

set_3 = []
for x_i in range(1,n+1):
	for y_i in range(1,n+1):
		if y_i != x_i:
			for i in range(1,d+1):
				set_3.append(Not(var_symbol("e",i,x_i,y_i)))
set_3 = Or(set_3)
print(set_3)

# Set 4: Stable set feasibility
# for 1 <= i <= d, N in S^i
# OR_(for all x,y in N) e_i_x_y
# Must generate all infeasible sets
S = []
for i in range(1,d+1):
	S.append([])
	for x_i,x in enumerate(O):
		for y_i,y in enumerate(O):
			if y_i != x_i and x[i-1] + y[i-1] > C[i-1]:
				S[i-1].append([x_i+1,y_i+1])
print(S)
set_4 = []
if S:
	for i in range(1,d+1):
		if S[i-1]:
			for N in S[i-1]:
				set_4.append(var_symbol("e",i,N[0],N[1]))
set_4 = Or(set_4)
print(set_4)



# Set 5: No empty cliques
# 1 <= i <= d, 1 <= a <= n
# (!c_i_1_a and ... and !c_i_n_a) implies (!c_i_1_(a+1) and ... and !c_i_n_(a+1))

set_5 = []
for i in range(1,d+1):
	for a in range(1,n):
		left = [Not(var_symbol("c",i,x_i,a)) for x_i in range(1,n+1)]
		right = [Not(var_symbol("c",i,x_i,a+1)) for x_i in range(1,n+1)]
		set_5.append(Implies(And(left),And(right)))
set_5 = And(set_5)
print(set_5)

# Set 6: Correlations between vars
# for x,y in O, 1 <= a <= n, 1 <= i <= d
# p_i_x_y_a iff (c_i_x_a and c_i_y_a) and (p_i_x_y_1 or ... or p_i_x_y_k) iff e_i_x_y
# TODO

# Combine formulas
# TODO

# Get sat assignment if possible
# TODO