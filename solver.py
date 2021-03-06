# Main file for getting satisfiable assignment of orthogonal packing instance
# Christine Breckenridge

import sys
from time import perf_counter
from pysmt.shortcuts import Symbol, And, Or, Solver, Iff, Implies, Not, get_model, get_formula_size
from itertools import combinations
import plot_graph

# Variables:
# e_i_x_y = true if edge x,y in G_i
# c_i_x_a = true if item x is in clique a
# p_i_x_y_a = true if items x & y are both in clique a

# d = dimension
# n = # of cliques
# O = set of items
# S^i = set of all infeasible sets in dim i
# C = container



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


def main(C,O,printing=False,graphing=False):

	n = len(O)
	d = len(O[0])

	print("Creating SAT formula...")
	start = perf_counter() # start timer

	# Set 1: All objects are packed
	# for x in O, 1 <= i <= d
	# c_i_x_1 or ... or c_i_x_n

	set_1 = []
	for x_i in range(1,n+1):
		for i in range(1,d+1):
			set_1.append(Or([var_symbol("c",i,x_i,j) for j in range(1,n+1)]))

	set_1 = And(set_1)

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

	# Set 3: No-overlap constraint
	# for x,y in O
	# !e_1_x_y or ... or !e_d_x_y

	set_3 = []
	pair = []
	for x_i in range(1,n+1):
		for y_i in range(x_i+1,n+1):
			for i in range(1,d+1):
				pair.append(Not(var_symbol("e",i,x_i,y_i)))
			set_3.append(Or(pair))
			pair = []
	set_3 = And(set_3)
	# print(set_3)

	# Set 4: Stable set feasibility
	# for 1 <= i <= d, N in S^i
	# OR_(for all x,y in N) e_i_x_y
	# Must generate all infeasible sets

	S = []
	item_indexes = set(range(1,n+1))
	for i in range(1,d+1):
		S.append([])
		for size in range(2,n+1):
			for N in combinations(item_indexes,size):
				if any(S_set and S_set.issubset(N) for S_set in S[i-1]): #already have min set
					continue
				elif sum(O[x-1][i-1] for x in N) > C[i-1]: #too big for container
					S[i-1].append(set(N))


	set_4 = []
	subset = []
	if S:
		for i in range(1,d+1):
			if S[i-1]:
				for N in S[i-1]:
					for x_i,y_i in combinations(N,2):
						if x_i < y_i:
							subset.append(var_symbol("e",i,x_i,y_i))
						else:
							subset.append(var_symbol("e",i,y_i,x_i))
					set_4.append(Or(subset))
					subset = []
	set_4 = And(set_4)


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

	# Combine formulas
	sat_formula = And([set_1,set_2,set_3,set_4,set_5])
	var_num = len(sat_formula.get_atoms())
	size = sat_formula.size()
	print(f"Number of variables: {var_num}")
	print(f"Size of formula: {size}")

	# Get sat assignment if possible
	
	model = get_model(sat_formula)
	end = perf_counter()
	print(f"Solved in {end-start} seconds")
	if model:
		print("Satisfying assignment found")
		if printing: print(model)
		if graphing: plot_graph.main(C,O,model)
	else:
	  	print("No solution found")
	print("____________________________")

if __name__ == '__main__':
	opts = [opt for opt in sys.argv[1:] if opt.startswith("-")]
	args = [arg for arg in sys.argv[1:] if not arg.startswith("-")]

	printing = False
	graphing = False

	if '-p' in opts:
		printing = True
	if '-g' in opts:
		graphing = True

	if len(args) >= 1:
		filepath = args[0]
		print("Reading file...")
		f = open(filepath,'r')

		lines = f.readlines()
		
		O = []
		n = 0

		for l in lines:
			if "N. OF ITEMS" in l:
				n = int(l.split()[0])
			elif "HBIN,WBIN" in l:
				C = tuple(int(w) for w in l.split()[:-1])
			elif "H(I),W(I),I=1,...,N" in l:
				O.append(tuple(int(w) for w in l.split()[:-1]))
			elif n and "RELATIVE AND ABSOLUTE N. OF INSTANCE" not in l:
				O.append(tuple(int(w) for w in l.split()))
			if n and len(O) == n:
				print(f"{n} items")
				print(f"Container size: {C}")
				print(f"Items: {O}")
				main(C,O,printing=printing,graphing=graphing)
				O = []
				n = 0
	else:
		print("Please specify filepath")