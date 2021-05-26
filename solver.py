# Main file for getting satisfiable assignment of bin packing instance
# Christine Breckenridge

from pysmt.shortcuts import Symbol, And, Or, Solver, Iff, Implies

# Variables:
# e_i_x_y = true if edge x,y in G_i
# c_i_x_a = true if item x is in clique a
# p_i_x_y_a = true if items x & y are both in clique a
# u_i_a = true if clique a is not empty

# d = dimension
# n = # of cliques


# Set 1: All objects are packed
# for x in O, 1 <= i <= d
# c_i_x_1 or ... or c_i_x_n
# TODO

# Set 2: Consecutive linear ordering
# for x in O, 1 <= i <= d, 1 <= a < b-1 < n
# (c_i_x_a and c_i_x_b) implies c_i_x_(a+1)
# TODO

# Set 3: No-overlap constraint
# for x,y in O
# !e_1_x_y or ... or !e_d_x_y
# TODO

# Set 4: Stable set feasibility
# for 1 <= i <= d, N in S^i
# OR_(for all x,y in N) e_i_x_y
# TODO
# Must generate all infeasible sets

# Set 5: No empty cliques
# 1 <= i <= d, 1 <= a <= n
# (!c_i_1_a and ... and !c_i_n_a) implies (!c_i_1_(a+1) and ... and !c_i_n_(a+1))
# TODO

# Set 6: Correlations between vars
# for x,y in O, 1 <= a <= n, 1 <= i <= d
# p_i_x_y_a iff (c_i_x_a and c_i_y_a) and (p_i_x_y_1 or ... or p_i_x_y_k) iff e_i_x_y
# TODO

# Combine formulas
# TODO

# Get sat assignment if possible
# TODO