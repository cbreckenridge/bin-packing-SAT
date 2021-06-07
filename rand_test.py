# Random testing for solver
# Christine Breckenridge

import solver
from numpy.random import randint

def random_problem(size,dim):
	C = randint(1,100,size=dim)
	O = randint(1,50,size=(size,dim))
	return [C,O]

def main(size=20,dim=2,num=10):
	for i in range(num):
		C,O = random_problem(size,dim)
		solver.main(C,O,printing=False)

if __name__ == '__main__':
	main()