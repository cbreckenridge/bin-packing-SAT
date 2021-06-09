# A SAT solver for the orthogonal packing problem

## To run:
    pip install -r requirements.txt

    pysmt-install --z3

    python3 solver.py <filepath> <options>


You must specify a filepath to the problem instance. Examples can be found in the problems folder.

## Options:
-p : print the satisfying assignment if possible

-g : show matplotlib plot of solution graphs if possible 
