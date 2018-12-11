This code implements the planning algorithm forward search with backward analysis.

To run the code
1) ./build.py
2) ./fast-downward.py domain.pddl problem.pddl --search "eager(single(ff()))" 

Note that this algorithm should only be tested for domains in Transition Normal Form. It's not gauranteed to work on domains not in TNF.
