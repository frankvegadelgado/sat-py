#Frank Vega
#March 13, 2023
#We show that SAT is as difficult as solving the Homogeneous Diophantine Equation of Degree Two.
#We transform this reduction to solve SAT instances.
#The whole algorithm is based on the problem of several quadratic constraints which is feasible when we do not restrict the variables to be integers.
#We use the Python programming language for making the whole reduction from SAT to NAE 3SAT. 
#Finally, we use Z3 that is a theorem prover from Microsoft Research.

import sys
sys.path.append("include")
import PyBool_public_interface as Bool
import z3

def maximum(clauses):
	return abs(max(list(set([max(t, key=abs) for t in clauses])), key=abs))
	
def vars(clauses):
	flat_list = [item for sublist in clauses for item in sublist]
	return list(set([abs(t) for t in flat_list]))
	
def pairwise(iterable):
	a = iter(iterable)
	return zip(a, a)
	
def sign(x, y):
	i = eval('%s' % x)
	j = eval('%s' % y)
	if i < j:
		return '-'
	else:
		return ''

def solve(dummy, clauses):
	s = z3.Solver()
	variables = vars(clauses)
	variables.sort()
	x = [ z3.Real('x%s' % i) for i in range(2 * len(variables)) ]
	for i in range(len(variables)):
		s.add(x[2*i] + x[2*i+1] - 2*x[2*i]*x[2*i+1] == 1.0)
	index = variables.index(dummy)
	s.add(x[2 * index] == 0.0, x[2 * index + 1] == 1.0)
	for list in clauses:
		a = 2 * variables.index(-list[0]) + 1 if (list[0] < 0) else 2 * variables.index(list[0])
		b = 2 * variables.index(-list[1]) + 1 if (list[1] < 0) else 2 * variables.index(list[1])
		c = 2 * variables.index(-list[2]) + 1 if (list[2] < 0) else 2 * variables.index(list[2])
		s.add(x[a]+x[b]+x[c]-x[a]*x[b]-x[b]*x[c]-x[a]*x[c] == 1.0)
	
	result = s.check()
	if result == z3.unsat:
		print('s UNSATISFIABLE')
	elif result == z3.unknown:
		print('s UNKNOWN')
	else:
		print('s SATISFIABLE')
		items = s.model()
		answer = (x for x in items.decls() if int(x.name().replace('x','')) < 2 * index)
		formatted = ' '.join((sign(items[x], items[y]) + str(variables[int(int(x.name().replace('x','')) / 2)])) for x, y in pairwise(sorted(answer, key=lambda x: int(x.name().replace('x','')))))
		print('v '+formatted+' 0')
                       

def reduction(dummy, clauses):
	reduced = []
	s = maximum(clauses) + 2
	for list in clauses:
		reduced.append([list[0], list[1], s])
		reduced.append([list[2], -s, dummy])
		s += 1
	variables = vars(reduced)
	for x in variables:
		reduced.append([x, -x, s])
		reduced.append([x, -x, -s])
	return reduced
	
def cnf3(dummy, clause):
	reduced = []
	s = dummy + 1
	for list in clauses:
		if len(list) == 1:
			reduced.append([list[0], dummy, dummy])
		elif len(list) == 2:
			reduced.append([list[0], list[1], dummy])
		elif len(list) == 3:
			reduced.append(list)
		else:
			if len(list) > 0:
				B = list
				while True:
					A = B[:2]
					B = B[2:]
					A.append(s)
					B.append(-s)
					s += 1
					reduced.append(A)
					if len(B) <= 3:
						break
				if len(B) > 0:
					if len(B) == 1:
						reduced.append([B[0], dummy, dummy])
					elif len(B) == 2:
						reduced.append([B[0], B[1], dummy])
					else:
						reduced.append(B)
	return reduced					
			
					   
if __name__ == "__main__":

	#Read and parse a dimacs file
	clauses = Bool.parse_dimacs(sys.argv[1])
	clauses = clauses["clauses"]
	dummy = maximum(clauses) + 1
	clauses = cnf3(dummy, clauses)
	clauses = reduction(dummy, clauses)
	solve(dummy, clauses)