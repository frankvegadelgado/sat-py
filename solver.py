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
	
class B:
	def __init__(self, start: z3.BitVecRef):
		self.value = start
	def __mul__(self, other):
		x = self.value
		y = other.value
		sz1 = x.sort().size()
		sz2 = y.sort().size()
		return B(z3.ZeroExt(sz2, x) * z3.ZeroExt(sz1, y))
	def __add__(self, other):
		x = self.value
		y = other.value
		sz1 = x.sort().size()
		sz2 = y.sort().size()
		rsz = max(sz1, sz2) + 1
		return B(z3.ZeroExt(rsz - sz1, x) + z3.ZeroExt(rsz - sz2, y))
	def __eq__(self, other):
		x = self.value
		y = other.value
		sz1 = x.sort().size()
		sz2 = y.sort().size()
		rsz = max(sz1, sz2)
		return z3.ZeroExt(rsz - sz1, x) == z3.ZeroExt(rsz - sz2, y)

def num_bits(n):
	assert(n >= 0)
	r = 0
	while n > 0:
		r = r + 1
		n = n / 2
	if r == 0:
		return 1
	return r
def val(x):
	return z3.BitVecVal(x, num_bits(x))		

def solve(dummy, clauses):
	s = z3.Solver()
	#s.set("timeout", 1800000)
	variables = vars(clauses)
	variables.sort()
	x = [ z3.BitVec('x%s' % i, 1) for i in range(2 * len(variables)) ]
	for i in range(len(variables)):
		s.add(B(x[2*i]) + B(x[2*i+1]) == B(val(1)) + B(val(2))*B(x[2*i])*B(x[2*i+1]))
	index = variables.index(dummy)
	s.add(B(x[2 * index]) == B(val(0)), B(x[2 * index + 1]) == B(val(1)))
	for list in clauses:
		a = 2 * variables.index(-list[0]) + 1 if (list[0] < 0) else 2 * variables.index(list[0])
		b = 2 * variables.index(-list[1]) + 1 if (list[1] < 0) else 2 * variables.index(list[1])
		c = 2 * variables.index(-list[2]) + 1 if (list[2] < 0) else 2 * variables.index(list[2])
		s.add(B(x[a])+B(x[b])+B(x[c]) == B(val(1)) + B(x[a])*B(x[b]) + B(x[a])*B(x[c]) + B(x[b])*B(x[c]))
	result = s.check()
	if result == z3.unsat:
		print("s UNSATISFIABLE")
		return []
	elif result == z3.unknown:
		print("s UNKNOWN")
		return []
	else:
		items = s.model()
		sol = []
		for i in range(len(variables)):
			if (i >= index):
				break
			else:	
				j = '%s' % items[x[2*i]]
				if j == '0':
					sol.append(-variables[i])
				else:
					sol.append(variables[i])
		return sol               

def reduction(dummy, clauses):
	reduced = []
	s = maximum(clauses) + 2
	for list in clauses:
		if list[0] == dummy or list[1] == dummy or list[2] == dummy:
			reduced.append(list)
		else:
			reduced.append([list[0], list[1], s])
			reduced.append([list[2], -s, dummy])
			s += 1
	return reduced
	
def cnf3(dummy, clauses):
	reduced = []
	s = dummy + 1
	for l in clauses:
		C = list(set(l))
		if len(C) == 1:
			reduced.append([C[0], dummy, dummy])
		elif len(C) == 2:
			reduced.append([C[0], C[1], dummy])
		elif len(C) == 3:
			reduced.append(C)
		else:
			if len(C) > 0:
				B = C
				while True:
					A = B[:2]
					B = B[2:]
					A.append(s)
					B.append(-s)
					s += 1
					reduced.append(A)
					if len(B) == 3:
						break
				reduced.append(B)
	return reduced					
			
					   
if __name__ == "__main__":

	#Read and parse a dimacs file
	formula = Bool.parse_dimacs(sys.argv[1])
	original = formula["clauses"]
	dummy = maximum(original) + 1
	cnf = cnf3(dummy, original)
	nae = reduction(dummy, cnf)
	solution = solve(dummy, nae)
	if len(solution) > 0:
		truth = True
		if len(sys.argv) > 2:
			print("Proof checking sat!")
			for list in original:
				truth = False
				for z in list:
					truth = z in solution
					if truth == True:
						break
				if truth == False:
					print("s UNSATISFIABLE")
					break
		if truth == True:
			print("s SATISFIABLE")
			print("v", end = " ")
			print(*solution, end = " ")
			print("0")
		
				
	