# SAT PY

Instance: A Boolean formula $\phi$ in CNF.

Question: Is $\phi$ satisfiable?
 
**Note: This problem is NP-complete (If any NP-complete can be solved in polynomial time, then $P = NP$)**.

- This project is mathematically supported by the same author on paper [SAT is as hard as solving Homogeneous Diophantine Equation of Degree Two](https://www.researchgate.net/publication/369013369_SAT_is_as_hard_as_solving_Homogeneous_Diophantine_Equation_of_Degree_Two)

# Theory

- A literal in a Boolean formula is an occurrence of a variable or its negation. A Boolean formula is in conjunctive normal form, or CNF, if it is expressed as an AND of clauses, each of which is the OR of one or more literals.

- A truth assignment for a Boolean formula $\phi$ is a set of values for the variables in $\phi$. A satisfying truth assignment is a truth assignment that causes $\phi$ to be evaluated as true. A Boolean formula with a satisfying truth assignment is satisfiable. The problem SAT asks whether a given Boolean formula $\phi$ in CNF is satisfiable.

Example
----- 

Instance: The Boolean formula $(x_{1} \vee \rightharpoondown x_{3} \vee \rightharpoondown x_{2}) \wedge (x_{3} \vee x_{2} \vee x_{4})$ where $\vee$ (OR), $\wedge$ (AND) and $\rightharpoondown$ (NEGATION) are the logic operations.

Answer: Satisfiable (the formula is satisfiable since we can assign simultaneously the variables $x_{1}$ and $x_{3}$ as true to obtain a satisfying truth assignment).

Input of this project
-----

The input is on [DIMACS](http://www.satcompetition.org/2009/format-benchmarks2009.html) formula with the extension .cnf.
  
Let's take as the **file.cnf** from our previous example: The Boolean formula $(x_{1} \vee \rightharpoondown x_{3} \vee \rightharpoondown x_{2}) \wedge (x_{3} \vee x_{2} \vee x_{4})$ is
```  
p cnf 4 2
1 -3 -2 0
3 2 4 0
```  

- The first line **p cnf 4 2** means there are 4 variables and 2 clauses.

- The second line **1 -3 -2 0** means the clause $(x_{1} \vee \rightharpoondown x_{3} \vee \rightharpoondown x_{2})$ (Note that, the number *0* means the end of the clause).

- The third line **3 2 4 0** means the clause $(x_{3} \vee x_{2} \vee x_{4})$ (Note that, the number *0* means the end of the clause).

# Compile and Environment

Downloading and Installing
-----

Install at least Python 2.7 or a greater version 

Download and Install the following Number Theory Library 

- Z3 is a theorem prover from Microsoft Research with support for bitvectors, booleans, arrays, floating point numbers, strings, and other data types.

If you use pip, you can install Z3 with:
-----
```
pip install z3-solver
```

-----

# Build and Execute

To build and run from the command prompt:

```
git clone https://github.com/frankvegadelgado/sat-py.git
cd sat-py
```

On Windows within sat-py directory run

```
.\starexec_run_default.bat file.cnf
```

On Linux within sat-py directory run

```
chmod +x starexec_run_default.sh
./starexec_run_default.sh file.cnf
```

Finally, it would obtain in the console output:

```
s SATISFIABLE
v 1 2 3 4 0
```

# **SAT Benchmarks** 

We can run the DIMACS files with the extension .cnf in the simplest benchmarks folder:

```
>  .\starexec_run_default.bat .\bin\simplest\aim-50-1_6-yes1-1.cnf
s SATISFIABLE
v -1 2 3 -4 -5 -6 7 8 9 -10 -11 -12 -13 14 -15 -16 17 18 19 20 21 22 23 24 -25 26 27 28 -29 30 31 -32 -33 -34 35 36 -37 38 39 40 41 42 43 -44 -45 46 -47 48 -49 -50 0
```

and

```
> .\starexec_run_default.bat .\bin\simplest\aim-50-1_6-no-1.cnf
s UNSATISFIABLE
```

- We run each script and output the solutions for the satisfiable formulas.

We obtain this result since those files were copied into the directory sat-py\bin\simplest:

```
aim-50-1_6-yes1-1.cnf
aim-50-1_6-no-1.cnf
```

from this well-known dataset [SAT Benchmarks](https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/DIMACS/AIM/descr.html). 

# Code

- Python code by **Frank Vega**.

# Complexity

````diff
+ This reduction runs in polynomial time: We reduce SAT to NAE 3SAT (This is a trivial and well-known polynomial time reduction).
- The whole algorithm is based on several quadratic homogeneous constraints which is feasible.
````
 

# License
- MIT.