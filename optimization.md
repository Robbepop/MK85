# Combinatorial optimization

This is minimize/maximize commands in SMT-LIB.
See simple example on GCD: https://yurichev.com/blog/GCD/

It was surprisingly easy to add support of it to MK85.
First, we take MaxSAT/WBO solver [Open-WBO](http://sat.inesc-id.pt/open-wbo/).
It supports both hard and soft clauses.
Hard are clauses which are *must* be satisfied.
Soft are *should* be satisfied, but they are also weighted.
The task of MaxSAT solver is to find such an assignment for variables, so the sum of weights of soft clauses would be
*maximized*..

This is GCD example rewritten to SMT-LIB format: https://github.com/DennisYurichev/MK85/blob/master/examples/optimize/GCD_BV2.smt
We are going to find such an assignment, for which GCD variable will be as big as possible (that would not break *hard* constraints, of course).

Whenever my MK85 encounters "minimize/maximize" command, the following function is called:

```c
void create_min_max (struct expr* e, bool min_max)
{

	...

	struct SMT_var* v=generate(e);
	add_comment ("%s(min_max=%d) id=%s var=%d", __FUNCTION__, min_max, v->id, v->SAT_var);
	assert (v->type==TY_BITVEC);
	for (int i=0; i<v->width; i++)
	{
		if (min_max==false)
			add_soft_clause1(/* weight */ 1<<i, -(v->SAT_var+i)); // minimize
		else
			add_soft_clause1(/* weight */ 1<<i, v->SAT_var+i); // maximize
	};

	...
};
```

Lowest bit of variable to maximize receives weight 1.
Second bit receives weight 2.
Then 4, 8, 16, etc.
Hence, MaxSAT solver, in order to maximize weights of soft clauses, would maximize the binary variable as well!

What is in the WCNF (weighted CNF) file for the GCD example?

```
...

c create_min_max(min_max=1) id=GCD var=51
1 51 0
2 52 0
4 53 0
8 54 0
16 55 0
32 56 0
64 57 0
128 58 0
256 59 0
512 60 0
1024 61 0
2048 62 0
4096 63 0
8192 64 0
16384 65 0
32768 66 0
```

Weights from 1 to 32768 to be assigned to specific bits of GCD variable.

Minimization works just as the same, but all bits are inverted.

Now some practical examples MK85 can already solve:
[Assignment problem](https://github.com/DennisYurichev/MK85/blob/master/examples/optimize/assign_problem.smt),
[Finding minimum of function](https://github.com/DennisYurichev/MK85/blob/master/examples/optimize/1959_AHSME_Problem_8.smt),
[Minimizing cost](https://github.com/DennisYurichev/MK85/blob/master/examples/optimize/popsicles.smt).

More optimization examples from my blog, mostly using z3:
[Making smallest possible test suite using Z3](https://yurichev.com/blog/set_cover/),
[Coin flipping problem](https://yurichev.com/blog/coin_flip/),
[Cracking simple XOR cipher with Z3](https://yurichev.com/blog/XOR_Z3/).

