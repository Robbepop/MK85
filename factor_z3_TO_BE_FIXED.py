#!/usr/bin/env python

import random
from z3 import *
from operator import mul

def factor(n):
    print "factoring",n

    s=Solver()

    #TODO in1,in2,out=Bitvecs('in1 in2 out', 64)
    # TODO: 64-bit
    in1=BitVec('in1', 32)
    in2=BitVec('in2', 32)
    out=BitVec('out', 32)

    s.add(out==n)
    s.add(BVMulNoOverflow(in1, in2)==out)
    # inputs cannot be negative and must be non-1:
    s.add(in1>1)
    s.add(in2>1)

    if s.check()==unsat:
        print n,"is prime (unsat)"
        return [n]

    m=s.model()
    # get inputs of multiplier:
    in1_n=m["in1"]
    in2_n=m["in2"]

    print "factors of", n, "are", in1_n, "and", in2_n
    # factor factors recursively:
    rt=sorted(factor (in1_n) + factor (in2_n))
    # self-test:
    assert reduce(mul, rt, 1)==n
    return rt

# infinite test:
def test():
    while True:
        print factor (random.randrange(1000000000))

#test()

print factor(1234567890)

