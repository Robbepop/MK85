#!/usr/bin/env python

# see also: https://yurichev.com/blog/factor/

import random
from MK85 import *
from operator import mul

def factor(n):
    print "factoring",n

    s=MK85()

    #TODO in1,in2,out=Bitvecs('in1 in2 out', 64)
    # TODO: 64-bit
    in1=s.BitVec('in1', 32)
    in2=s.BitVec('in2', 32)
    out=s.BitVec('out', 32)

    s.add(out==n)
    s.add(s.BVMulNoOverflow(in1, in2)==out)
    # inputs cannot be negative and must be non-1:
    s.add(in1>1)
    s.add(in2>1)

    if s.check()==False:
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

"""
factoring 1234567890
factors of 1234567890 are 2 and 617283945
factoring 2
2 is prime (unsat)
factoring 617283945
factors of 617283945 are 57045 and 10821
factoring 57045
factors of 57045 are 11409 and 5
factoring 11409
factors of 11409 are 3803 and 3
factoring 3803
3803 is prime (unsat)
factoring 3
3 is prime (unsat)
factoring 5
5 is prime (unsat)
factoring 10821
factors of 10821 are 3 and 3607
factoring 3
3 is prime (unsat)
factoring 3607
3607 is prime (unsat)
[2, 3, 3, 5, 3607, 3803]
"""

