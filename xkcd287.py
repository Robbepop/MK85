from MK85 import *

# https://www.xkcd.com/287/

s=MK85()
a=s.BitVec("a", 16)
b=s.BitVec("b", 16)
c=s.BitVec("c", 16)
d=s.BitVec("d", 16)
e=s.BitVec("e", 16)
f=s.BitVec("f", 16)

s.add(a<=10)
s.add(b<=10)
s.add(c<=10)
s.add(d<=10)
s.add(e<=10)
s.add(f<=10)

s.add(a*215 + b*275 + c*335 + d*355 + e*420 + f*580 == 1505)

while s.check():
    m=s.model()
    print m
    # block current solution and solve again:
    s.add(expr.Not(And(a==m["a"], b==m["b"], c==m["c"], d==m["d"], e==m["e"], f==m["f"])))

"""
% python xkcd287.py

{'a': 7, 'c': 0, 'b': 0, 'e': 0, 'd': 0, 'f': 0}
{'a': 1, 'c': 0, 'b': 0, 'e': 0, 'd': 2, 'f': 1}
"""
