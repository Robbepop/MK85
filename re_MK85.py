#!/usr/bin/env python
from MK85 import *

# https://yurichev.com/blog/regexp/

BIT_WIDTH=16

INVALID_STATE=999
ACCEPTING_STATES=[13, 19, 23, 24]

# st - state
# i - input character
def transition (s, st, i):
    # this is like switch()
    return s.If(And(st==0, i==ord('r')), s.BitVecConst(3, BIT_WIDTH),
    s.If(And(st==0, i==ord('b')), s.BitVecConst(4, BIT_WIDTH),
    s.If(And(st==0, i==ord('g')), s.BitVecConst(5, BIT_WIDTH),
    s.If(And(st==0, i==ord('d')), s.BitVecConst(1, BIT_WIDTH),
    s.If(And(st==0, i==ord('l')), s.BitVecConst(2, BIT_WIDTH),
    s.If(And(st==1, i==ord('a')), s.BitVecConst(6, BIT_WIDTH),
    s.If(And(st==2, i==ord('i')), s.BitVecConst(7, BIT_WIDTH),
    s.If(And(st==3, i==ord('e')), s.BitVecConst(8, BIT_WIDTH),
    s.If(And(st==4, i==ord('l')), s.BitVecConst(9, BIT_WIDTH),
    s.If(And(st==5, i==ord('r')), s.BitVecConst(10, BIT_WIDTH),
    s.If(And(st==6, i==ord('r')), s.BitVecConst(11, BIT_WIDTH),
    s.If(And(st==7, i==ord('g')), s.BitVecConst(12, BIT_WIDTH),
    s.If(And(st==8, i==ord('d')), s.BitVecConst(13, BIT_WIDTH),
    s.If(And(st==9, i==ord('u')), s.BitVecConst(14, BIT_WIDTH),
    s.If(And(st==10, i==ord('e')), s.BitVecConst(15, BIT_WIDTH),
    s.If(And(st==11, i==ord('k')), s.BitVecConst(16, BIT_WIDTH),
    s.If(And(st==12, i==ord('h')), s.BitVecConst(17, BIT_WIDTH),
    s.If(And(st==13, i==ord('i')), s.BitVecConst(18, BIT_WIDTH),
    s.If(And(st==14, i==ord('e')), s.BitVecConst(19, BIT_WIDTH),
    s.If(And(st==15, i==ord('e')), s.BitVecConst(20, BIT_WIDTH),
    s.If(And(st==16, i==ord('r')), s.BitVecConst(3, BIT_WIDTH),
    s.If(And(st==16, i==ord('b')), s.BitVecConst(4, BIT_WIDTH),
    s.If(And(st==16, i==ord('g')), s.BitVecConst(5, BIT_WIDTH),
    s.If(And(st==17, i==ord('t')), s.BitVecConst(21, BIT_WIDTH),
    s.If(And(st==18, i==ord('s')), s.BitVecConst(22, BIT_WIDTH),
    s.If(And(st==19, i==ord('i')), s.BitVecConst(18, BIT_WIDTH),
    s.If(And(st==20, i==ord('n')), s.BitVecConst(23, BIT_WIDTH),
    s.If(And(st==21, i==ord('r')), s.BitVecConst(3, BIT_WIDTH),
    s.If(And(st==21, i==ord('b')), s.BitVecConst(4, BIT_WIDTH),
    s.If(And(st==21, i==ord('g')), s.BitVecConst(5, BIT_WIDTH),
    s.If(And(st==22, i==ord('h')), s.BitVecConst(24, BIT_WIDTH),
    s.If(And(st==23, i==ord('i')), s.BitVecConst(18, BIT_WIDTH),
        s.BitVecConst(INVALID_STATE, 16)))))))))))))))))))))))))))))))))

def print_model(m, length, inputs):
    #print "length=", length
    tmp=""
    for i in range(length-1):
        tmp=tmp+chr(m["inputs_%d" % i])
    print tmp

def make_FSM(length):
    s=MK85(verbose=0)
    states=[s.BitVec('states_%d' % i,BIT_WIDTH) for i in range(length)]
    inputs=[s.BitVec('inputs_%d' % i,BIT_WIDTH) for i in range(length-1)]

    # initial state:
    s.add(states[0]==0)

    # the last state must be equal to one of the acceping states
    s.add(Or(*[states[length-1]==i for i in ACCEPTING_STATES]))

    # all states are in limits...
    for i in range(length):
        s.add(And(states[i]>=0, states[i]<=24))
        # redundant, though. however, we are not interesting in non-matched inputs, right?
        s.add(states[i]!=INVALID_STATE)

    # "insert" transition() functions between subsequent states
    for i in range(length-1):
        s.add(states[i+1] == transition(s, states[i], inputs[i]))

    # enumerate results:
    results=[]
    while s.check():
        m=s.model()
        #print m
        print_model(m, length, inputs)
        # add the current solution negated:
        tmp=[]
        for pair in m:
            tmp.append(s.var_by_name(pair) == m[pair])
        s.add(expr.Not(And(*tmp)))

for l in range(2,15):
    make_FSM(l)

"""
red
blue
green
redish
blueish
darkred
greenish
lightred
darkblue
darkgreen
lightblue
lightgreen
darkredish
lightredish
darkblueish
lightblueish
darkgreenish
lightgreenish
"""

