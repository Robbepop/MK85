#!/usr/bin/python

# see: https://yurichev.com/blog/spreadsheet/

"""
test file:

1	0	B0+B2		A0*B0*C0
123	10	12		11
667	A0+B1	(C1*A0)*122	A3+C2

result:

1	0	135	82041	
123	10	12	11	
667	11	1342	83383	

"""

from MK85 import *
import sys, re

# MS Excel or LibreOffice style.
# first top-left cell is A0, not A1
def coord_to_name(R, C):        
    return "ABCDEFGHIJKLMNOPQRSTUVWXYZ"[R]+str(C)

# open file and parse it as list of lists:
f=open(sys.argv[1],"r")
# filter(None, ...) to remove empty sublists:
ar=filter(None, [item.rstrip().split() for item in f.readlines()])
f.close()

WIDTH=len(ar[0])
HEIGHT=len(ar)

s=MK85()

# cells{} is a dictionary with keys like "A0", "B9", etc:
cells={}
for R in range(HEIGHT):
    for C in range(WIDTH):
        name=coord_to_name(R, C)
        cells[name]=s.BitVec(name, 32)

cur_R=0
cur_C=0

for row in ar:
    for c in row:
        # string like "A0+B2" becomes "cells["A0"]+cells["B2"]":
        c=re.sub(r'([A-Z]{1}[0-9]+)', r'cells["\1"]', c)
        st="cells[\"%s\"]==%s" % (coord_to_name(cur_R, cur_C), c)
        # evaluate string. Z3Py expression is constructed at this step:
        e=eval(st)
        # add constraint:
        s.add (e)
        cur_C=cur_C+1
    cur_R=cur_R+1
    cur_C=0

if s.check():
    m=s.model()
    for r in range(HEIGHT):
        for c in range(WIDTH):
            sys.stdout.write (str(m[coord_to_name(r, c)])+"\t")
        sys.stdout.write ("\n")


