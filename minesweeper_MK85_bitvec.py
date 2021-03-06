#!/usr/bin/python

"""
See also: https://yurichev.com/blog/minesweeper/

Now MK85 is capable of solving this.
Thanks to picosat SAT solver, on small bitvector examples, its performance is comparable to Z3's.
Even more, sometimes it's slightly faster than Z3:

% time python minesweeper_MK85_bitvec.py
WIDTH= 9 HEIGHT= 9
row=1 col=3, unsat!
row=6 col=2, unsat!
row=6 col=3, unsat!
row=7 col=4, unsat!
row=7 col=9, unsat!
row=8 col=9, unsat!
python minesweeper_MK85_bitvec.py  0.81s user 0.06s system 99% cpu 0.869 total

~/P/MK85-repo % time python minesweeper_Z3_bitvec.py
WIDTH= 9 HEIGHT= 9
row=1 col=3, unsat!
row=6 col=2, unsat!
row=6 col=3, unsat!
row=7 col=4, unsat!
row=7 col=9, unsat!
row=8 col=9, unsat!
python minesweeper_Z3_bitvec.py  1.28s user 0.02s system 99% cpu 1.293 total
"""

known=[
"01?10001?",
"01?100011",
"011100000",
"000000000",
"111110011",
"????1001?",
"????3101?",
"?????211?",
"?????????"]

from MK85 import *
import sys

WIDTH=len(known[0])
HEIGHT=len(known)

print "WIDTH=", WIDTH, "HEIGHT=", HEIGHT

def chk_bomb(row, col):

    s=MK85()

    cells=[[s.BitVec('cell_r=%d_c=%d' % (r,c), 4) for c in range(WIDTH+2)] for r in range(HEIGHT+2)]

    # make border
    for c in range(WIDTH+2):
        s.add(cells[0][c]==0)
        s.add(cells[HEIGHT+1][c]==0)
    for r in range(HEIGHT+2):
        s.add(cells[r][0]==0)
        s.add(cells[r][WIDTH+1]==0)

    for r in range(1,HEIGHT+1):
        for c in range(1,WIDTH+1):

            t=known[r-1][c-1]
            if t in "012345678":
                s.add(cells[r][c]==0)
                # we need empty border so the following expression would be able to work for all possible cases:
                s.add(cells[r-1][c-1] + cells[r-1][c] + cells[r-1][c+1] + cells[r][c-1] + cells[r][c+1] + cells[r+1][c-1] + cells[r+1][c] + cells[r+1][c+1]==int(t))

    # place bomb:
    s.add(cells[row][col]==1)

    result=s.check()
    if result==False:
        print "row=%d col=%d, unsat!" % (row, col)

# enumerate all hidden cells:
for r in range(1,HEIGHT+1):
    for c in range(1,WIDTH+1):
        if known[r-1][c-1]=="?":
            chk_bomb(r, c)

