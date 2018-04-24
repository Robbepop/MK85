from z3 import *
import itertools, math

PERSONS, DAYS, GROUPS = 15, 7, 5 # OK
#PERSONS, DAYS, GROUPS = 20, 5, 5 # no answer
#PERSONS, DAYS, GROUPS = 21, 10, 7 # no answer

# each element - group for each person and each day:
tbl=[[BitVec('%d_%d' % (person, day), GROUPS) for day in range(DAYS)] for person in range(PERSONS)]

s=Solver()

for person in range(PERSONS):
    for day in range(DAYS):
        s.add(Or(*[tbl[person][day]==(2**i) for i in range(GROUPS)]))

# enumerate all variables
# we add Or(pair1!=0, pair2!=0) constraint, so two non-zero variables couldn't be present,
# but both zero variables in pair is OK, one non-zero and one zero variable is also OK:
def only_one_must_be_zero(lst):
    for pair in itertools.combinations(lst, r=2):
        s.add(Or(pair[0]!=0, pair[1]!=0))
    # at least one variable must be zero:
    s.add(Or(*[l==0 for l in lst]))

# get two arrays of variables XORed. one element of this new array must be zero:
def only_one_in_pair_can_be_equal(l1, l2):
    assert len(l1)==len(l2)
    only_one_must_be_zero([l1[i]^l2[i] for i in range(len(l1))])

# enumerate all possible pairs:
for pair in itertools.combinations(range(PERSONS), r=2):
    only_one_in_pair_can_be_equal (tbl[pair[0]], tbl[pair[1]])

print s.check()
m=s.model()

print "group for each person:"
print "person:"+"".join([chr(ord('A')+i)+" " for i in range(PERSONS)])
for day in range(DAYS):
    print "day=%d:" % day,
    for person in range(PERSONS):
        print int(math.log(m[tbl[person][day]].as_long(),2)),
    print ""

def persons_in_group(day, group):
    rt=""
    for person in range(PERSONS):
        if int(math.log(m[tbl[person][day]].as_long(),2))==group:
            rt=rt+chr(ord('A')+person)
    return rt

print ""
print "persons grouped:"
for day in range(DAYS):
    print "day=%d:" % day,
    for group in range(GROUPS):
        print persons_in_group(day, group)+" ",
    print ""

