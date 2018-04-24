from z3 import *
import itertools

#PERSONS, DAYS, GROUPS = 8, 7, 4
PERSONS, DAYS, GROUPS = 15, 7, 5
#PERSONS, DAYS, GROUPS = 20, 5, 5

# each element - group for each person and each day:
tbl=[[BitVec('%d_%d' % (person, day), 16) for day in range(DAYS)] for person in range(PERSONS)]

s=Solver()

for person in range(PERSONS):
    for day in range(DAYS):
        s.add(And(tbl[person][day]>=0, tbl[person][day] < GROUPS))

# one in pair must be equal, all others must differ:
def only_one_in_pair_can_be_equal(l1, l2):
    assert len(l1)==len(l2)
    expr=[]
    for pair_eq in range(len(l1)):
        tmp=[]
        for i in range(len(l1)):
            if pair_eq==i:
                tmp.append(l1[i]==l2[i])
            else:
                tmp.append(l1[i]!=l2[i])
        expr.append(And(*tmp))

# at this point, expression like this constructed:
# Or(
#	And(l1[0]==l2[0], l1[1]!=l2[1], l1[2]!=l2[2])
#	And(l1[0]!=l2[0], l1[1]==l2[1], l1[2]!=l2[2])
#	And(l1[0]!=l2[0], l1[1]!=l2[1], l1[2]==l2[2])
#   )

    s.add(Or(*expr))

# enumerate all possible pairs.
for pair in itertools.combinations(range(PERSONS), r=2):
    only_one_in_pair_can_be_equal (tbl[pair[0]], tbl[pair[1]])

print s.check()
m=s.model()

print "group for each person:"
print "person:"+"".join([chr(ord('A')+i)+" " for i in range(PERSONS)])
for day in range(DAYS):
    print "day=%d:" % day,
    for person in range(PERSONS):
        print m[tbl[person][day]].as_long(),
    print ""

def persons_in_group(day, group):
    rt=""
    for person in range(PERSONS):
        if m[tbl[person][day]].as_long()==group:
            rt=rt+chr(ord('A')+person)
    return rt

print ""
print "persons grouped:"
for day in range(DAYS):
    print "day=%d:" % day,
    for group in range(GROUPS):
        print persons_in_group(day, group)+" ",
    print ""

