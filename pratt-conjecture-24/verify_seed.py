from itertools import product
from math import factorial

A, B, C = {0, 1, 2, 4}, set(range(7)), {0, 1, 5, 6}
X = {(0,0,6),(0,5,1),(0,6,0),(1,0,5),(2,3,1),(2,4,0),(4,1,1),(4,2,0)}
Y = {e for e in product(A,B,C) if sum(e) == 6}
assert Y-X == {(0,1,5),(1,4,1),(1,5,0)} and X <= Y
for a,b,c in Y:
    assert (a == 1) - 2*(b == 0) + (c == 5) + 2*(c == 6) == int((a,b,c) not in X)
for i in range(3):
    j,k = [r for r in range(3) if r != i]
    seen = set()
    for center in {e[i] for e in X}:
        star = [e for e in X if e[i] == center]
        rect = set(product({e[j] for e in star},{e[k] for e in star}))
        assert not (seen & rect), (i,center)
        seen |= rect
for m, factor in [(14,1),(15,3)]:
    n = 8*m
    count = factorial(n)//factorial(m)**8
    bound = 7**n if factor == 1 else 3*(7**n-1)+1
    assert count > bound
print("PASS: digit relation, all three ETF orientations, separator, exact count comparisons.")
