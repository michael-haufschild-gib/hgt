import math
from collections import defaultdict
from itertools import product


def primitive(triple):
    if triple == (0, 0, 0):
        return False
    g = 0
    for x in triple:
        g = math.gcd(g, abs(x))
    return g == 1


planes = [t for t in product(range(-2, 3), repeat=3) if primitive(t)]
axes = [t for t in product(range(-2, 3), repeat=3) if primitive(t)]


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


incidence = defaultdict(list)
for axis in axes:
    for plane in planes:
        if dot(axis, plane) == 0:
            incidence[axis].append(plane)

sample_axes = [(0, 0, 1), (1, 1, 0), (1, -1, 1), (2, -1, 0)]
print("Weiss zone law: incidence constraint hu+kv+lw=0")
for axis in sample_axes:
    members = sorted(incidence[axis])
    naive_steps = []
    u, v, w = axis
    for step in [(-1, 0, 0), (0, 1, 0), (0, 0, 1), (1, -1, 0)]:
        candidate = (u + step[0], v + step[1], w + step[2])
        if primitive(candidate):
            naive_steps.append((candidate, dot(axis, candidate) == 0))
    print(
        f"axis={axis} members_count={len(members):2d} "
        f"first_members={members[:8]} naive_neighbor_membership={naive_steps}"
    )

violations = 0
for axis, members in incidence.items():
    for plane in members:
        if dot(axis, plane) != 0:
            violations += 1
print(f"verified_incidence_violations={violations}")
