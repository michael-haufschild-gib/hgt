import itertools
import math
import numpy as np


angles = [0, 60, 120, 180, 240, 300]


def k(theta):
    rad = math.radians(theta)
    return np.array([math.cos(rad), math.sin(rad)])


def canonical(triple):
    return tuple(sorted(t % 360 for t in triple))


def closure_norm(triple):
    return float(np.linalg.norm(sum((k(t) for t in triple), np.zeros(2))))


triples = sorted({canonical(t) for t in itertools.combinations_with_replacement(angles, 3)})
closing = []
nonclosing_same_passport = []
for tri in triples:
    c = closure_norm(tri)
    if c < 1e-9:
        closing.append(tri)
    else:
        nonclosing_same_passport.append((tri, c))

print("Minimal equal-length three-mode counterexamples to scalar passport sufficiency")
print(f"scalar_passport=(mode_count=3, total_energy=3, avg_wavenumber=1)")
print(f"closing_triples_count={len(closing)}")
for tri in closing[:8]:
    print(f"  closing={tri} closure={closure_norm(tri):.8f}")
print("first non-closing triples with identical scalar passport")
for tri, c in nonclosing_same_passport[:8]:
    print(f"  nonclosing={tri} closure={c:.8f}")
