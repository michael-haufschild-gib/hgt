"""Exploratory exact tangent calculation; run on the authorized Runpod only.

Output is research guidance, not a formal proof certificate. Each cutoff is
independent and runs in a separate worker. No floating-point or eigenvalue test.
"""
import json
import os
from concurrent.futures import ProcessPoolExecutor
from itertools import combinations

import sympy as S


def calculate(cutoff):
    primes = list(S.primerange(1, cutoff + 1))
    divisors = [2, 3, 5, 6, 10, 15, 30]
    def a(d, n):
        return 1 - d * int(n % d == 0)
    valuations = []
    for n in range(1, cutoff + 1):
        factorization = S.factorint(n)
        valuations.append([factorization.get(p, 0) for p in primes])
    V = S.Matrix(valuations)
    C = S.Matrix([[a(d, n) for n in range(1, cutoff + 1)] for d in divisors])
    k = [2 * (a(6, n) - a(3, n) + 5 * (a(15, n) - a(30, n)))
         for n in range(1, cutoff + 1)]
    A = C * V
    H = V.T * S.diag(*k) * V
    basis = A.nullspace()
    B = S.Matrix.hstack(*basis)
    R = B.T * H * B
    witnesses = {}
    directions = [S.eye(len(basis))[:, i] for i in range(len(basis))]
    for i, j in combinations(range(len(basis)), 2):
        directions.extend([directions[i] + directions[j], directions[i] - directions[j]])
    for y in directions:
        value = (y.T * R * y)[0]
        label = "negative" if value < 0 else "positive" if value > 0 else "zero"
        if label in witnesses:
            continue
        x = B * y
        assert A * x == S.zeros(A.rows, 1)
        witnesses[label] = {
            "prime_direction": {str(p): str(v) for p, v in zip(primes, x) if v},
            "quadratic_value": str(value),
        }
    return {
        "cutoff": cutoff,
        "primes": primes,
        "constraint_rank": A.rank(),
        "tangent_dimension": len(basis),
        "restriction_rank": R.rank(),
        "restriction_is_zero": R.is_zero_matrix,
        "witnesses": witnesses,
        "constraint_matrix": [[str(x) for x in row] for row in A.tolist()],
        "nullspace_basis": [[str(x) for x in row] for row in B.tolist()],
        "restricted_form": [[str(x) for x in row] for row in R.tolist()],
    }


if __name__ == "__main__":
    cutoffs = [30, 60, 90, 120, 180, 210]
    with ProcessPoolExecutor(max_workers=min(len(cutoffs), os.cpu_count() or 1)) as pool:
        results = list(pool.map(calculate, cutoffs))
    print(json.dumps({"sympy": S.__version__, "method": "exact rational nullspace and quadratic directions",
                      "results": results}, indent=2))
