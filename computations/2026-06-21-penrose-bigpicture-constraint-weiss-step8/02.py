import numpy as np


# Constraint rows are linear incidences; a completed object is allowed when it lies
# in the kernel.  This measures kernel dimension, not fixed-point residual.
rows = np.array(
    [
        [1, 0, -1, 0],
        [0, 1, 0, -1],
        [1, 1, -1, -1],
    ],
    dtype=float,
)

samples = {
    "constraint_satisfying": np.array([2.0, 3.0, 2.0, 3.0]),
    "one_incidence_broken": np.array([2.0, 3.0, 2.1, 3.0]),
    "balanced_sum_only": np.array([2.0, 3.0, 1.0, 4.0]),
}

u, singular, vt = np.linalg.svd(rows)
rank = int(np.sum(singular > 1e-12))
null_dim = rows.shape[1] - rank

print("02 incidence-rank model for constraint-not-flow")
print(f"rank={rank} null_dim={null_dim} singular={singular}")
for name, x in samples.items():
    residual = rows @ x
    print(f"{name:24s} residual={residual} norm={np.linalg.norm(residual):.6f}")

