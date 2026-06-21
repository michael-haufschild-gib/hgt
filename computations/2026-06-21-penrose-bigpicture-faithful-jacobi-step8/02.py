import numpy as np


bulk = np.eye(4)
boundary_vectors = {
    "no_boundary": np.zeros(4),
    "weak_boundary": np.array([0.25, 0.0, 0.0, 0.0]),
    "critical_boundary": np.array([1.0, 0.0, 0.0, 0.0]),
    "strong_boundary": np.array([1.25, 0.0, 0.0, 0.0]),
}

print("02 same positive bulk, different boundary extension inertia")
for name, v in boundary_vectors.items():
    q = bulk - np.outer(v, v)
    eig = np.linalg.eigvalsh(q)
    neg = int(np.sum(eig < -1e-12))
    zero = int(np.sum(np.abs(eig) <= 1e-12))
    print(f"{name:18s} boundary_norm={np.linalg.norm(v):.3f} inertia=({neg},{zero},{4-neg-zero}) eig={eig}")

