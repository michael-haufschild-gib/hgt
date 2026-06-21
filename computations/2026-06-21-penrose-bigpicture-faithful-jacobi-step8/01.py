import numpy as np


forms = {
    "same_trace_no_negative": np.diag([1.0, 1.0, 1.0, 1.0]),
    "same_trace_one_negative": np.diag([-0.5, 1.5, 1.5, 1.5]),
    "same_trace_two_negative": np.diag([-0.5, -0.5, 2.5, 2.5]),
}

print("01 same scalar trace, different faithful negative index")
for name, q in forms.items():
    eig = np.linalg.eigvalsh(q)
    neg = int(np.sum(eig < -1e-12))
    print(f"{name:24s} trace={np.trace(q):+.3f} frob={np.linalg.norm(q):.3f} neg_index={neg} eig={eig}")

