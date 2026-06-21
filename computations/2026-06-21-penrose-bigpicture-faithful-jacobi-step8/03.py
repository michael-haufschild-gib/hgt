import math


def y(t):
    # Synthetic Jacobi-like signal with a narrow negative crossing.
    return (t - 1.003) * (t - 1.017) * (t - 2.5)


def count_sign_changes(step):
    xs = [i * step for i in range(int(3.0 / step) + 1)]
    vals = [y(x) for x in xs]
    hits = 0
    for a, b in zip(vals, vals[1:]):
        if a == 0 or a * b < 0:
            hits += 1
    return hits


print("03 finite sampling can miss narrow faithful zero events")
for step in [0.5, 0.1, 0.05, 0.02, 0.005]:
    print(f"step={step:.3f} detected_sign_changes={count_sign_changes(step)}")
print("true_roots=[1.003, 1.017, 2.5]")
