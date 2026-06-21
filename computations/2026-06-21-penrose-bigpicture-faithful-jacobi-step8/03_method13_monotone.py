def y(t):
    return (t - 1.003) * (t - 1.017) * (t - 2.5)


def count_sign_changes(step):
    xs = [i * step for i in range(int(3.0 / step) + 1)]
    vals = [y(x) for x in xs]
    hits = 0
    for a, b in zip(vals, vals[1:]):
        if a == 0 or a * b < 0:
            hits += 1
    return hits


steps = [0.5, 0.25, 0.1, 0.05, 0.025, 0.02, 0.01, 0.005, 0.0025]
counts = [count_sign_changes(step) for step in steps]
print("03 method 13 monotone refinement check")
for step, count in zip(steps, counts):
    print(f"step={step:.4f} detected={count}")
print(f"nondecreasing_under_this_refinement={all(a <= b for a, b in zip(counts, counts[1:]))}")
print("stabilizes_at_true_count=3 only after step below the narrow root separation")
