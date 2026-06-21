def involution(x):
    return 1 - x


def mark(x):
    # Map x in [-1,2] onto a 61-character line.
    lo, hi = -1.0, 2.0
    idx = round((x - lo) / (hi - lo) * 60)
    idx = max(0, min(60, idx))
    chars = [" "] * 61
    chars[20] = "|"  # x = 0
    chars[30] = "*"  # x = 1/2 fixed locus
    chars[40] = "|"  # x = 1
    chars[idx] = "X"
    return "".join(chars)


points = [0.5, 0.4, 0.7, -1.0]
print("03 method 5 visual: order-2 orbit against fixed-locus marker")
print("legend: * = fixed locus x=1/2, | = x=0 or x=1, X = orbit point")
for x in points:
    y = involution(x)
    print(f"x={x:+.2f} -> iota(x)={y:+.2f}")
    print("  " + mark(x))
    print("  " + mark(y))
    if abs(x - y) < 1e-12:
        print("  fixed: one-point constraint orbit")
    else:
        print("  paired: two-point constraint orbit, not a propagated trajectory")
