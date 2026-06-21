def involution(x):
    return 1 - x


def translation_flow(x, steps=6, delta=0.2):
    out = [x]
    cur = x
    for _ in range(steps):
        cur = cur + delta
        out.append(cur)
    return out


points = [0.5, 0.4, 0.7, -1.0]

print("03 orbit-length spectrum: order-2 constraint vs generated flow")
for x in points:
    orbit = []
    cur = x
    for _ in range(4):
        orbit.append(cur)
        cur = involution(cur)
    distinct = sorted(set(round(v, 12) for v in orbit))
    print(f"x={x:+.2f} involution_orbit={distinct} orbit_size={len(distinct)} flow_prefix={translation_flow(x)[:4]}")
