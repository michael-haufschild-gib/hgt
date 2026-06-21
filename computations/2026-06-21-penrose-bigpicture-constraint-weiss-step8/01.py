import cmath


def sigma_conj(s):
    return 1 - s.conjugate()


points = [
    0.5 + 0.1j,
    0.5 + 2.0j,
    0.4 + 0.1j,
    0.7 - 3.0j,
    1.2 + 0.0j,
]

print("01 fixed-locus residual for anti-holomorphic FE constraint")
for s in points:
    residual = abs(sigma_conj(s) - s)
    print(f"s={s!r:18s} residual={residual:.6f} on_line={residual < 1e-12}")

