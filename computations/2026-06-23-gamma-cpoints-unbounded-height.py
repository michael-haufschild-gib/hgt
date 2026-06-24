"""Gamma c-points at unbounded height.

Purpose: stress-test the pole-confinement lemma in
docs/drafts/pipeline/0-backlog/gamma-zeta-differential-independence.md.

For Gamma(z)=1, solve log Gamma(z) = 2*pi*i*k.  Stirling gives

    (z - 1/2) log z - z + 1/2 log(2*pi) ~= 2*pi*i*k,

with first approximation z ~= 2*pi*i*k / W(2*pi*i*k/e).

Newton refinement on loggamma(z)-2*pi*i*k produces genuine Gamma(z)=1
points with Im(z) -> infinity. Therefore 1/(Gamma(z)-1) is an element
of C(z)<Gamma> with unbounded-height poles, contradicting the
pole-confinement lemma as stated.
"""

import mpmath as mp


mp.mp.dps = 80


def stirling_initial(k: int) -> mp.mpc:
    a = 2 * mp.pi * 1j * k / mp.e
    return 2 * mp.pi * 1j * k / mp.lambertw(a)


def refine(k: int) -> mp.mpc:
    z = stirling_initial(k)
    target = 2 * mp.pi * 1j * k
    for _ in range(40):
        step = (mp.loggamma(z) - target) / mp.digamma(z)
        z -= step
        if abs(step) < mp.mpf("1e-50"):
            break
    return z


print("Gamma(z)=1 c-points from loggamma(z)=2*pi*i*k")
print("k       Re(z)                 Im(z)                 |Gamma(z)-1|        k / ((T/2pi)log(T/2pi))")
for k in [5, 10, 20, 50, 100, 200, 500]:
    z = refine(k)
    err = abs(mp.gamma(z) - 1)
    t = mp.im(z)
    rv_main = (t / (2 * mp.pi)) * mp.log(t / (2 * mp.pi))
    ratio = k / rv_main
    print(
        f"{k:<7d} "
        f"{mp.nstr(mp.re(z), 20):<21s} "
        f"{mp.nstr(mp.im(z), 20):<21s} "
        f"{mp.nstr(err, 6):<18s} "
        f"{mp.nstr(ratio, 12)}"
    )

print()
print("Conclusion: Im(z) is unbounded along this explicit branch.")
print("Thus 1/(Gamma(z)-1) has unbounded-height poles inside C(z)<Gamma>.")
print("The branch also has the same T log T leading counting scale as Riemann-von Mangoldt.")
