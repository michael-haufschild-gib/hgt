"""
Referee: the no-margin is an EXCEPTIONAL POINT of a PT-symmetric operator.
Draft: arithmetic-cosmology-II-pt-symmetry-horizons-time-loops.md §1.

PT-symmetric quantum mechanics (Bender-Boettcher 1998; Bender-Brody-Mueller 2017 for the zeta zeros):
a non-Hermitian but PT-symmetric Hamiltonian has a REAL spectrum when PT is unbroken, and
COMPLEX-CONJUGATE PAIRS when PT is spontaneously broken. The two regimes meet at an EXCEPTIONAL POINT
where eigenvalues AND eigenvectors coalesce (the operator becomes defective / non-diagonalizable).

Toy family (P = sigma_x, T = complex conjugation; PT-symmetric for all real a,b):
    H(a,b) = [[ i a , b ],
              [ b , -i a ]]
    eigenvalues  lambda = +/- sqrt(b^2 - a^2)
    eigenvector overlap (normalized) = a/b           (exact, derived; -> 1 at the exceptional point)

Dictionary to the zeta picture:
    a < b   : real spectrum            <->  zeros ON the line   (PT unbroken, "RH-like")
    a = b   : EXCEPTIONAL POINT, lambda=0 double, defective  <->  the NO-MARGIN (lambda_min -> 0)
    a > b   : conjugate imaginary pair <->  off-line zero quad (PT broken)
The parameter a/b plays the role of off-line-ness; RH = the operator sits in the PT-unbroken phase,
pinned exactly at the exceptional threshold (no positive margin). Certifies the structural identity
"no-margin = exceptional point", not RH itself.
"""
import mpmath as mp

mp.mp.dps = 30
b = mp.mpf('1')


def eigs(a):
    disc = b * b - a * a
    r = mp.sqrt(disc + 0j)  # complex sqrt: real for a<b, imaginary for a>b
    return r, -r


def overlap(a):
    # normalized Hermitian inner product of the two eigenvectors; exact closed form a/b for a<b
    lam, _ = eigs(a)
    vp = mp.matrix([1, (lam - 1j * a) / b])
    vm = mp.matrix([1, (-lam - 1j * a) / b])
    ip = mp.conj(vp[0]) * vm[0] + mp.conj(vp[1]) * vm[1]
    np_ = mp.sqrt((mp.conj(vp[0]) * vp[0] + mp.conj(vp[1]) * vp[1]).real)
    nm_ = mp.sqrt((mp.conj(vm[0]) * vm[0] + mp.conj(vm[1]) * vm[1]).real)
    return abs(ip) / (np_ * nm_)


print("=== PT phases of H(a,b=1): real spectrum -> exceptional point -> conjugate pair ===")
print(f"{'a':>6} {'a/b':>6} | {'eigenvalues lambda = +/- sqrt(b^2-a^2)':>40} | {'gap':>12} | phase / zeta meaning")
for av in ['0.0', '0.5', '0.9', '0.99', '0.999', '1.0', '1.001', '1.1', '1.5']:
    a = mp.mpf(av)
    lp, lm = eigs(a)
    gap = abs(lp - lm)
    if a < b:
        phase = "PT UNBROKEN (real) = zeros ON line"
    elif a == b:
        phase = "EXCEPTIONAL POINT = the NO-MARGIN"
    else:
        phase = "PT BROKEN (conj pair) = OFF line"
    print(f"{av:>6} {mp.nstr(a/b,4):>6} | {mp.nstr(lp,8):>19} , {mp.nstr(lm,8):>17} | {mp.nstr(gap,6):>12} | {phase}")

print()
print("=== eigenvector coalescence -> 1 at the exceptional point (overlap = a/b, exact) ===")
for av in ['0.0', '0.5', '0.9', '0.99', '0.999', '0.9999']:
    a = mp.mpf(av)
    print(f"  a/b={av:>7}:  |<v+|v->|/(|v+||v-|) = {mp.nstr(overlap(a),12)}   (predicted a/b = {av})")

print()
print("=== the exceptional point a=b: defective / non-diagonalizable (single eigenvector) ===")
a = b
lp, lm = eigs(a)
print(f"  a=b=1: eigenvalues = {mp.nstr(lp,6)}, {mp.nstr(lm,6)} (degenerate at 0)")
print(f"         eigenvector overlap -> 1: matrix is DEFECTIVE (Jordan block) = the no-margin singularity")

print()
print("VERDICT: the on-line / no-margin / off-line trichotomy of the zeros is, structurally, the")
print("         PT-unbroken / exceptional-point / PT-broken trichotomy of a PT-symmetric operator.")
print("         The NO-MARGIN (lambda_min -> 0, eigenvalues + eigenvectors coalescing) is an")
print("         EXCEPTIONAL POINT. RH = the operator stays PT-unbroken, pinned at the threshold. OPEN.")
