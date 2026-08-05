# Cycle 9: TSP at level two + the reduced criterion X1 (2026-08-05)

Card: `squarefree-gibbs-parity-vortex.md` (cycle-9 section).
Lean: `formal/GaloisForLFunctions/RHTower/GibbsTwoScaleLevelTwo.lean`, wired, built,
no sorry, axioms clean. Whole RHTower umbrella rebuilt clean (16955 jobs).

## X1 — the reduced OPEN CORE (all-k stability ⟸ a finite inequality)
Re[P_S(z,x)·conj P_S(z,y)] = Σ_n r^n Σ_d D_d^{(n)} cos(dθ), with
D_d = B_{(n+d)/2,(n−d)/2} + B_{(n−d)/2,(n+d)/2} (d ≥ 1), D_0 = B_{n/2,n/2},
B_{j,l} = Σ_{|T|=j,|U|=l} e^{−x(e(T)+p·e(U))}.
Using cos(dθ) ≥ −1 (even d) and **|cos(dθ)| ≤ d·cos θ for ODD d** (from
|sin(dφ)| ≤ d|sin φ|), each n-group is ≥ 0 as soon as
  even n: D_0 ≥ Σ_{d≥2 even} D_d ;  odd n: D_1 ≥ Σ_{d≥3 odd} d·D_d.
=> ALL-k sector stability follows from an explicit finite inequality on Boltzmann sums.

## X2 — level two PROVED (and the ordering constraint is an identity)
S = {q,r}: gas = a + bz + cz², a = e^{−x}, b = e^{−rx}+e^{−qx}, c = e^{−qrx}.
Criterion collapses to b₁b₂ ≥ a₁c₂ + a₂c₁. Correct pairing is CROSSWISE (diagonal fails!):
  e^{−qx}e^{−ry} ≥ e^{−y}e^{−qrx}  ⟺ q + rp ≤ p + qr ⟺ (q−p)(r−1) ≥ 0
  e^{−rx}e^{−qy} ≥ e^{−x}e^{−qry}  ⟺ r + qp ≤ 1 + qrp ⟺ (r−1)(qp−1) ≥ 0
with y = px. The cycle-8 "adjoin primes in DECREASING order" constraint is exactly the
factor (q−p). Gives 3-element gas stability at every coupling via the engine (new route,
generalizes; cycle 3's Routh cubic did not).
Cartesian trick (no polar): (a₁c₂+a₂c₁)(re²−im²) + b₁b₂(re²+im²) ≥ 2(a₁c₂+a₂c₁)re² ≥ 0.

## Repo hygiene note
The authoritative lint gate currently fails on ORPHAN MODULES in HTGeometry
(HalfLineTransportDistance, SiteFactorLiftedSpectrum, RatioBoundedWindowLanding …) from
CONCURRENT work in that area — the reported set changed between two consecutive runs
while HTGeometry.lean was being edited elsewhere. Not caused by the Gibbs programme; do
not "fix" HTGeometry.lean from a Route-E session (edit races).

## Lean traps
- `map_pow` is NOT needed when the polynomial is written with `z^2 * ↑c` (unusedSimpArgs
  linter fails the gate — warnings are errors here).
- Level-2 expansion: simp only [map_add, map_mul, Complex.conj_ofReal, add_re, add_im,
  mul_re, mul_im, conj_re, conj_im, ofReal_re, ofReal_im, pow_two] then `ring`.
