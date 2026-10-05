# Is the Báez-Duarte limit distance exactly the Blaschke defect of the off-line zeros?

**Conjecture (open).** `lim_{N→∞} d_N² = 1 − e^{−2I}`, `I = (1/2π)∫ log|ζ(½+it)| dt/(¼+t²)`
(= Σ_{Re ρ>½} m_ρ log|ρ/(ρ−1)|, MUST-783). Equivalently: the closed NB span is the Hardy subspace B·H² of functions
vanishing at the off-line zeros (B the Blaschke product of `G = (s−1)ζ(s)`, whose singular inner factor is trivial).

## What is proved (unconditional)
- Lower bound for every N and distinct zeros: `d_N² ≥ 1 − Π|1−ρ|²/|ρ|²` (MUST-784, BaezDuarteBlaschkeFloor).
  With simple off-line zeros this is `≥ 1 − e^{−2I}` in the limit.
- RH case: `I = 0` and `d_N → 0` (MUST-778, MUST-781).
- Critical zeros only affect the rate: `liminf d_N² log N ≥ Σ 2/|ρ|²` (MUST-782).

## Missing for the upper bound
Approximate `−conj(B(1))·B/ζ = −conj(B(1))/O` (O = ζ/B outer on Re s > ½) by NB polynomials in L²(dt/|s|²). Under RH the
corpus does this with Riesz–Perron for 1/ζ and |ζ(½+it)| ≤ K t^{1/8}|ζ(½+δ+it)| (ξ monotone). Without RH: log|1/O(σ+it)| is
the Poisson integral of −log|ζ(½+·)|, so |1/O| ≤ T^{C/δ} on Re s = ½+δ (local log⁻ bound) — polynomial, not T^ε; and the
transfer from Re s = ½+δ to the line needs a replacement for ξ-monotonicity near off-line zeros.

## Status
- 2026-10-05: opened after MUST-784. Multiplicity version of the floor (derivative detectors) also open.
- 2026-10-05: route identified for the CONTINUOUS family θ ∈ (0,1] (bdDist over all dilations): the closed span is invariant
  under all dilations, i.e. under multiplication by e^{−λs}, λ ≥ 0, in H²(Re s > ½) — Beurling–Lax gives span = Θ·H², Θ inner.
  Θ = gcd of the inner parts of ζ(s)(θ^{s}−θ)/s (normalization aside): the factors (θ^s − θ) have no common zeros/singular part
  as θ varies, ζ's Blaschke part is B, and MUST-783 (no singular mass at s = ∞) removes e^{−cs}. Then d² = dist(k₁, BH²)² =
  1 − |B(1)|² = 1 − e^{−2I}. Missing infrastructure: Beurling–Lax for the half-plane translation semigroup and inner–outer
  factorization (HTGeometry has model spaces/Cauchy totality, not Beurling–Lax). The discrete family 1/n is NOT invariant under
  all dilations (only n^{−s}), so this route gives only the continuous distance.
- 2026-10-05: P1 done — Beurling's theorem on coefficient H²(𝔻): `HTGeometry.exists_inner_multiplier_of_shiftInvariant`
  (HardyBeurlingInvariantSubspace, axiom-clean): every closed shift-invariant M ≠ 0 is θH² with M_θ isometric. Wandering
  subspace proof in the ℓ² model; inner bound |θ| ≤ 1 by Bessel against Szegő kernels; no boundary theory.
  Next: P2 carrier ≅ H²(𝔻) intertwining dilations θ ↦ θ^s with the semigroup e^{−λ(1+w)/(1−w)} (Laguerre/Mellin),
  P3 semigroup-invariant ⇒ shift-invariant (resolvent (1−w)/2 = ∫e^{−λ}e^{−λ(1+w)/(1−w)}dλ), P4 identify θ = B
  (gcd of inner parts; no singular factor by MUST-783), P5 dist(k, BH²)² = 1 − |B(1)|² = 1 − e^{−2I}.
- 2026-10-05 (external audit): the continuous-family identity is Nikolski's distance formula (Ann. Inst. Fourier 45 (1995)
  143–159; Beurling 1955 closure theorem). REDISCOVERED — programme P2–P5 cancelled. Only P1 (Beurling's theorem in Lean)
  stays, as reusable infrastructure. Open variants that are not classical: (i) unconditional equality of the discrete
  (Báez-Duarte) and continuous closures; (ii) the Bettin–Conrey–Farmer constant without their Σ1/|ζ'(ρ)|² hypothesis.
  Both are receiver-level; not pursued.
- 2026-10-05 (correction): for the DISCRETE family the conjectured equality is unsupported. D = span{ρ_{1/k}} ⊊ C
  unconditionally (on (½,1] each ρ_{1/k}, k ≥ 2, is the constant 1/k; g = 1_{(½,¾)} − 1_{(¾,1)} is ⊥ D but not ⊥ ρ_θ for
  θ ∈ (½,¾)). Only lim d_N² ≥ dist²(χ, C) = 1 − e^{−2I} (Nikolski + MUST-784) holds; equality for the discrete family is open
  and not implied by Beurling–Lax (D is invariant only under the dilations by 1/k).
