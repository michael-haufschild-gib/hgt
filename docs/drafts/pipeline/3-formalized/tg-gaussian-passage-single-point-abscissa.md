# TG — single-point abscissa law of the Gaussian passage

- **ID:** TG-ABS-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** TG-ZF-2 converse (open there); corpus "bounded passage ⇔ zero-free half-plane" used circle
  arg-oscillation at all heights
- **Statement:** For Re s > 0, a ≥ 0: Φₓ'/Φₓ(s) = O(x^{−a}) as x→0⁺ ⇒ ξ(z) ≠ 0 for Re z > Re s + 2a.
  Abscissa law: (∀ρ, Re ρ ≤ θ) ⟺ passage bounded at every real σ ∈ (max θ 0, 2).
  RH ⟺ passage bounded at every real σ ∈ (½, 2).

## Proof
- Φₓ'/Φₓ(s) = A(s) − G_s(πx), G_s(y) = Σ Λ(n)n^{−s}e^{−yn²} − E(y,1−s).
- Mellin in y: prime part via mathlib hasSum_mellin (frequencies n²) = Γ(w)L(Λ,s+2w); continuum part
  by Fubini (integrable_prod_iff') = Γ(w)/(s+2w−1).
- Bound at 0 from hypothesis; faster-than-any-power decay at ∞ (prime part ≤ Ce^{−y}, continuum by the
  incomplete-Gamma bound) ⇒ mellin G_s holomorphic on Re w > a (mathlib
  mellin_differentiableAt_of_isBigO_rpow).
- L(Λ,z) − 1/(z−1) = A(z) − ξ'/ξ(z) (Re z>1) ⇒ ξ'(s+2w) = ξ(s+2w)K(w) with K holomorphic on Re w>a
  (identity theorem on the convex half-plane).
- Zero at z ⇒ (u−z)ξ'/ξ(u) → ord ≥ 1 (HTGeometry residue lemma) but = (u−z)K → 0. Contradiction.

## Lean
`RHTower/GaussianPassageSinglePointAbscissa.lean` (603 lines), wired after FormationAnchoredCubicEndpoint.
`lake build --old` exit 0, no warnings; axioms [propext, Classical.choice, Quot.sound].

## Reading
Local-to-global: the source at ONE point controls the whole half-plane to its right, with growth
exponent a ↦ abscissa excess 2a. The Mellin variable is the damping y; zeros of ξ are exactly the
poles (ρ−s)/2 of the damping transform, so no cancellation among zeros can hide one (the analytic
individuation the statistical/mean-square approach lacks). TG content: a TG producer only needs a
one-point bound on the real axis per σ; equivalently the obstruction is a pointwise growth estimate
of the Gaussian prime sum Σ Λ(n)n^{−σ}e^{−yn²} − E(y,1−σ) on (0,1].
