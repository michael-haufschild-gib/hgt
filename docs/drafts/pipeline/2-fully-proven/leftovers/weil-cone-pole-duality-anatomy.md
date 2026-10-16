# Weil-cone anatomy: pole duality and comparative rigidity

- **ID:** weil-cone-pole-duality-anatomy
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** route-tt-loop-2026-10-13 rows 201, 203, 205, 206
- **Statement:**
  - (A) For a pole-free L-function whose archimedean density is nonnegative, the zero weight system lies in its Weil cone.
  - (B) If L = ζ·L′ with L′ pole-free and Ω_{L′} ≥ 0, then an (N1)-type pinning of the Weil cone of L would refute RH for ζ.
  - (C) Function-field Weil cones contain the weights of every curve of the same genus.

## Goal
These results constrain any cone-rigidity proof of RH (the HF/(N1) programme). Rigidity can only come
from the pole together with ζ's archimedean anomaly, and from Hamburger uniqueness of ζ's functional
equation. A mechanism that would also apply to ζ·L′ or to function fields proves something false.

## Definitions
For an L-function L with completed functional equation s ↦ 1 − s, write Ω_L(t) for its archimedean
spectral density on the critical line and pole_L for its pole term in Weil's explicit formula. The
Weil cone of L is the set of real weights λ on n ≥ 2 such that

  W_{L,λ}(g) = pole_L(g) + ∫ ĝ(t) Ω_L(t) dt − Σ_{n≥2} λ(n) n^{−½} (g(log n) + g(−log n)) ≥ 0

for every positive-definite test g = f⋆f̃ (f real, compactly supported).

## Theorems (paper proofs)
**(A) Pole-free L-functions have fat cones.**
- Let f be a level-1 holomorphic Hecke eigenform of weight k. Then pole_f = 0 and
  Ω_f(t) = (1/π)(Re ψ(k/2 + it) − log 2π).
- Since Re ψ(x + iy) = ψ(x) + Σ_n y²/((n+x)((n+x)² + y²)) ≥ ψ(x) for x > 0, we get
  Ω_f ≥ (1/π)(ψ(k/2) − log 2π).
- This is > 0 for k ≥ 14, because ψ(7) = H_6 − γ ≈ 1.873 > log 2π ≈ 1.838.
- So W_{f,0}(g) = ∫ ĝ Ω_f ≥ 0, i.e. λ = 0 is in the cone.
- The same holds for Dirichlet L(s, χ) with Ω_χ(t) = (1/2π)(log(q/π) + Re ψ((½ + a + it)/2)) ≥ 0 when
  log(q/π) + ψ((½ + a)/2) ≥ 0. For odd χ (a = 1) that means q ≥ 10; for even χ, q ≥ 216.
- Hence no blind test can pin the cone to {Λ_L}: pinning would force Λ_L = 0.

**(B) Cone embedding under factorization.**
- Let L = ζ·L′ with L′ pole-free and Ω_{L′} ≥ 0. Then pole_L = pole_ζ, Ω_L = Ω_ζ + Ω_{L′}, and
  W_{L,Λ} = W_{ζ,Λ} + ∫ ĝ Ω_{L′}.
- Under RH for ζ, W_{ζ,Λ} ≥ 0 (Weil's criterion), so Λ ∈ cone_L.
- Under GRH for L, also Λ_L = Λ + Λ_{L′} ∈ cone_L. Since Λ_{L′} ≠ 0, the cone contains a segment.
- Consequently, if the cone of L is contained in {Λ_L} (an (N1)-type pinning), then Λ ∉ cone_L and
  RH fails for ζ.
- Example: L = ζ_K for K = ℚ(√−q) with an odd quadratic character of conductor q ≥ 10.

**(C) Function fields.**
- Let C, C′ be curves over F_q of the same genus. Their explicit formulas have identical pole terms
  and identical constant archimedean term ∝ (2g − 2) log q.
- Hence W_{C,Λ_{C′}} = W_{C′,Λ_{C′}} ≥ 0 by Weil's theorem for C′.
- So cone_C contains the weights of every curve of genus g over F_q.

## Interpretation
- **Pole duality.** The trivial representation (the pole) blocks every height-uniform positivity
  producer (pole trilemma; route-tt rows 131, 197, 199). It is also the anchor that forces
  Σ_{n≤x} λ(n) ~ x, the only route to cone rigidity.
- **Anomaly.** The n = 1 chirp cos 2θ(t) is stationary only where θ′ = πΩ_ζ changes sign, near t ≈ 2π.
  (N1) witnesses must place their n = 1 response there (route-tt rows 184, 185, 204). A positive Ω_{L′}
  removes this window, consistent with (B).
- **Hamburger.** A fake weight system enters ζ's cone only if its own archimedean term cancels.
  By Hamburger's theorem, ζ is the only Dirichlet series over ℕ with Riemann's functional equation.
  Function fields have many curves sharing the archimedean term, hence fat cones.
  Cone fatness therefore equals the number of objects sharing the archimedean factor.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (A–C are short, dependency-closed paper proofs)
- [ ] 2 → 3  formalized: needs Weil functionals for L(s, f), L(s, χ) and curves, none of which is in
  the corpus; the core digamma inequality ψ(7) > log 2π is elementary

## Log
- 2026-10-14 — created from route-tt-loop rows 201–207.
- 2026-10-14 — added the σ-picture (route-tt rows 208–214), proved on paper under RH.
  - Any cone element has spectral measure μ_ζ+σ, with σ̂ supported on ±log ℕ_{≥2}.
  - If σ≥0 or σ≤0 then σ=0. Proof: pair σ with φ=\|sinc(a(t−i))\|², which is positive everywhere and has φ̂⊂(−log 2, log 2).
  - Proportional moves σ⁻=αμ_ζ are excluded, because σ's transform would carry a non-tempered pole kernel on the gaps.
  - Ratio form: uniqueness ⟺ no nonconstant zero-free Dirichlet series Y=X/ζ whose boundary phase is nondecreasing between consecutive ζ-zeros (with drops ≤π). The power family ζ^α fails only through the branch point at the pole.
  - (N1) uniqueness ⟺ atomicity of the cone spectral measure (corpus NULL-test lane) ⟺ a Hamburger theorem for functional equations with a jump across the critical line.
- 2026-10-14 — Lean: compactness of the Weil cone and the Krein–Milman reduction are formalized in
  `RHTower/WeilFullConeKreinMilmanReduction.lean` (`isCompact_weilCone`,
  `riemannHypothesis_of_extremePoints_weilCone`,
  `riemannHypothesis_of_primeBlindPositive_of_extremePoints`). Standard axioms only.
  (A)–(C) remain paper-only: they need Weil functionals for L(s, f), L(s, χ) and curves.
