# Rational Bochner deformations of ζ_γ are classified by the horizontal zero line at height γ

- **ID:** bgg-c1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Every nontrivial rational deformation `F = ζ_γ · ∏(s − zᵢ)^{mᵢ}` in
  `HeightCoupledSystem 2 1 1 γ` has its rightmost net-multiplicity point anchored at a real pole
  `σ*` of the multiplier with `ξ(σ* + iγ) = 0`; hence rational rigidity off the zero ordinates,
  exact chiral central descent without off-critical zeros at `γ`, and
  `RationalCentralVanishingCeiling γ ⟺` no off-critical zero at ordinate `γ` (`γ ≠ 0`),
  `RH ⟺ ∀ γ ≠ 0, RationalCentralVanishingCeiling γ`.

## Paper proof
1. *Lattice sieve.* `−F'/F = A + G`, `A = Σ Λ(n)(2 + 2cos(γ log n)) n^{−s}` (nonnegative lattice),
   `G = Σ_w (−M(w))/(s − w)`. Positive-definite sections ⇒ complete monotonicity on a real ray ⇒
   Post–Widder `PW_k(A+G)(t) ≥ 0`. `PW_k(G)(t) → w(t) = Σ c(w)e^{t Re w}cos(t Im w)`;
   each atom `log n ≠ t` contributes `≤ (k/t)(re^{1−r})^k`, `r = log n/t`, uniform tail
   `(k/t)(2e^{−2})^k e^{4σ₀t} n^{−σ₀}` for `r ≥ 4`, so `PW_k(A)(t) → 0` off `log ℕ`; continuity
   extends `w ≥ 0` to `(0, ∞)`.
2. *Conjugation symmetry.* Evenness of `Re G` on vertical lines makes `Re(G − G^*) = 0`,
   `G^*(s) = Σ c/(s − w̄)`; Cauchy–Riemann gives a constant, which decays, so `G = G^*`.
3. *Landau anchor.* `G(s) = ∫₀^∞ w(t)e^{−st}dt` right of `σ*`, so `|G(x+ib)| ≤ G(x)`; residues
   `(x − σ*)G(x + ib) → c(σ* + ib)` give `|c(σ* + ib)| ≤ c(σ*)`, and a nonzero top weight forces
   `c(σ*) > 0`.
4. *Pole forcing.* `Λ = Λ_γ R` on `ℂ ∖ {zᵢ}` (identity theorem, connected complement);
   `Λ(s)(s − σ*)^k = Λ_γ(s)R_{σ*}(s)` near `σ*` gives `Λ_γ(σ*) = 0`; `ξ` has no real zeros, and
   conjugation gives `ξ(σ* + iγ) = 0`.
5. *Orders.* Without off-critical zeros at `γ`, `σ* = 1/2`, and the same identity yields
   `ord Λ + (−M(1/2)) = ord Λ_γ`. The quartet contraction is `∏` over 9 explicit points.

## Lean
Modules `BiarithmeticGaugeGeometry/LatticeSievedPostWidderAndLandauAnchor.lean`,
`BiarithmeticGaugeGeometry/RationalBochnerDeformationsOfTheHeightCoupledCarrier.lean`.
Theorems: `tendsto_postWidder_lattice`, `polarScaleWeight_nonneg_of_lattice_posDef`,
`polarSum_eq_reflected_of_even`, `landau_real_anchor`, `lattice_real_anchor`,
`neg_logDeriv_heightCoupledF_eq_LSeries`, `rationalDeformation_real_anchor`,
`rationalDeformation_rigid_of_xi_ne_zero_on_line`, `rationalDeformation_rigid_zero_height`,
`rationalDeformation_central_descent`, `rationalCentralVanishingCeiling_iff`,
`riemannHypothesis_iff_forall_rationalCentralVanishingCeiling`. Axioms: propext,
Classical.choice, Quot.sound.

## Log
- 2026-10-27 — formalized.
