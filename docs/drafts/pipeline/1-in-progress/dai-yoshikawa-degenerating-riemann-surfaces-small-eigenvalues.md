# Dai–Yoshikawa: degeneration of Riemann surfaces and small eigenvalues (arXiv:2509.06151v2)

- **ID:** dai-yoshikawa-small-eigenvalues
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) → THEOREM (Lean)
- **Source:** X. Dai, K.-I. Yoshikawa, *Degeneration of Riemann surfaces and small eigenvalues of the
  Laplacian*, arXiv:2509.06151v2 (math.DG, 22 Dec 2025), 45 pp.
- **Statement:** For a one-parameter degeneration `f : X → S` of compact Riemann surfaces with
  reduced reducible singular fibre `X₀` (N irreducible components) and fibre metric induced from a
  Kähler metric on `X`, the small eigenvalues satisfy
  `C₀/log|s|⁻¹ ≤ λ₁(s) ≤ … ≤ λ_{N−1}(s) ≤ C₁/log|s|⁻¹`, and
  `∏_{k<N} λ_k(s) = (c+o(1))/(log|s|⁻¹)^{N−1}`.

## Goal
Formalize, unconditionally and closed, every lemma/theorem/proposition of the paper whose content is
expressible without a Lean theory of analytic torsion / Quillen metrics / determinant of the
cohomology (none of which exist in mathlib or the corpus).  Build the missing analytic
infrastructure.

## Formalizable inventory (paper → Lean)

| Paper item | Mathematical core | Lean module | Status |
|---|---|---|---|
| Lemma 1.1 | Rayleigh-quotient comparison under a metric bound `g' ≤ c⁻¹ g` | `DaiYoshikawa/RayleighMetricComparison` | **stage 3** `mul_isGLB_le_isGLB_of_le` |
| Lemma 2.1, Thm 2.5, Lemma 2.7 constants `B`, `B'_m`, `B(n)` | `sup_{x≥0} xᵐe^{−x/a} = (ma)ᵐe^{−m}`, attained | `DaiYoshikawa/PowerExpSup` | **stage 3** `isGreatest_pow_mul_exp_neg_div` |
| Lemma 2.1 | spectral Cauchy–Schwarz `Σλᵢe^{−tλᵢ}aᵢbᵢ ≤ B^{1/2}t⁻¹(…)^{1/2}(…)^{1/2}` | `DaiYoshikawa/SpectralHeatCauchySchwarz` | **stage 3** `tsum_eigenvalue_heat_mul_le` |
| (2.10)–(2.13) | Gaussian-decay absorption `s^{−m}e^{−δ²/(cs)} ≤ B'_m δ^{−2m}e^{−δ²/(2cs)}` | `DaiYoshikawa/PowerExpSup` | **stage 3** `exp_neg_sq_div_div_pow_le` |
| Lemma 3.3, Thm 3.9, Thm 3.10 | Cheng–Li: heat-trace bound `Σ_{i≤k}e^{−tλᵢ} ≤ Ct^{−n}` ⟹ `λ_k ≳ k^{1/n}` | `DaiYoshikawa/HeatTraceEigenvalueGrowth` | **stage 3** `heatTrace_eigenvalue_pow_bound` |
| Thm 3.9 (domination) | `Σ_k e^{−tB√k}/t` integrable on `[1,∞)` | `DaiYoshikawa/HeatTraceEigenvalueGrowth` | **stage 3** `summable_exp_neg_mul_sqrt` |
| Thm 3.9 (constant `c`) | `E₁(λ) + log λ → −γ`, `c = −(N−1)γ` | `DaiYoshikawa/ExponentialIntegralSmall` | **stage 3** `tendsto_expIntegralE1_add_log` |
| Prop 5.1(3) / Prop 5.2 | `det(L·Ã + B̃ + o(1))/L^{m−k} → det A · det B` for the block pattern | `DaiYoshikawa/BlockDeterminantGrowth` | **stage 3** `tendsto_det_blockPencil_div` |
| Prop 5.1(3) | Gram matrix of an independent family is positive definite | `DaiYoshikawa/GramPositiveDefinite` | **stage 3** `gramMatrix_posDef_of_linearIndependent` |
| (5.2), Prop 5.1(1) | annulus period integral `= 2π c₀\overline{d₀} log|t|⁻¹ + (continuous)` | `DaiYoshikawa/AnnulusMonomialIntegral`, `AnnulusLaurentPairing`, `AnnulusPeriodSubstitution`, `AnnulusPeriodAsymptotic` | **stage 3** `exists_continuous_annulusPeriodRemainder` |
| Prop 5.1(2) | vanishing residue kills the logarithmic coefficient | `DaiYoshikawa/AnnulusPeriodSubstitution` | **stage 3** `substCoeff_zero_zero_eq_zero_of_residue` |
| Lemma 3.1 | smooth convex cut: `0` below `c`, slope one above `2c` | `DaiYoshikawa/SmoothConvexTransition` | **stage 3** `convexOn_cutPrimitive` |
| Lemma 3.2 | spectral-gap transfer across comparable metrics | `DaiYoshikawa/RayleighMetricComparison` | **stage 3** `le_of_comparable_gap` |
| Prop 3.5 (2) | uniform geometric tail of the spectral expansion | `DaiYoshikawa/UniformSpectralTail` | **stage 3** `tsum_spectral_tail_le` |
| Prop 6.1 (min–max) | disjointly supported trial functions: quotient ≤ max of quotients | `DaiYoshikawa/RayleighMetricComparison` | **stage 3** `sum_sq_mul_le_of_le` |
| Thm 3.9 (identity) | `Σ E₁(λᵢ) = −log ∏λᵢ + Σ Ein(λᵢ) − mγ`, error `O(Σλᵢ)` | `DaiYoshikawa/ExponentialIntegralSmall` | **stage 3** `sum_expIntegralE1_eq` |
| Lemma 6.2 | Jacobi-ideal Cauchy–Schwarz `‖ζ‖^{2ν} ≤ (Σ|g_ij|²)‖df‖²` | `DaiYoshikawa/JacobiIdealLojasiewicz` | **stage 3** `pow_sum_normSq_le_of_jacobi_relation` |
| Lemma 6.3 | integral Grönwall `ψ ≤ aη + b∫ψ ⟹ ψ ≤ (a/b)(e^{bη}−1)` | `DaiYoshikawa/IntegralGronwallAffine` | **stage 3** `le_affine_gronwall_of_volterra_bound` |
| Lemma 6.6(3) | logarithmic cutoff has Dirichlet energy `2π/log(b/a)` | `DaiYoshikawa/LogarithmicCutoffEnergy` | **stage 3** `setIntegral_logCutoff_energy` |
| §7 | product law + individual upper bounds ⟹ individual lower bounds | `DaiYoshikawa/ProductLawTwoSided` | **stage 3** `le_of_prod_le_of_le_div` |
| §10 Appendix | Gauss–Bonnet defect `2δ_p + Σ(N_q−1) > 0` forces `min K_s → −∞` | `DaiYoshikawa/NormalizationEulerDefect` | **stage 3** `gaussBonnet_normalization_incompatible` |
| Lemma 2.8, Prop 2.10 | the Duhamel Gaussian constant `(8π)^n t^{k+1−n}/(k+1)` | `DaiYoshikawa/GaussianDuhamelConstant` | **stage 3** `integral_duhamelGaussian_mul_inv` |

## Out of reach (recorded, not faked)
Analytic torsion `τ(M,E)` and its zeta-regularized definition; Quillen metrics and the
Bismut–Gillet–Soulé anomaly formula; Bismut–Bost degeneration of Quillen metrics; determinant of
the cohomology `λ(F)`; semistable reduction; Grauert base change; Riemann–Roch on curves
(Lemma 4.1); Masur's hyperbolic comparison; Schoen–Wolpert–Yau; Li–Tian / Carlen–Kusuoka–Stroock /
Grigor'yan heat kernel machinery on manifolds.  These are cited external inputs, not proved in the
paper, or require a manifold-level heat-kernel theory absent from mathlib.  Lemmas whose *whole*
content is one of these are not restated as Lean hypotheses.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  paper proof of each extracted core
- [x] 2 → 3  18 Lean modules green, wired into `GaloisForLFunctions.HTGeometry`; every extracted
      item at stage 3; axiom audit clean
- [ ] 3 → 4  n/a (external paper)

## Log
- 2026-08-22 — created; full paper read; formalizable inventory frozen.
- 2026-08-22 — 11 modules Lean-closed and wired into the `HTGeometry` umbrella; axiom audit clean
  (`propext`, `Classical.choice`, `Quot.sound` only).
- 2026-08-22 — 18 modules total.  Added the full §5 annulus layer (monomial orthogonality, Laurent
  pairing, the `y = t/x` substitution, and Proposition 5.1 (1) in the sharp form "logarithm plus a
  globally continuous remainder"), Proposition 5.1 (2)–(3), Lemma 3.1's convex cut, Lemma 3.2's
  comparison chain, Proposition 3.5's uniform spectral tail, Theorem 3.9's summed identity, the
  min–max step of Proposition 6.1, and the Appendix defect.  Every formalizable item of the
  inventory is now at stage 3.
