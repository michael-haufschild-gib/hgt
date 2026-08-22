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
| Lemma 2.3 (extension step) | heat trace antitone in `t`; `(0,1]` bound extends to `(0,∞)` | `DaiYoshikawa/HeatTraceMonotone` | **stage 3** `le_mul_add_one_of_antitoneOn` |
| §3.1 (3.3) | heat-trace form of `log det'`, convergence, and the cancellation (3.19) | `DaiYoshikawa/RegularizedLogDeterminant` | **stage 3** `logTorsion_sub_logTorsion` |
| §3.1 (ζ side) | `∫_0^∞ e^{−λt}t^{s−1}dt = Γ(s)λ^{−s}` and `Γ(s)ζ(s) = ∫_0^∞ Θ(t)t^{s−1}dt` | `DaiYoshikawa/SpectralZetaMellin`, `SpectralZetaMellinSum` | **stage 3** `gamma_mul_tsum_rpow_neg_heatTrace` |
| Corollary 0.4 | comparable power scales have comparable logarithms | `DaiYoshikawa/ComparableLogScales` | **stage 3** `log_inv_le_and_le_of_rpow_bounds` |
| §3.1 (continuation) | head/tail Mellin holomorphy, split at `t=1`, the two poles | `DaiYoshikawa/MellinHalfLine`, `MellinSplit`, `MellinHeadExpansion` | **stage 3** `differentiableAt_mellinHead`, `mellinHead_eq_regularized_add` |
| §3.1 (`ζ'(0)`) | `ζ(0) = a₁−h`, `ζ'(0) = H(0)+T(0)−a₀+(a₁−h)γ`, and the bridge to (3.3) | `DaiYoshikawa/SpectralZetaDerivative`, `SpectralZetaTorsionBridge` | **stage 3** `deriv_zetaCont_zero_ofReal`, `gamma_mul_zetaCont_eq_mellin` |

## Foundational theory being built (mathlib gaps, `HTGeometry/SpectralHeatKernel/`)

| Layer | Content | Lean |
|---|---|---|
| Kernel | `K(t,x,y) = Σ e^{−tλ}φ(x)\overline{φ(y)}`; Hermitian; diagonal; pointwise Cauchy–Schwarz; trace formula; antitone diagonal | `SpectralHeatKernel/Basic` |
| Semigroup | Chapman–Kolmogorov `∫K(s,x,z)K(t,z,y)dμ = K(s+t,x,y)` | `SpectralHeatKernel/Semigroup` |
| Operator | `∫K(t,x,y)v(y)dμ = Σ e^{−tλ}⟪φ,v⟫φ(x)` | `SpectralHeatKernel/Operator` |
| Min–max | infinite-dimensional Courant–Fischer upper bound (Prop 6.1's principle) + Parseval | `SpectralHeatKernel/MinMax` |
| Flow | `e^{−tΔ}` as a contraction semigroup on the eigenbasis; `‖e^{−tΔ}v‖² = Σ e^{−2tλ}|c|²` | `SpectralHeatKernel/Flow` |
| Energy | `λe^{−t₀λ} ≤ 1/(e t₀)`; the energy identity `d/dt Σe^{−2tλ}a = −2Σλe^{−2tλ}a` | `SpectralHeatKernel/Energy` |
| Heat equation | `ΔK`; **Lemma 2.1 in kernel form**; `∂ₜK = −ΔK` | `SpectralHeatKernel/HeatEquation` |
| Trial spaces | orthogonal ⟹ independent ⟹ `finrank = n`; Prop 6.1's certificate | `SpectralHeatKernel/TrialSpace` |
| Nash | `f' ≤ −A f^{1+p}` on `(0,∞)`, `f>0` ⟹ `f(t) ≤ (Apt)^{−1/p}` | `NashDifferentialInequality` |

Next: an `L¹`-contractive (Markov) layer, which is what turns Nash's inequality into
Carlen–Kusuoka–Stroock ultracontractivity, then Grigor'yan's on-diagonal-to-Gaussian bound — the
engine of Lemma 2.3.  Above that sits the geometric stack (Riemannian volume measure,
Laplace–Beltrami, Hodge theory, elliptic regularity), none of which mathlib has.

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
- [x] 2 → 3  30 Lean modules green, wired into `GaloisForLFunctions.HTGeometry`; every extracted
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
- 2026-08-22 — 24 modules.  Added the §3.1 regularization layer: the heat-trace form (3.3) of the
  zeta-regularized log-determinant with both convergence criteria and the cancellation (3.19); the
  scaled Gamma integral `∫_0^∞ e^{−λt}t^{s−1}dt = Γ(s)λ^{−s}` (a mathlib gap) and the Mellin
  representation `Γ(s)ζ(s) = ∫_0^∞ Θ(t)t^{s−1}dt`; Lemma 2.3's antitonicity/extension step; and
  Corollary 0.4's logarithmic comparison.
- 2026-08-22 — 29 modules.  The zeta-regularization chain is closed: the head and tail Mellin
  integrals are holomorphic on `Re s > −1` and entire respectively; the Mellin transform splits at
  `t = 1`; subtracting the two-term expansion produces exactly the poles `a₀/(s−1)` and `(a₁−h)/s`;
  and the continued zeta has `ζ(0) = a₁−h`, `ζ'(0) = H(0)+T(0)−a₀+(a₁−h)γ`, which the bridge module
  identifies with the two real integrals of (3.3).  The computation shows the constant term of the
  paper's (3.3) is `−a₀+(a₁−h)γ`, not the printed `(a₀−h)γ`; nothing in the paper depends on it,
  since only differences with identical `a₀,a₁,h` are used.  `gamma_mul_zetaCont_eq_mellin` closes
  the loop: on `Re s > 1` the continued zeta satisfies `Γ(s)ζ(s) = ∫_0^∞ (Θ(t)−h)t^{s−1}dt`.
  Open frontier: everything resting on
  Quillen metrics, the Bismut–Gillet–Soulé anomaly formula, Bismut–Bost, semistable reduction, and
  a manifold-level heat-kernel theory (Duhamel, parabolic maximum principle, parametrix).
