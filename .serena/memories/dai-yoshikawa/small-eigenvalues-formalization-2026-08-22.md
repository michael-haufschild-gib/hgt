# Dai–Yoshikawa, *Degeneration of Riemann surfaces and small eigenvalues* (arXiv:2509.06151v2)

Card: `docs/drafts/pipeline/1-in-progress/dai-yoshikawa-degenerating-riemann-surfaces-small-eigenvalues.md`
Lean: `formal/GaloisForLFunctions/HTGeometry/DaiYoshikawa/` (19 modules, all wired into the
`GaloisForLFunctions.HTGeometry` umbrella, axiom audit clean).

## What is closed (stage 3)

| Paper item | Lean name |
|---|---|
| Lemma 1.1 (Rayleigh comparison) | `mul_isGLB_le_isGLB_of_le` |
| Lemma 3.2 (gap transfer across comparable metrics) | `le_of_comparable_gap` |
| Prop 6.1 min–max step (disjoint supports) | `sum_sq_mul_le_of_le` |
| `sup_{x≥0} xᵐ e^{−x/a} = (ma)ᵐe^{−m}`, attained | `isGreatest_pow_mul_exp_neg_div` |
| Gaussian-decay absorption (2.10)–(2.13) | `exp_neg_sq_div_div_pow_le` |
| Lemma 2.1 (spectral Cauchy–Schwarz) | `tsum_eigenvalue_heat_mul_le` |
| Lemma 2.8/Prop 2.10 Duhamel Gaussian constant | `integral_duhamelGaussian_mul_inv`, `integral_gaussian_pi` |
| Lemma 3.1 (smooth convex cut) | `convexOn_cutPrimitive`, `cutPrimitive_eq_zero`, `cutPrimitive_eq_add` |
| Lemma 3.3 / Cheng–Li (any `n`) | `heatTrace_eigenvalue_pow_bound`, `_linear_bound`, `_sqrt_bound` |
| Prop 3.5 (2) uniform spectral tail | `tsum_spectral_tail_le` |
| Thm 3.9 constant `c = −(N−1)γ` | `tendsto_expIntegralE1_add_log`, `sum_expIntegralE1_eq` |
| Thm 3.9/3.10 domination `Σ e^{−c√k}` | `summable_exp_neg_mul_sqrt` |
| §3.1 formula (3.3) and its cancellation (3.19) | `logTorsion`, `logTorsion_sub_logTorsion` |
| Prop 5.1 (1) — sharp form | `exists_continuous_annulusPeriodRemainder` |
| Prop 5.1 (2) | `substCoeff_zero_zero_eq_zero_of_residue` |
| Prop 5.1 (3) | `gramMatrix_posDef_of_linearIndependent` |
| Prop 5.2 determinant asymptotic | `tendsto_det_blockPencil_div`, `tendsto_log_det_blockPencil_sub` |
| Lemma 6.2 (Jacobi ideal) | `pow_sum_normSq_le_of_jacobi_relation` |
| Lemma 6.3 (affine-source Grönwall) | `le_affine_gronwall_of_volterra_bound` |
| Lemma 6.6 (3) log cutoff energy `= 4π/log ε⁻¹` | `setIntegral_logCutoff_energy` |
| §7 product law ⟹ two-sided bounds | `le_of_prod_le_of_le_div` |
| Appendix Lemma 10.1 arithmetic | `gaussBonnet_normalization_incompatible` |

## Reusable bricks this left in the corpus

* `PowerExpSup` — the one extremal inequality behind every `B`, `B'`, `B'_m`, `B(n)` constant, plus
  the trade of `s^{−m}` against half a Gaussian.  Use it instead of re-deriving.
* `AnnulusMonomialIntegral` / `AnnulusLaurentPairing` — `∫_{a<|z|<b} z^j z̄^{j'} |z|^{−2} dA`
  evaluated: `0` off-diagonal, `2π log(b/a)` at `j=0`, `2π(b^{2j}−a^{2j})/(2j)` otherwise.  This is
  the general machine for logarithmic period divergence over a vanishing cycle.
* `BlockDeterminantGrowth` — `det(L·Ã + B̃ + o(1))/L^{#κ} → det B · det A`, proved by scaling the
  lower rows; works over any `RCLike`.
* `GramPositiveDefinite` — Gram matrix of a linearly independent family is `PosDef` (mathlib gap;
  the corpus previously had only the determinant criterion in `SeparatingGramLocus`).
* `RegularizedLogDeterminant` — heat-trace form of `log det'`, its two convergence criteria, and the
  cancellation of `a₀, a₁, h` in a difference.
* `IntegralGronwallAffine` — Grönwall with an *affine* source; the corpus's
  `GronwallVariableCoefficient` only covers a constant source.

## Frontier (what is genuinely not formalizable yet)

Everything that needs a Lean theory of: the Hodge–Kodaira Laplacian on a Kähler manifold, heat
kernels on manifolds (Duhamel, parabolic maximum principle, parametrix), zeta-regularized
determinants (meromorphic continuation of a spectral zeta from a heat-trace expansion), the
determinant of the cohomology, Quillen metrics, the Bismut–Gillet–Soulé anomaly formula,
Bismut–Bost degeneration, semistable reduction, and Riemann–Roch on curves.  Concretely blocked:
Lemmas 2.2/2.4/2.5/2.6, Theorem 2.11, Lemma 4.1, Theorems 3.6–3.8, 3.10, 3.11, 4.4, Cor 4.5,
Prop 5.3, Theorem 5.5, and Theorems 0.2/0.3 as stated.

Next tractable layer: the spectral zeta function.  `RegularizedLogDeterminant` already owns the
`(3.3)` side; what is missing is `Γ(s)ζ(s) = ∫_0^∞ (Θ(t)−h)t^{s−1}dt` and the meromorphic
continuation giving `ζ'(0) = logTorsion`.  Mathlib has `mellin`, `Complex.Gamma`,
`Complex.hasDerivAt_Gamma_one`; the scaled Gamma integral `∫_0^∞ e^{−bx}x^{s−1}dx = Γ(s)/b^s` is
**not** in mathlib and has to be built by change of variables.
