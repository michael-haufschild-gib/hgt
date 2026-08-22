# Dai–Yoshikawa, *Degeneration of Riemann surfaces and small eigenvalues* (arXiv:2509.06151v2)

Card: `docs/drafts/pipeline/1-in-progress/dai-yoshikawa-degenerating-riemann-surfaces-small-eigenvalues.md`
Lean: `formal/GaloisForLFunctions/HTGeometry/DaiYoshikawa/` — **29 modules**, all wired into the
`GaloisForLFunctions.HTGeometry` umbrella, every theorem audited to `propext`, `Classical.choice`,
`Quot.sound` only.

## Closed (stage 3)

| Paper item | Lean name |
|---|---|
| Lemma 1.1 (Rayleigh comparison) | `mul_isGLB_le_isGLB_of_le` |
| Lemma 3.2 (gap transfer across comparable metrics) | `le_of_comparable_gap` |
| Prop 6.1 min–max step (disjoint supports) | `sum_sq_mul_le_of_le` |
| `sup_{x≥0} xᵐ e^{−x/a} = (ma)ᵐe^{−m}`, attained | `isGreatest_pow_mul_exp_neg_div` |
| Gaussian-decay absorption (2.10)–(2.13) | `exp_neg_sq_div_div_pow_le` |
| Lemma 2.1 (spectral Cauchy–Schwarz) | `tsum_eigenvalue_heat_mul_le` |
| Lemma 2.3 (antitone + extension step) | `le_mul_add_one_of_antitoneOn` |
| Lemma 2.8/Prop 2.10 Duhamel Gaussian constant | `integral_duhamelGaussian_mul_inv`, `integral_gaussian_pi` |
| Lemma 3.1 (smooth convex cut) | `convexOn_cutPrimitive`, `cutPrimitive_eq_zero`, `cutPrimitive_eq_add` |
| Lemma 3.3 / Cheng–Li (any `n`) | `heatTrace_eigenvalue_pow_bound`, `_linear_bound`, `_sqrt_bound` |
| Prop 3.5 (2) uniform spectral tail | `tsum_spectral_tail_le` |
| Thm 3.9 constant `c = −(N−1)γ` and identity | `tendsto_expIntegralE1_add_log`, `sum_expIntegralE1_eq` |
| Thm 3.9/3.10 domination `Σ e^{−c√k}` | `summable_exp_neg_mul_sqrt` |
| §3.1 (3.3) + cancellation (3.19) | `logTorsion`, `logTorsion_sub_logTorsion` |
| §3.1 Mellin side | `gamma_mul_tsum_rpow_neg_heatTrace`, `integral_exp_neg_mul_rpow` |
| §3.1 continuation | `differentiableAt_mellinHead/Tail`, `mellin_eq_mellinHead_add_mellinTail`, `mellinHead_eq_regularized_add` |
| §3.1 `ζ'(0)` | `hasDerivAt_zetaCont_zero`, `deriv_zetaCont_zero_ofReal` |
| Prop 5.1 (1) — sharp form | `exists_continuous_annulusPeriodRemainder` |
| Prop 5.1 (2), (3) | `substCoeff_zero_zero_eq_zero_of_residue`, `gramMatrix_posDef_of_linearIndependent` |
| Prop 5.2 determinant asymptotic | `tendsto_det_blockPencil_div`, `tendsto_log_det_blockPencil_sub` |
| Lemma 6.2 (Jacobi ideal) | `pow_sum_normSq_le_of_jacobi_relation` |
| Lemma 6.3 (affine-source Grönwall) | `le_affine_gronwall_of_volterra_bound` |
| Lemma 6.6 (3) `= 4π/log ε⁻¹` | `setIntegral_logCutoff_energy` |
| §7 product law ⟹ two-sided bounds | `le_of_prod_le_of_le_div` |
| Corollary 0.4 | `log_inv_le_and_le_of_rpow_bounds`, `le_div_of_le_mul_add` |
| Appendix Lemma 10.1 arithmetic | `gaussBonnet_normalization_incompatible` |

## Reusable bricks (mathlib gaps closed here)

* `PowerExpSup` — the one extremal inequality behind every `B, B', B'_m, B(n)`, plus the trade of
  `s^{−m}` against half a Gaussian.
* `AnnulusMonomialIntegral` / `AnnulusLaurentPairing` — `∫_{a<|z|<b} z^j z̄^{j'}|z|^{−2}dA` fully
  evaluated: `0` off-diagonal, `2π log(b/a)` at `j=0`, `2π(b^{2j}−a^{2j})/(2j)` otherwise.  The
  general engine for logarithmic period divergence over a vanishing cycle.
* `BlockDeterminantGrowth` — `det(L·Ã + B̃ + o(1))/L^{#κ} → det B · det A`, over any `RCLike`.
* `GramPositiveDefinite` — Gram matrix of a linearly independent family is `PosDef`.
* `SpectralZetaMellin` — `∫_0^∞ e^{−bx}x^{s−1}dx = Γ(s)/b^s` (**not** in mathlib).
* `MellinHalfLine` / `MellinSplit` / `MellinHeadExpansion` — half-line Mellin transforms, their
  holomorphy, the split at `t=1`, and the extraction of the poles `a₀/(s−1)`, `(a₁−h)/s`.
* `RegularizedLogDeterminant` + `SpectralZetaDerivative` + `SpectralZetaTorsionBridge` — a complete
  abstract zeta-regularized log-determinant layer from a heat trace with a two-term expansion.
* `IntegralGronwallAffine` — Grönwall with an *affine* source (the corpus's
  `GronwallVariableCoefficient` only covers a constant source).

## A correction found

The computation gives `ζ'(0) = H(0)+T(0) − a₀ + (a₁−h)γ`.  The paper's (3.3) prints the constant as
`−Γ'(1)(a₀−h) = (a₀−h)γ`.  Nothing downstream depends on it: only differences of two torsions with
identical `a₀,a₁,h` are used, and the constant cancels (`logTorsion_sub_logTorsion`).

## Frontier

Blocked on theories that do not exist in mathlib: Hodge–Kodaira Laplacians on Kähler manifolds,
manifold heat kernels (Duhamel, parabolic maximum principle, parametrix), the determinant of the
cohomology, Quillen metrics, the Bismut–Gillet–Soulé anomaly formula, Bismut–Bost degeneration,
semistable reduction, Riemann–Roch on curves.  Concretely: Lemmas 2.2/2.4/2.5/2.6, Theorem 2.11,
Lemma 4.1, Theorems 3.6–3.8, 3.10, 3.11, 4.4, Cor 4.5, Prop 5.3, Theorem 5.5, and Theorems 0.2/0.3
as stated.

One small remaining link inside the zeta chain: the *complex*-`s` version of
`Γ(s)ζ(s) = mellin(Θ−h)(s)` (the real-`s` version is `gamma_mul_tsum_rpow_neg_heatTrace`).
