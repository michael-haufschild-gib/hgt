# Abscissa dictionary and strict multiplicity grading for `1/ζ`-type receivers

- **ID:** abscissa-strict-multiplicity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Opus loop rows 663, 676–681, 684–689 (`1-in-progress/rh-goal-loop-opus-2026-09-29.md`); STATUS CANNOT-500/501, MUST-882–886
- **Statement:** (i) Abscissae of convergence of signed, pole-free arithmetic Dirichlet series encode the zero-free half-plane, while nonnegative ones are pinned at 1. (ii) Little-`o` polylogarithmic bounds for `1/ζ`-type receivers cap the order of every zero on the abscissa line strictly below `a + 1`; at `a = 0` this gives unconditional Ω-results.

## Goal
These map exactly which receiver forms are RH-equivalent (ε-lossy, multiplicity-blind) and which overshoot to RH ∧ multiplicity bounds (log-sharp `1/ζ` forms). They also correct two frontier claims (DR, PBM).

## Gates
- [x] 0 → 1 in-progress
- [x] 1 → 2 fully-proven (paper proofs in the loop rows)
- [x] 2 → 3 formalized: all modules build with `lake --old build`, `#print axioms` = `[propext, Classical.choice, Quot.sound]`, wired into `GaloisForLFunctions.RHTower`
- [ ] 3 → 4 publication-ready

## Lean theorems (module : declarations)
- **Nonnegative series are pinned at 1** (CANNOT-500/501).
  - `RHTower/LogZetaDirichletDivergence`: `not_dirichletConvergesAt_logZetaShiftedCoeff`, `summable_of_dirichletConvergesAt_of_nonneg`, `not_dirichletConvergesAt_primeIndicator`.
- **Signed, pole-free abscissa laws** (MUST-882/883).
  - `RHTower/VonMangoldtMinusOneAbscissa`: `xiZeroHalfPlaneBound_iff_vonMangoldtMinusOne_converges`, `riemannHypothesis_iff_vonMangoldtMinusOne_converges`.
  - `RHTower/SignedArithmeticAbscissaRH`: `forall_halfPower_bound_iff_forall_converges`, `exists_abs_sum_range_le_of_converges` (Kronecker), `riemannHypothesis_iff_moebius_converges`, `riemannHypothesis_iff_liouville_converges`.
  - `RHTower/RegularizedLogZetaAbscissa`: `partialSumPowerBound_iff_convergesRightOf`, `PartialSumPowerBound.log_weight`, `.inv_log_weight`, `xiZeroHalfPlaneBound_iff_logZetaRegCoeff_converges`, `xiZeroHalfPlaneBound_iff_primeRegCoeff_converges`.
  - Prior art for general exponents: the `zetaZeroAbscissa` family (`ZetaZeroAbscissa`, `MobiusMertensAbscissaLittlewood`, `*ExponentLaw`).
- **One-sided Liouville** (MUST-882).
  - `RHTower/LiouvilleExponentialSumOneSidedPower`: `zetaResidueUnit_ne_zero_of_liouvilleExpSum_lower_rpow`, `riemannHypothesis_iff_forall_liouvilleExpSum_lower`.
- **Strict multiplicity grading** (MUST-884/885/886).
  - `RHTower/MertensPolylogStrictMultiplicity`: `riemannHypothesis_and_order_lt_of_mertens_littleO`, `riemannHypothesis_and_simple_of_weighted_moebius_converges` (single point `s = ½`), `not_moebius_div_sqrt_converges`.
  - `RHTower/RayPolylogMultiplicity` (abstract): `natCast_lt_of_ray_littleO`, `norm_integral_Ioi_one_cpow_mul_le`.
  - `RHTower/RieszFunctionStrictMultiplicity`: `riemannHypothesis_and_order_lt_of_rieszLittleO`, `not_rieszLittleO_zero`.
  - `RHTower/HardyLittlewoodStrictMultiplicity`: `riemannHypothesis_and_order_lt_of_hardyLittlewoodLittleO`, `not_hardyLittlewoodLittleO_zero`.
  - `RHTower/MertensFrontierMultiplicityOmega`: `natCast_order_lt_of_mertens_littleO_at`, `not_mertens_littleO_zetaZeroAbscissa_of_le_order`, `not_mertens_littleO_zetaZeroAbscissa` (unconditional, at the true frontier `Θ`).
  - `RHTower/MertensFrontierOneSidedOmega` (MUST-888, row 691): `natCast_order_le_of_mertens_oneSided`, `not_eventually_mertens_oneSided_zetaZeroAbscissa`, `exists_mertens_omega_pm_zetaZeroAbscissa` (one-sided graded Ω± at `Θ`, unconditional); big-`O` ray lemmas `norm_le_of_ray_bigO`, `eq_zero_of_ray_bigO_lt`.
- **`ζ(2s)`-denominator receivers: the halving cascade** (MUST-889/890, rows 692, 694).
  - `RHTower/SquarefreeDiscrepancyZeroCascade`: `riemannZeta_half_eq_zero_of_bound`, `riemannZeta_ne_zero_of_squarefree_bound` (zero-free band `2α < Re s < 2 − 4α` from `|E| ≤ Cx^α`), `riemannHypothesis_of_squarefree_quarter_bound`, `not_squarefree_bound_of_lt_quarter`.
  - `RHTower/SquarefreeDiscrepancyQuarterOmega`: `natCast_lt_of_squarefree_littleO`, `not_squarefree_littleO_of_le_order`, `not_squarefree_littleO_quarter` (`E ≠ o(x^{¼})`, unconditional).
  - **RH-equivalence (MUST-891, rows 695–696).** `RHTower/SquarefreeExponentialCascade` (receiver via `Γ(ρ/2) ≠ 0` + shared cascade `riemannZeta_ne_zero_of_halving`), `RHTower/SquarefreeExponentialRH`: `riemannHypothesis_iff_squarefree_exponential` (RH ⟺ `Σμ(n)²e^{−nt} = (6/π²)/t + O(t^{−¼−ε})`), `abs_profile_sub_le_of_mertens` (Mertens exponent `θ` ⟹ smoothed squarefree exponent `θ/2`).
  - **Exponent law and one-sided forms (MUST-892/893, rows 697–698).** `RHTower/SquarefreeExponentialExponentLaw`: `expBound_zetaZeroAbscissa` (exponent `≤ Θ/2`), `not_expBound_of_lt_half_zetaZeroAbscissa` (exact when `Θ ≤ 2/3`, the cascade fixed point). `RHTower/SquarefreeExponentialOneSided`: `riemannHypothesis_iff_sqfError_upper`, `riemannHypothesis_iff_sqfError_lower`, `riemannZeta_ne_zero_of_sqfError_oneSided`.
  - **General dilation and Ω± (rows 700–701, MUST-894).** `RHTower/ZetaDilationCascade`: `riemannZeta_ne_zero_of_dilation` (any `k > 1`), `band_contains_iff` (frontier reachable iff `Θ < k/(k+1)`). `RHTower/SquarefreeExponentialOmega`: `exists_sqfError_omega_pm` (`Ω±(t^{−¼})`, unconditional), `norm_H_le_of_oneSided`.
  - **The quasi-RH ladder (rows 702–705, MUST-895).** `RHTower/ZetaBranchingDilationCascade`: `riemannZeta_ne_zero_of_branching` (IFS of reflected contractions). `RHTower/KFreeExponentialMellin` (`mellin_kProfile`: `Γ(s)ζ(s)/ζ(ks)`), `RHTower/KFreeExponentialCascade` (`riemannZeta_ne_zero_of_kBound`), `RHTower/KFreeExponentialLadder` (`abs_kProfile_sub_le_of_mertens`, `zeroFree_strip_iff_kFree`: zero-free on `Re s > 1 − 1/k` ⟺ smoothed `k`-free error `O(t^{−(k−1)/k²−ε})`).

## Reframing: faithfulness of integral Euler-product receivers
- Every Euler product with integral local factors is `∏_k ζ(ks)^{b_k}` (necklace factorization of `F(x) = ∏_k(1−x^k)^{−b_k}`). Squarefree: `ζ(s)/ζ(2s)`. Squarefull: `ζ(2s)ζ(3s)/ζ(6s)`. `k`-free: `ζ(s)/ζ(ks)`.
- A power bound on the counting error at exponent `α` forces the zeros of the dilated denominators to be cancelled by zeros of dilated numerators: `ρ ↦ ρ·j/k` with `b_k < 0 < b_j`. Reflection then gives `z ↦ 1 − (j/k)z`.
- When all such maps contract (`j < k`), the orbit converges to the real segment, where `ζ ≠ 0` (`riemannZeta_ne_zero_of_dilation`, `riemannZeta_ne_zero_of_branching`). The receiver is faithful exactly on the invariant band, and its exponent law is exact only up to the attractor (`k/(k+1)` for `k`-free).
- Mertens (`k = 1`, reflection only) is faithful everywhere. Smoothing with a weight whose Mellin transform is zero-free (`Γ`) removes the lattice-point overshoot of sharp counts (MUST-891).

## Approach
- **Abscissae.** For real coefficients and `θ ≥ 0`, convergence at every real `σ > θ` is the growth class "partial sums `O(N^{θ+δ})` for every `δ > 0`" (Abel summation one way, Kronecker the other). This class is stable under the weights `log n` and `1/log n`. Nonnegative coefficients make convergence absolute.
- **Grading.**
  - The transform of a `1/ζ`-type receiver satisfies `F·E = H` near a zero `ρ`, with `E` the zeta unit (order `m` at `ρ`) and `H(ρ) ≠ 0`.
  - A little-`o` polylog bound at the abscissa gives `‖F(ρ+r)‖ ≤ ηr^{−(a+1)} + C_η`, via the pointwise inequality `(1+log x)^a ≤ (2/r)^aK_a x^{r/2}`.
  - If `m ≥ a+1`, then `r^m F → 0` forces `H(ρ) = 0`.

## No-go closure
- **Killed claims.** DR's "`Σ Λ(n)n^{−s}/log n` converges on `½ < Re s < 1` iff RH" and PBM's "`Σ_p p^{−s}` convergent on `Re s > ½` iff RH" are false (abscissa 1, unconditionally).
- **Positive survivor.** The pole-regularized series above, formalized.
- **New insight.**
  - The pole at `s = 1` is the whole monodromy; after subtracting it, prime, `log ζ` and `ζ′/ζ` sources carry the same exponent.
  - The multiplicity grading is a property of `Γ/ζ`-type transforms, not of RH. It holds at the true frontier `Θ` unconditionally.

## Log
- 2026-10-10 — created at stage 3; all listed modules built and wired the same day.
