# The explicit formula with the genus kernel, the Weil lag function, and the lag criterion (Lean)

- **ID:** `lag-explicit-formula-lean`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean, unconditional)
- **Parent:** `1-in-progress/weil-lag-function-bochner-form.md`
- **Lean modules (all wired, axioms `[propext, Classical.choice, Quot.sound]`, lint passed):**
  - `HTGeometry.DigammaMittagLeffler` — `hasSum_digammaSeries`, `digamma_eq_tsum`: `ψ(s) = −γ + Σ_{k≥0}(1/(k+1) − 1/(s+k))` for `Re s > 0`, from the corpus's Gauss limit `gauss_digamma` and `H_n − log n → γ`.
  - `HTGeometry.PerronRationalKernels` — Mellin-inversion evaluations on vertical lines: `perron_twoPole` (`(1/2π)∫ X^{σ+it}/((s−a)(s−b)) = (X^a − X^b)/(a−b)` for `X > 1`, `0` for `X ≤ 1`), `perron_doublePole` (`X^a log X`, as the limit `b → a` by dominated convergence), the line-`2` specialisations `perron_lineTwo_basic/_sq/_sub_one_sq/_shift/_threePole`, the integrable majorant `(1+t²)^{−3/4}` and the `two_centre_majorant` `1/((1+|t−γ|)(1+|t|)) ≤ √2(1+|γ|)^{−1/2}((1+t²)^{−3/4} + (1+(t−γ)²)^{−3/4})`.
  - `RHTower.LagExplicitFormula` — constants (`tsum_halfShift_reflect`, `tsum_halfShift_pole`, `hasSum_inv_succ_mul_two_add_three`), the partial-fraction form of `Σ Λ(n)n^{−s}` on `Re s = 2` (`lseries_vonMangoldt_lineTwo`), the Dirichlet side (`dirichlet_side`), the termwise bounds and interchanges (`norm_kTerm_le`, `norm_zTerm_le_majorant`, `integrable_tsum_of_summable_integral_norm'`), and **`lag_explicit_formula`**.
  - `RHTower.WeilLagFunction` — `weilLagFunction`, `weilLagFunction_zero`, `weilLagFunction_neg`, `weilLagFunction_eq_prime_side`, `norm_weilLagFunction_le_of_riemannHypothesis`, `prime_side_lag_bound_of_riemannHypothesis`.
  - `RHTower.WeilLagFunctionOneSided` — `Φ` is real (`weilLagFunction_im_eq_zero`, `weilLagFunctionReal`), the Laplace transform of `Φ` on `Re s > ½` (`integral_weilLagFunction_mul_cexp`), the one-sided measure `(M ∓ Φ)du + du` with its abscissa (`isAbscissa_oneSided`, `abscissa_oneSided_eq_zero` via the corpus Landau theorem), and **`riemannHypothesis_iff_weilLagFunctionReal_bddAbove` / `…_bddBelow`**.
  - `RHTower.WeilLagFunctionCriterion` — zero-set facts (`xi_zero_isolated`, `isDiscrete_xiZeroSet`, `finite_xiZeroSet_inter`, `exists_xiZeroCopy_of_xi_eq_zero`, `exists_xiZeroCopy_re_gt_half_of_not_rh`), the Mittag-Leffler series `lagPoleSeries` (`differentiableAt_lagPoleSeries` off the poles, `norm_lagPoleSeries_ge` at a pole), the window Mellin transform (`mellin_lagWindow` on `Re s > ½`, `differentiableAt_mellin_lagWindow` on `0 < Re s < 2` for bounded `Φ`), and **`riemannHypothesis_iff_weilLagFunction_bounded : RH ↔ ∃ M, ∀ L, ‖Φ L‖ ≤ M`**.

## Statement

For real `X > 1`, with the sum over the nontrivial zeros of `ξ` counted with multiplicity,

```
Σ'_ρ X^ρ/(ρ(1−ρ)) = (X − ψ(X)) + X·(Σ_{n≤X} Λ(n)/n − log X + γ) − log 2π + Σ_{k≥1} X^{−2k}/(2k(2k+1)).
```

Hence, with `Φ(L) = Σ_ρ e^{L(ρ−½)}/(ρ(1−ρ))`, `Φ(L) = e^{−L/2}·[…]_{X=e^L}` for `L > 0`, `Φ(0) = 2+γ−log 4π`, `Φ(−L) = Φ(L)`,
and under RH `|Φ(L)| ≤ Φ(0)`.

## Proof mechanism

Perron integral `(1/2πi)∫_{Re s=2} (−ζ'/ζ)(s) X^s/(s(s−1)) ds`. Dirichlet side: `Σ_n Λ(n)(X/n−1)_+` by the
two-pole kernel `(y−1)_+`. Mittag-Leffler side: `−ζ'/ζ = 1/(s−1) + 1/s + ψ(s/2)/2 − ½log π − Σ_ρ[1/(s−ρ) + 1/(ρ−½)]`
(corpus `xi_explicitFormula_logDeriv`), the digamma series, and termwise residues. The zero terms
`(s−½)/((ρ−½)(s−ρ))·X^s/(s(s−1))` are dominated by `8X²/(|ρ−½|(1+|t−γ|)(1+|t|))`, hence by the two-centre
majorant with `Σ_ρ |ρ−½|^{−3/2} < ∞` (corpus). The digamma terms are dominated by `X²(1+t²)^{−3/4}/(2(k+2)^{3/2})`.
Constants: `Σ_ρ 1/(ρ(1−ρ)) = 2+γ−log 4π`, `Σ_ρ[1/(ρ−½) − 1/ρ] = −(2+γ−log 4π)/2`, `ψ(½) = −γ−2log 2`, `ψ(2) = 1−γ`.

## The criterion

`RH ⟺ Φ bounded` (`riemannHypothesis_iff_weilLagFunction_bounded`), with the bound `Φ(0) = 2+γ−log 4π` under RH; and
the one-sided sharpening `RH ⟺ Φ bounded above ⟺ Φ bounded below` (`WeilLagFunctionOneSided`), by Landau's theorem
applied to the nonnegative density `M ∓ Φ` (the corpus's `false_of_analyticAt_abscissa`) and the absence of real
zeros of `ξ` (`xi_pos_on_real_anchor`). The analytic-extension core is the reusable
`riemannHypothesis_of_lagPoleSeries_extension`. Converse
mechanism: Mellin holomorphy of the bounded window on `0 < Re s < 2` (`mellin_differentiableAt_of_isBigO_rpow`), the
identity with the Mittag-Leffler series on `Re s > ½`, an off-line zero of maximal real part on its horizontal line
(finitely many zeros on a compact segment: `IsCompact.finite` with `isDiscrete_iff_nhdsNE`), and the real-analytic identity
theorem along the pole-free horizontal ray; no planar connectivity argument is needed.

## What it unlocks

Every sharp-cutoff prime criterion of Route O now has a certified prime side, and the criterion form with the sharp constant
built in is closed in Lean: any bound `|Φ| ≤ M` proves RH and then improves itself to `M = Φ(0)`.

## The integer lag law (added)

- `RHTower.WeilLagFunctionInteger` — real prime side `weilLagFunctionReal_eq_prime_side`, the integer lags
  `integerLag n = Φ(log n)` with the explicit formula `integerLag_eq`, `integerLag_one = 2+γ−log 4π`, the interval
  bound `|Φ(L) − a_{⌊e^L⌋}| ≤ 30` for `L ≥ log 2` (`weilLagFunctionReal_integerLag_interval`, via the five monotone
  prime-side pieces, `ψ(n) ≤ 2n log n`, `Σ_{m≤n}Λ(m)/m ≤ log n(1+log n)`, `(log n + 2)² ≤ 36√n`, `S(n) ≤ S(1) = 1 − log 2`),
  and the criteria **`riemannHypothesis_iff_integerLag_bddAbove`**, **`…_bddBelow`**,
  **`riemannHypothesis_iff_integerLag_le_sharp`** (`RH ↔ ∀ n ≥ 2, a_n ≤ 2+γ−log 4π`),
  **`riemannHypothesis_iff_integerLag_le_one`** (`RH ↔ ∀ n ≥ 1, a_n ≤ a_1`),
  **`riemannHypothesis_iff_integerLagInequality`** (the inequality written out), and the dichotomy
  **`integerLag_dichotomy`** (all `|a_n| ≤ a_1`, or unbounded above and below).
- `RHTower.WeilLagFunctionRecurrence` — under RH `Φ(L) = Σ' cos(γL)/(¼+γ²)` (`weilLagFunctionReal_eq_cos_series`,
  `tsum_cosWeight = a_1`), the recurrence **`exists_pow_integerLag_gt_of_riemannHypothesis`** (`∀ b, ∀ ε>0, ∃ m ≥ 1,
  a_1 − ε < a_{b^m}`; corpus `exists_simultaneous_dirichlet` on the ordinates), **`isLUB_integerLag_of_riemannHypothesis`**
  (`a_1` is the exact supremum of `{a_n : n ≥ 2}`), the tail version `isLUB_integerLag_tail_of_riemannHypothesis`
  (every tail `{a_n : n ≥ N}` has supremum `a_1`), the unconditional limit-point theorem
  **`frequently_integerLag_gt`** (`∀ ε > 0, ∃ᶠ n, a_1 − ε < a_n`; so `limsup a_n ≥ a_1` always, `= a_1` iff RH),
  and the package **`integerLag_law`**. Numerics (no proof use): `computations/integer-lag-records/`.

- `RHTower.WeilLagFunctionOmega` — `Φ` as the corpus Bohr exponential series (`weilLagFunction_eq_expSeriesCarrier`,
  `isBohrAlmostPeriodic_weilLagFunction`, `bohrMean_weilLagFunction = 0` via `bohrCoefficient_expSeriesCarrier_of_ne`),
  the non-eventual-nonnegativity `exists_weilLagFunctionReal_le_neg_of_riemannHypothesis` (vanishing lemma +
  `eq_zero_of_bohrMean_eq_zero_of_nonneg`), the sharp interval bound `abs_weilLagFunctionReal_sub_integerLag_le`
  (`≤ 3(log n+2)²/√n`, `tendsto_lagGap`), the unconditional **`frequently_integerLag_le_neg`**, the package
  **`genusKernelError_omega_pm`** (`Ω±(√n)` with the exact positive ceiling), unconditional continuity
  `continuous_weilLagFunction_unconditional`, and **`riemannHypothesis_iff_isBohrAlmostPeriodic_weilLagFunction`**.

- `RHTower.WeilLagFunctionFloor` — `NoOddRelation` (every integer relation among distinct ordinates has even
  coefficient sum), unimodular product bounds (`norm_prod_zpow_sub_one_le`, `norm_prod_zpow_sub_prod_zpow_le`),
  the excess identity `cosWeight_mul_one_add_cos_le`, `noOddRelation_of_forall_exists_lt` (odd relations obstruct the
  floor), `exists_weilLagFunctionReal_lt_of_noOddRelation` and `exists_integerLag_lt_of_noOddRelation` (corpus
  `exists_rat_independent_intSpanning` + `kronecker_approx` + almost periodicity), and the **floor law**
  **`integerLag_floor_law : RH → (IsGLB {a_n : n ≥ 2} (−a_1) ↔ NoOddRelation)`**.

Statement: `RH ⟺ ∀ n ≥ 2: (n − ψ(n)) + n(Σ_{m≤n}Λ(m)/m − log n + γ) − log 2π + Σ_{k≥1} n^{−2k}/(2k(2k+1)) ≤ (2+γ−log 4π)√n`,
and under RH the inequality is tight along `b^m` for every base `b`. Axioms: `[propext, Classical.choice, Quot.sound]`.

- `RHTower.ZetaLogDerivZeroDistance` — the partial-fraction bound for `ζ'/ζ`: `summable_partialFractionTerm`,
  `logDeriv_xi_sub_eq_tsum` (anchor difference `Σ'_ρ ((s−ρ)⁻¹ − (s₀−ρ)⁻¹)`), `logDeriv_zeta_eq_logDeriv_xi`
  (`ζ'/ζ = ξ'/ξ − 1/s − 1/(s−1) − Γ_ℝ'/Γ_ℝ`), `norm_logDeriv_zeta_three_le` (`≤ 2` on `Re s = 3`),
  `norm_logDeriv_Gammaℝ_le` (`≤ log t + 2 + 2π + log 2` on `½ ≤ σ ≤ 3`, `t ≥ 4`), `smallHeightCopies_finite` /
  `smallHeightCount` (`K₀`), `card_zeroWindow_le` (`≤ 80 log(180(t+k+1)) + K₀` on `|t−γ| ∈ [k,k+1)`), the telescoping
  tails `sum_inv_sq_Ico_le`, `sum_log_div_sq_Ico_le` (`≤ 7`), `windowIndex`/`windowWeight`, `norm_term_le_windowWeight`,
  `sum_norm_partialFractionDiff_le`, and **`norm_logDeriv_zeta_le`**: `½ ≤ σ ≤ 2`, `t ≥ 4`, `0 < δ ≤ 1`,
  `∀ ρ, ‖s − ρ‖ ≥ δ` ⟹ `‖ζ'/ζ(σ+it)‖ ≤ (3700 + 5K₀) log t / δ`. STATUS MUST-247.

- `RHTower.WeilLagFunctionSingleBase` — `lagWeight_re_pos` (`Re(1/(ρ(1−ρ))) > 0`), `AttainedTop β₀`, `topLevel`,
  `topWeight` (`> 0` when attained), `lowerTail` + `tendsto_lowerTail` (dominated convergence), `abs_re_lowerPart_le`,
  `norm_exp_phase_sub_one_le` (Dirichlet phase within `2π/Q`), **`exists_pow_integerLag_gt_of_attainedTop`**
  (attained `β₀ > ½` ⟹ `a_{b^m}` unbounded for every `b ≥ 2`), `not_attainedTop_of_forall_le`, `offLineCopies`,
  `exists_attainedTop_of_finite_offLine`, `exists_pow_integerLag_gt_of_finite_offLine`,
  `riemannHypothesis_of_forall_xiZeroCopy_re_eq_half` (public), **`riemannHypothesis_or_infinite_offLine_of_forall_le`**,
  **`riemannHypothesis_or_not_attained_of_forall_le`**. STATUS MUST-248.

- `RHTower.WeilLagFunctionShadow` — nodes `baseNode b q = b^{ρ−½}` with bounds `nodeBound`, generating function
  `lagGen` (analytic on the unit disc under `|a_{b^m}| ≤ M`, `differentiableOn_lagGen`), node series `nodeSeries` with
  the double-series interchange `tsum_tsum_lagWeight_mul_pow` and `lagGen_eq_nodeSeries` near `0`, `aliasSet`/
  `aliasWeight` (`aliasWeight_re_pos`), `regularPart` (`differentiableOn_regularPart` off the poles), the split
  `nodeSeries_split`, `shadowPoles`, **`not_bounded_of_clean_shadow`** (identity theorem on a convex tube around the
  segment `[0, 1/z_{q₀}]`), **`exists_segment_mem_closure_shadowPoles`** (the shadow law), and
  `riemannHypothesis_of_forall_abs_le_of_clean_shadows`. STATUS MUST-249.

- `RHTower.RingRecursionWitness` — the structural counterexample to single-base sufficiency, with rate parameter `l`:
  rings at radii `ringRadius N = e^{−5/√N}`, seeds `ringSeed l m = e^{−lm}`, the divisor recursion
  `ringStep`/`ringPrefix`/`ringData` (`ringWeight l`, `ringFlag l`), the cancellation identity `ringS_add_self`/
  `ringTotal_eq` (`|ringTotal l m| ≤ e^{−lm}`), the bounds `ringRadius_ratio_le` (`(ρ_N/ρ_m)^m ≤ e^{−2√m}`),
  `exp_seed_cost_le` (`e^{5√m−lm} ≤ e^{25/(4l)}`), `exp_seed_cost_le_geom`, `ringWeight_step_le`, `ringWeight_le_bound`
  (`≤ 2e^{25/(4l)}`), `ringWeight_le_majorant`, `summable_ringWeight`; nodes `ringNode l`/`ringNodeWeight l`,
  `sum_rootsOfUnity_pow`, `ring_powerSum`, `tsum_powerSum`, **`exists_positive_configuration_powerSums_le`**
  (unit disc, sums `≤ e^{−lm}`) and **`exists_positive_configuration_bounded_powerSums`** (`R > 1`, sums `≤ 1`).
  STATUS CANNOT-327.

- `RHTower.WeilLagFunctionGrowth` — `re_le_half_add_of_lagPoleSeries_extension` (extension of the lag pole series to
  `Re z > a` ⟹ `Re ρ ≤ ½ + a`), the growth measure `growthMeasure a M` (density `M e^{au} − Φ` plus `e^{au}du`),
  `laplaceMass_growthShift`, `isAbscissa_growth`, `growthContinuation`, `complexLaplace_growth_eq`, `abscissa_growth_eq`
  (Landau), **`re_le_half_add_of_weilLagFunctionReal_le_exp`**. STATUS MUST-250 (i).
- `RHTower.WeilLagFunctionPrimeGap` — gap sums `psi_sub_psi_le`, `mertensSum_sub_le`, the bracket `lagBracket` with
  `abs_lagBracket_le` (`≤ 4k(log k+2)²`) and `abs_lagBracket_sub_le`, **`abs_integerLag_sub_le`** (Lipschitz law),
  `abs_weilLagFunctionReal_sub_integerLag_le_of_gap`, `exists_prime_short_gap` (corpus Hoheisel + Bertrand),
  `gap_factor_le` (`≤ 457776 p^{23/100}`), `exists_growth_bound_of_primeLag_le`, **`re_le_three_quarters_of_primeLag_le`**,
  `one_quarter_le_re_of_primeLag_le`. STATUS MUST-250 (ii)–(iii).

## The prime-power criterion (added 2026-09-06, Lean, `PrimeLagLandauCriterion`)

`riemannHypothesis_iff_primePowerLag_bddAbove : RH ↔ ∃ M, ∀ n, Λ(n) ≠ 0 → integerLag n ≤ M`, and
`riemannHypothesis_of_primePowerLag_le`. Modules (all wired in `RHTower.lean`, axioms `[propext, Classical.choice,
Quot.sound]`):
- `PrimeLagLandauWeights`: `summable_lagWeight_mul_log` (`Σ_q ‖w_q‖ log(2+|γ_q|) < ∞` from the local zero count), the
  two-sided `norm_logDeriv_zeta_le_abs`, `zeroOrdinate_ne_zero'` (unconditional, from `xi_pos_on_real_anchor`).
- `PrimeLagLandauSeries`: `primeLagCoeff M n = (M − a_n)Λ(n)/n`, nonnegative under the hypothesis, `abs_integerLag_le_rpow`
  (`|a_n| ≤ W n^{θ−½}`), `lagCoeff_LSeriesSummable` on `Re s > θ − ½`, the identity `LSeries_lagCoeff_eq`.
- `PrimeLagLandauContinuation`: `landauG`, the box, far-term bound `norm_landauTerm_le_far` (MUST-247), `nearSet`
  finite, `differentiableOn_landauG` on open subsets of the box avoiding the near poles.
- `PrimeLagLandauCriterion`: `zeroReSup`, `landau_transfer_step` (corpus `landau_local_summability_transfer` with
  `σ₁ = Θ−½+η`, `h = η`, `R = 5η/2`), `exists_bound_neg_logDeriv_zeta_sub_inv`, `aliasedWeight` (finite sum over the
  near copies with the same support point, `Re > 0`), `landauG_ray_lower_bound`, `exists_pos_le_ordinate_gap`, the
  maximal-zero + ray identity-theorem contradiction.

## The `k`-th power criterion (added 2026-09-06, Lean, `PowerLagLandau*`)

`riemannHypothesis_iff_powLag_bddAbove (hk : 1 ≤ k) : RH ↔ ∃ M, ∀ m ≥ 1, integerLag (m ^ k) ≤ M`
(`PowerLagLandauCriterion`), for every `k ≥ 1`; no prime-gap input. Modules (wired, axioms clean):
- `PowerLagLandauSeries`: `summable_lagWeight_mul_sqrt` (`Σ ‖w_q‖ √(2+|γ_q|) < ∞`, windows + `winLog_le_rpow_quarter`
  + majorant `powMajorant k = 16(240+K₀) k^{−5/4}`), `powLagCoeff k M m = (M − a_{m^k})/m^k`, `powAbscissa k θ =
  k(θ−3/2)+1`, `powLagCoeff_LSeriesSummable`, `powShift k q u = u + 3k/2 − kρ_q`, `LSeries_powLagCoeff_eq`.
- `PowerLagLandauContinuation`: `powTerm`, `powLandauG`, `sameOrdinate t₀` (finite), `powBox`, `norm_powTerm_le_far`
  (exponent-½ bound `norm_riemannZeta_le_sqrt_norm_add_two_half` with `d = kg/2`), `differentiableOn_powLandauG`
  (hypotheses: `Re u ≥ abscissa − η`, `|Im u − k t₀| ≤ kg/2`, `‖u‖ ≤ B`, `k + u ≠ 1`, same-ordinate arguments `≠ 1`).
- `PowerLagLandauCriterion`: `exists_pos_le_abs_ordinate_all`, `exists_norm_riemannZeta_ge_inv` (`‖ζ(1+t)‖ ≥ 1/(2t)`),
  `powLandau_transfer_step`, `powPole k q₀ = k(ρ₀ − 3/2) + 1`, `powAliasedWeight`, `powLandauG_ray_lower_bound`,
  `exists_small_ray_parameter`, the maximal-zero ray contradiction.
Traps: `field_simp`/`positivity`/`linarith` time out in `set`-heavy contexts — factor scalar steps into standalone lemmas
(`exists_small_ray_parameter`) and introduce constants with `obtain ⟨Bd, hBd⟩ : ∃ Bd, Bd = …`.

## The counting-function law (added 2026-09-06, Lean, `LagCountingFunctionLaw`)

`structure LagWeightSystem` (`c ≥ 0`, `F`, `α`, `η₀`, `A < 1`; fields `hasSum`, `differentiableAt_right`, `far`,
`blowup`) and `LagWeightSystem.riemannHypothesis_iff_lag_bddAbove : RH ↔ ∃ M, ∀ n, c n ≠ 0 → integerLag n ≤ M`.
Internals: `summable_lagWeight_mul_rpow (hA0 : 0 ≤ A) (hA : A < 1)` (`Σ ‖w_q‖ (2+|γ_q|)^A < ∞`, window majorant
`lagRpowMajorant A k = (240+K₀)(2/ε)·4·k^{−(2−A−ε)}`, `ε = (1−A)/4`), `coeff M n = c n (M − a_n)`, `shift q s = s − ρ_q + ½`,
`absc θ = α + θ − ½`, `LSeries_coeff_eq`, `coeff_LSeriesSummable`, `term`, `G`, `norm_term_le_far`, `exists_far_const`,
`differentiableOn_G` (hypotheses: `absc θ − η ≤ Re s ≤ α + 3/2`, `|Im s − t₀| ≤ g/2`, `F` differentiable at `s` and at
the same-ordinate shifts), `transfer_step`, `pole q₀ = α + ρ₀ − ½`, `G_ray_lower_bound` (`‖W₀‖‖F(α+t)‖ − C`), the
final contradiction via `blowup`. Reuses `powAliasedWeight`, `sameOrdinate`, `powBox`, `exists_pos_le_ordinate_gap_all`
from the `k`-th power modules. STATUS MUST-253.

## The prime-only criterion (added 2026-09-06, Lean, `PrimeLagLandauPrimesOnly`)

`riemannHypothesis_iff_primeLag_bddAbove : RH ↔ ∃ M, ∀ p, p.Prime → integerLag p ≤ M` and the sharp
`riemannHypothesis_iff_primeLag_le_sharp` (constant `poleSharpConstant = 2 + γ − log 4π`). Bricks: `IsProperPrimePow`,
`isProperPrimePow_iff` (`∃ p prime, ∃ j, n = p^(j+2)`), `properPowMap` injective (`Nat.Prime.pow_inj`),
`rpow_neg_le_three_quarters`, `summable_shifted_geometric`, `properLogTerm`, `summable_properMajorant`
(`summable_prod_of_nonneg` over `Nat.Primes × ℕ`), `summable_properPrimePow_log_rpow (hx : 1/2 < x)`,
`primeOnlyCoeff`/`properCoeff` with `primeLagCoeff = primeOnlyCoeff + properCoeff`, `properCoeff_LSeriesSummable`
(`Re s > θ − 1`), `differentiableAt_LSeries_properCoeff`, `primeOnlyG M = landauG M − LSeries properCoeff`,
`differentiableOn_primeOnlyG`, `primesOnly_transfer_step`, the ray bound `‖W₀‖/t − (C + B_T)`. STATUS MUST-254.
