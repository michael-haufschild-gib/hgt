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
