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

`RH ⟺ Φ bounded` (`riemannHypothesis_iff_weilLagFunction_bounded`), with the bound `Φ(0) = 2+γ−log 4π` under RH. Converse
mechanism: Mellin holomorphy of the bounded window on `0 < Re s < 2` (`mellin_differentiableAt_of_isBigO_rpow`), the
identity with the Mittag-Leffler series on `Re s > ½`, an off-line zero of maximal real part on its horizontal line
(finitely many zeros on a compact segment: `IsCompact.finite` with `isDiscrete_iff_nhdsNE`), and the real-analytic identity
theorem along the pole-free horizontal ray; no planar connectivity argument is needed.

## What it unlocks

Every sharp-cutoff prime criterion of Route O now has a certified prime side, and the criterion form with the sharp constant
built in is closed in Lean: any bound `|Φ| ≤ M` proves RH and then improves itself to `M = Φ(0)`.
