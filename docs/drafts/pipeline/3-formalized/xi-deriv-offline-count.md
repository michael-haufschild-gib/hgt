# Differentiation does not create off-line zeros: ξ′ versus ξ between good heights

- **ID:** XI-DERIV-OFFLINE-COUNT
- **Stage:** 3-formalized
- **Type:** THEOREM (unconditional; windowed Laguerre–Pólya principle for `ξ`)
- **STATUS:** MUST-604
- **Parent:** `1-in-progress/rh-goal-loop-opus-2026-09-29.md`, cycle 74; uses MUST-600 (unshadowed heights), corpus
  strict disk criterion, Zeta23

## Statement

**Good heights.** `T` is good if it is unshadowed (MUST-600), `ξ(½+iT) ≠ 0` and `ξ'(½+iT) ≠ 0`.

**Theorem A.** For good heights `T₁ < T₂`, the numbers of zeros (with multiplicity) of `ξ'` and of
`ξ` in `R = [−1, 2] × [T₁, T₂]` differ by at most 3.

**Theorem B.** In the same window:
- #distinct on-line zeros of `ξ'` ≥ #distinct on-line zeros of `ξ` − 1 (Rolle for `Ξ(t) = ξ(½+it)`).
- Hence #off-line zeros of `ξ'` ≤ #off-line zeros of `ξ` + (on-line multiplicity excess of `ξ`) + 4.

## Proof of A

- Let `g = ξ'/ξ`. On `∂R` it stays in closed half-planes:
  - right edge `σ = 2`: `Re g > 0`;
  - left edge `σ = −1`: `Re g < 0`, by `g(1−s) = −g(s)`;
  - horizontal edges at good `T`: `Re g > 0` for `σ > ½` (strict disk criterion; unshadowed) and
    `Re g < 0` for `σ < ½` (reflection);
  - at `σ = ½`: `g = i y` with `y ≠ 0`, since `g(conj s) = conj g(s)` and `g(1−s) = −g(s)` make `g`
    purely imaginary on the line.
- Split the boundary into six segments. On each, `±g` has nonnegative real part and lies in the slit
  plane, so `Im log(±g)` is a primitive with values in `[−π/2, π/2]`. Each segment contributes at
  most `π`.
- The argument principle for the entire `ξ'` and `ξ` gives `2π|N(ξ') − N(ξ)| ≤ 6π`.

## Lean status [L] (clean, standard axioms, wired)

- `R:RectangleHalfPlaneSegmentsWinding`.
  - `abs_sum_analyticOrderAt_sub_le_three`: the generic six-segment winding bound.
  - Edge primitives: `integral_re_logDeriv_vertical_eq_of_slitPlane`, `integral_im_logDeriv_horizontal_eq_of_slitPlane`.
- `R:XiDerivOffLineCount`.
  - `XiGoodHeight`.
  - Theorem A: `exists_abs_count_deriv_xi_sub_xi_le`.
  - Rolle on the line: `exists_deriv_xi_criticalLine_eq_zero`.
  - Counting lemma: `exists_finset_between_card`.
  - Theorem B: `offLine_count_deriv_xi_le`.

## Remarks

- Good heights are dense in the unshadowed set, since only countably many heights are excluded. Unshadowed heights have density ≥ 58%.
- Unconditional literature for comparison:
  - Conrey (1983) proves more than 79% of the zeros of `ξ'` on the line via Levinson's method.
  - The windowed inequality here transfers any on-line proportion for `ξ` to `ξ'`, e.g. Zeta23's 2/3.
  - That transfer has not been assembled yet: it needs the Zeta23 windows to match good heights.
- Under RH, Theorem B is consistent with `deriv_xi_zero_re_eq_half_of_re_zeros` (all ξ′ zeros on the line).

## Addendum (cycle 75): extra critical points of Ξ [L]

`extraCritical_add_offLine_count_deriv_xi_le`. With `E = (#on-line zeros of ξ', with multiplicity) − (A − 1) ≥ 0`, the critical points of `Ξ` beyond Rolle's minimum:
`E + #off-line zeros of ξ' ≤ #off-line zeros of ξ + (on-line multiplicity excess) + 4`, between good heights.

A positive local minimum or negative local maximum of Hardy's `Z` contributes at least 2 to `E`. So the violations of the critical-point sign law `ZZ'' ≤ 0` at `Z' = 0` (the near-double loop's reformulation of the open core) are paid for by off-line zeros of `ξ`, up to on-line multiplicity excess and 4, in every good window.

## Addendum (cycle 76): the two-sided accounting law [L]

`extraCritical_add_offLine_count_deriv_xi_le` now has both bounds. Between good heights,
`E + O' = O + (M − A) + θ` with `θ ∈ [−2, 4]`, where:
- `E` is the critical points of `Ξ` beyond Rolle's minimum;
- `O`, `O'` are the off-line zero counts of `ξ` and `ξ'`;
- `M − A` is the on-line multiplicity excess of `ξ`.

Heuristic sharpness: a complex pair `γ ± ib` of `Ξ` replaces two real zeros by a wrong-sign local extremum (two extra critical points), so `E ≈ O` and `O' ≈ 0`. Hence no strengthening `E ≥ cO` with `c > 1` can hold, and the law cannot by itself exclude off-line zeros. Verdict on the conjecture "off-line zeros force more than one extra critical point each": dead, since the accounting is sharp.

## Addendum (loop cycle 107): two thirds of the zeros of `ξ'` lie on the critical line [L] — MUST-626

Module `R:XiDerivCriticalLineProportion`.

- `exists_deriv_xi_criticalLine_finset`: for every `T` there is a set `C` of ordinates `0 < c ≤ T` with `ξ'(½+ic) = 0` and `#C + 1 ≥ N₀ˢ(T)`. The proof is Rolle between consecutive distinct critical zeros of `ξ` (`exists_deriv_xi_criticalLine_eq_zero`, `exists_finset_between_card`).
- `eventually_deriv_xi_criticalLine_count_ge`: for every `ε > 0` and all large `T`, `#C ≥ (HD 1 − ε)N(T) − 1`, with `HD 1 = 0.6725…`, via Zeta23 (`lamzouri_montgomeryTaylor_simpleCritical_epsilon`).

## Addendum (loop cycle 108): every derivative of `Ξ` [L] — MUST-627

Module `R:XiHigherDerivRealZeros`.

`eventually_iteratedDeriv_Xi_zeros_ge k`: for every `k`, every `ε > 0` and all large `T`, `Ξ^{(k)}` has at least `(HD 1 − ε)N(T) − k` distinct zeros in `(0, T]`.

Tools:
- `contDiff_Xi`.
- `exists_deriv_zeros_card`: Rolle loses at most one zero.
- `exists_iteratedDeriv_Xi_zeros`.
