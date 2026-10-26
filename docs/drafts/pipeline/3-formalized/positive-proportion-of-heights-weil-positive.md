# A positive proportion of heights is Weil-positive for a whole class of tests

- **ID:** positive-proportion-of-heights-weil-positive
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** B1.4 (selection), walls ledger 3.14 ("Need: a selection theorem"); frontier map row
  "Averaged positivity" (individual heights). The corpus had positive-measure positive frequencies
  per test on `[Γ, 2Γ]`; here the set of heights does not depend on the test.
- **Statement.** There are `c > 0`, `C`, `Γ₀` such that for `Γ ≥ Γ₀`, `Γ^{99/100} ≤ H ≤ Γ/8`, `A ≥ 0`,
  `η > 0` there is `S ⊆ [Γ, Γ+H]` with `|S| ≥ cH/(A+1) − CH/(η log Γ)` such that for every `γ ∈ S`
  and every nonnegative `F₀ ∈ C²_c([−A,A])`:
  `Q(F₀ cos γ·) + Q(F₀ sin γ·) ≥ (∫F₀)²/4 − 4η(A+1)² e^A N(F₀)²`.
  For each nonnegative test with `16η(A+1)²e^A N(F₀)² < (∫F₀)²` the Weil form is positive on all of `S`.

## Lean
`formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/APositiveProportionOfHeightsIsWeilPositive.lean`:
`half_integral_le_norm_paperFT_depthSumProfile`, `quarter_sq_integral_sub_offLineField_le_fullZeroForm`,
`le_volume_biUnion_of_overlap`, `exists_shortWindow_positiveProportion_heights_weilPositive`.
Axioms: `propext`, `Classical.choice`, `Quot.sound`. Wired into `ArithmeticCastelnuovoSeveri.lean`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized

## Proof
1. If a zero `ρ` has `|Im ρ − γ|·A ≤ 1`, then for `F₀ ≥ 0` on `[−A,A]`:
   `Re F̂(depthSum_ρ)(−γ) = ∫F₀(u) cosh(δu) cos((Im ρ − γ)u) du ≥ (1/2)∫F₀`, since
   `cos x ≥ 1 − x²/2 ≥ 1/2` for `|x| ≤ 1`. Keeping `ρ` in the quadrature and bounding the depth
   differences by the off-line field: `Q_γ(F₀) ≥ (∫F₀)²/4 − 4(A+1)²e^A N² Φ(γ)`.
2. Let `Z` be the zero copies with ordinate in `(Γ+H/4, Γ+3H/4]` (`#Z ≥ H log Γ/(16π)`) and
   `U = ⋃_{q∈Z} [Im q − r, Im q + r]`, `r = 1/(A+1)`. Each height lies within `r` of at most
   `K log Γ` ordinates (`N(γ+1) − N(γ−2) ≤ (3/2π + 2C) log(γ+1)`), so
   `2r #Z = ∫ Σ_q 1_{I_q} ≤ K log Γ |U|`: `|U| ≥ H/(8πK(A+1))`.
3. `S = U ∖ {Φ > η}`; `|{Φ > η} ∩ [Γ,Γ+H]| ≤ CH/(η log Γ)` (`exists_volume_offLineField_gt_le`).

## Subsumed
In the only aperture range where this bound yields positivity, `(A + 1)² e^A ≪ log Γ`, the
single-height law `zetaZeroConfig_re_W_heightShift_nonneg_of_sharp_horizon` already gives
`Q_γ(F₀) ≥ 0` at every height `log(1 + γ/8) ≥ C + (4 + ε)e^A + 2` for every test (tail conditions
aside). Not a contribution to the selection obstacle, which lives at logarithmic aperture.
