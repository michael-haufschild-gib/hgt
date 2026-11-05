# Mixed depths hide beyond the Ingham scale

- **ID:** zcg-mixed-depths-hide-beyond-ingham
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** formal/GaloisForLFunctions/ZeroConfigurationGeometry/README.md §6 Q2 · card `zcg-deep-hiding-at-ingham-scale` (5-failed)
- **Statement:** For `L ≥ 734` and `g = 2π/L` there are tempered, disjoint, nonempty configurations
  `Z, Z'`. Their union is separated at `g` apart from FE partners, and they are mimics at every
  aperture `a < 5π/(6g)`, above the Ingham scale `π/(2g)`. A simpler pair hides up to `2π/(3g)`.

## Goal
Decide whether the Ingham scale resolves separated configurations at every depth. It does at one
depth (`eq_of_mimic_of_oneDepth`); this theorem shows it does not for mixed depths.

## Proof
Write `ℓ = L/6`, so the ordinate period is `6g = 2π/ℓ`.
1. **Columns.** The column of FE pairs `½ ± δ + i(6j + r)g` with multiplicity `n` has image
   `n ℓ Σ_m k(mℓ) e^{irmπ/3} (e^{δmℓ} + e^{−δmℓ})` with `k = f ⋆ f̃`. This is Poisson summation for
   the translated lattice (`hasSum_paperFT_translate`). Disjoint superpositions add their image
   series.
2. **Seven lags.** For `tsupport f ⊆ [−a, a]` with `a < 2ℓ`, `k(mℓ) = 0` for `|m| ≥ 4`. So the image
   is `ℓ Σ_{|m|≤3} k(mℓ) D(m)` with `D(m) = Σ_r n_r e^{irmπ/3} 2cosh(mx_r)`, `x_r = δ_r ℓ`.
3. **The configurations.** Let `P = (367/6, 8, 5/3, 3/2)` at the residue classes `0, ±1, ±2, 3`,
   and `x_r = arcosh P_r`, so `δ_r = 6x_r/L ≤ ½` for `L ≥ 734`. `Z` has multiplicities `29, 6016`
   (each of `±1`) and `89929` at the classes `0, ±1, 3`. `Z'` has multiplicity `50995` at each of
   `±2`.
4. **Symbols.** With `c_k = cos(kπ/3)` and `cosh(mx) = T_m(P)`, the identity
   `29 T_m(367/6) + 12032 c_m T_m(8) + 89929 c_{3m} T_m(3/2) = 101990 c_{2m} T_m(5/3)` holds for
   `m = 0, …, 3`. At `m = 3` it reads
   `716603833/27 − 24352768 − 809361 = 37226350/27 = 101990 · 365/27`. The imaginary parts cancel
   within the pairs `±r`, and `sin(mπ) = 0`.
5. **Separation.** All points have ordinates in `gℤ`, and the depth is a function of the ordinate
   index mod 6. Two points at one height are equal or FE partners.

## Five lags
Allow an on-line class (`P = 1`). With rows `m ≤ 4` the `5 × 4` matrix must have rank `≤ 3`,
which is two conditions. On the slice `P₀ = 1` (residue `0` on-line) the two `4 × 4` minors have
a common factor curve in `(P₁, P₃)`. One component is a plane quartic with rational double points
`(½, ½)` and `(1, −½)`. Lines through `(½, ½)` turn it into `y² = 4t⁴ − 4t³ + 9t² + 12t + 4`,
which has the rational point `t = 85/14`. That gives `P₁ = 11381/3358`, `P₃ = 30292/1679`, and
then `P₂ = 2131/73` with integer null vector `(−322435047274, 155314585150, 1311418449,
9183040076)`.

The configuration `Z₄` consists of off-line columns at `±1, ±2, 3` with multiplicities
`155314585150, 1311418449, 9183040076`. `Z₄'` is the on-line column at residue `0` with
multiplicity `644870094548`. For `|m| ≤ 4`,
`155314585150 · 2c_m · 2T_m(P₁) + 1311418449 · 2c_{2m} · 2T_m(P₂) + 9183040076 · c_{3m} · 2T_m(P₃)
= 644870094548`, so the symbol of `Z₄` is constant. A window of aperture `a < 5ℓ/2 = 5π/(6g)`
sees only these lags. Lean: `lineColumn`, `hasSum_Wsummand_lineColumn`, `lagSum_line_eq`,
`mixed4_symbol_eq`, `mixedZ4`, `mixedZ4'`, `mixedDepth_mimics_to_five_sixths`,
`not_eq_of_mimic_below_five_sixths`.

**Sharpness.** At `m = ±5` the symbol difference is
`−36469449013318963017129111481200/25223062072031 ≠ 0` (Chebyshev `T₅`, `cosh 5x = 2cosh x cosh 4x
− cosh 3x`). The test `κ_w(t + 5ℓ/2) − κ_w(t − 5ℓ/2)` with `w < ℓ/8` has kernel
`2K(y) − K(y + 5ℓ) − K(y − 5ℓ)`, which at the lags `mℓ`, `|m| ≤ 5`, is nonzero only at `0, ±5`. So
for every `a > 5π/(6g)` it separates `Z₄` from `Z₄'` (`mixedZ4_W_sub`, `phiZ4_sub_five`,
`mixedDepth_five_sixths_sharp`). With `eq_zero_of_lagSymbol_eq_zero` no period-`6` pattern hides
above `5π/(6g)`.

## The period-6 system
The weights solve the `4 × 4` linear system `Σ_r w_r C_r T_m(P_r) cos(πrm/3) = 0`, `m ≤ 3`, with
`w = (1, 2, 2, 1)`. Its determinant vanishes at many rational `P`. Since the cosines are rational,
the null vector is rational.

## Lean
`formal/GaloisForLFunctions/ZeroConfigurationGeometry/MixedDepthsHideBeyondTheInghamScale.lean`:
`column`, `temperedConfig_column`, `hasSum_Wsummand_column`, `hasSum_Wsummand_superpose`,
`temperedConfig_superpose`, `lagSum_pair_eq`, `cos_int_mul_pi_div_three`, `cosh_mul_int_eq`,
`mixed_symbol_eq`, `separated_of_depthFun`, `mixedZ`, `mixedZ'`, `mixedDepth_mimics_beyond_ingham`,
`not_eq_of_mimic_at_ingham_scale`, and the five-lag theorems above. `#print axioms`: `propext`,
`Classical.choice`, `Quot.sound`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized

## Log
- 2026-11-05 — created; formalized
