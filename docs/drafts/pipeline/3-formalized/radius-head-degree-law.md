# Degree law for heated finite heads: every head is repaired at every large height

- **ID:** radius-head-degree-law
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `1-in-progress/wd-la-sign-producer-loop-2026-10-25.md`, row 14
- **Statement:** A monic real polynomial `q` of degree `N` whose complex roots lie in `|y| ≤ r` has
  `e^{s∂_x²} q(x²)` coefficient-positive for every `s > 0` with `32 r ≤ s N`. For the radius-`R`
  finite head of `Ξ` this gives head positivity at heat `λ` wherever the head retains at least
  `64R²/λ` zero copies, hence at every large height for every fixed `λ > 0`.

## Goal
Partial supply for the LA obstacle (finite-head coefficient positivity at small heat): the finite
head at a fixed positive heat is coefficient-positive at all large heights, by zero counting
alone. The Ki–Kim–Lee mechanism for the full slice (heat as an Euler-region shift) is not used.

## Gates
- [x] 0 → 1
- [x] 1 → 2 paper proof below
- [x] 2 → 3 Lean, standard axioms, wired into `ArithmeticLocalDivisorGeometry.lean`
- [ ] 3 → 4

## Paper proof
1. `(2l)! s^l/l! · [x^{2l}] e^{s∂²} q(x²) = ∫ g_s(u) u^{2l} H_l(u²) du`, `H_l(y) = [w^l] q(y+w)`,
   `g_s` the Gaussian of variance `2s`, moments `μ_m = (2m)! s^m/m!`.
2. For `y ≥ r`, every factor of `q(y+w)` dominates the matching power of `w + (y − r)`
   coefficientwise (linear factors: `y − ρ ≥ y − r`; conjugate pairs: `|y − ρ|² ≥ (y − r)²`,
   `y − Re ρ ≥ y − r`), so `H_l(y) ≥ C(N,l)(y − r)^{N−l}`; for every real `y`,
   `|H_l(y)| ≤ C(N,l)(|y| + r)^{N−l}`.
3. Splitting `y ≥ 2r`, `r ≤ y < 2r`, `0 ≤ y < r`:
   `2^{N−l} y^l H_l(y) ≥ C(N,l)(y^N − (2r)^N − (4r)^{N−l} y^l)` for `y ≥ 0`, `l ≤ N`.
4. Integrating against `g_s`, the coefficient is `≥ 0` once `(2r)^N + (4r)^{N−l} μ_l ≤ μ_N`
   (`l < N`). Since `μ_N/μ_l = ∏_{l≤m<N} 2s(2m+1) ≥ (2s)^{N−l} N!/l! ≥ (2sN/e)^{N−l}`, this holds
   when `32 r ≤ sN`. For `l ≥ N` the coefficient is a nonnegative multiple of `q_N = 1`.
5. Head: roots `−(z − t)²` with `|z − t| ≤ R`, so `r = R²`; degree = number of retained copies.
   Copies with ordinate in `(t − R/2, t + R/2]` are retained (`R ≥ 1`), and Riemann–von Mangoldt
   (`|N(T) − M(T)| ≤ C log T`) with the tangent bound `M(b) − M(a) ≥ (b − a) log(a/2π)/2π` gives
   at least `2C log t − O(C)` of them for `R ≥ 8πC`. Reflection `z ↦ −z` covers `t < 0`.
6. Slice: off the zero ordinates the normalized head is a positive multiple of the divisor head;
   the exact head/tail transfer (`xiSliceHeatTransfer_nonneg_of_finiteHead_poly`) gives every
   heated slice coefficient at every large height.

## Lean
- `ArithmeticLocalDivisorGeometry/RootRadiusHeatCone`: `DiscFactor`, `CoeffDom.mul`,
  `CoeffAbsLe.mul`, `coeffDom_taylor_prod`, `coeffAbsLe_taylor_prod`, `pointwise_lower`,
  `gaussMoment_add`, `pow_le_exp_mul_factorial_div`, `prod_moment_ratio_lower`, `moment_numerics`,
  `heatCoeff_mul_eq_integral`, `coeffNonneg_forwardPolyHeat_expand_of_discFactors`.
- `ArithmeticLocalDivisorGeometry/RadiusHeadHeatPositivity`:
  `coeffNonneg_heat_localDivisorPolynomial_radiusHead`, `sliceTruncPoly_eq_C_mul_localDivisorPolynomial`,
  `coeffNonneg_heat_sliceTruncPoly_radiusHead`, `exists_le_card_radiusHead`, `card_radiusHead_neg`,
  `exists_radiusHead_heat_coeffNonneg`, `exists_xiSliceHeatTransfer_nonneg_of_head_counting`.
- Checks: plain `lake --old env lean` on both leaves, no warnings; `#print axioms` on the three main
  theorems: `propext, Classical.choice, Quot.sound`.

## Position
- The admissible heat depends only on root radius and degree; it ignores off-line depth and
  clustering. The order `r/N` is sharp (`(y − r)^N` needs heat of order `r/N`).
- What remains of the LA obstacle at heat `λ`: heights where the head retains fewer than `64R²/λ`
  copies, a bounded range that grows as `λ → 0`. Going below the Riemann–von Mangoldt counting
  scale would need local zero counts at the depth scale (wall 3).

## Log
- 2026-10-25 — conjectured, proved, formalized (loop row 14).
