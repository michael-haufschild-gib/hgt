# The simple-pole class is ζ (κ = 1 class collapse)

- **ID:** the-simple-pole-class-is-zeta
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** `docs/reports/review-2610/hard-obstacles-summary.md` W11 and first milestone (5)
  ("`CompletedPositiveSystem 1 1 = {cζ}` [R]"); B3.19 boundary ("the κ = 1 class is expected to be
  `{ζ}`; a base must leave conductor-one completed positive systems").
- **Statement.** If `CompletedPositiveSystem 1 1 F Λ` (`F` holomorphic and nonvanishing on
  `Re s > 1` with positive-definite vertical sections of `Re(−F'/F)`, and
  `Λ = s(s − 1)Γ_ℝ(s)F` entire of order one, `Λ(1 − s) = Λ(s)`, `Λ(s̄) = conj Λ(s)`), then
  `F = Kζ` on `Re s > 1` for some real `K ≠ 0`.

## Lean
`GaloisForLFunctions.StripBochnerWeilForcing.completedPositiveSystem_one_one_eq_zeta`
(`formal/GaloisForLFunctions/StripBochnerWeilForcing/TheSimplePoleClassIsZeta.lean`), with the
general analytic step `exists_dirichletMeasure_of_posDef_sections`
(`formal/GaloisForLFunctions/StripBochnerWeilForcing/PositiveDefiniteSectionsAreCompletelyMonotone.lean`:
`isPosDef_secondDiff`, `tendsto_secondDiffQuotient_re`, `isPosDef_re_iterate_deriv_two_mul`,
`tower_odd_nonpos`, `alternating_iterate_deriv_nonneg`, `differentiableOn_laplaceC`).

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized

## Proof
1. *Even derivatives.* Second differences `2φ(u) − φ(u+h) − φ(u−h)` of a positive-definite `φ`
   are positive definite (the form of `φ` at `{x_i, x_i + h}` with coefficients `(c, −c)`), and
   for holomorphic `H`, `(2 Re H(w) − Re H(w+ih) − Re H(w−ih))/h² → Re H''(w)`. So
   `u ↦ Re G^{(2k)}(σ + iu)` is positive definite for `G = −F'/F` and every `k`, and
   `G^{(2k)}(σ) ≥ 0` on `(1, ∞)`.
2. *Odd derivatives.* `Re Λ'/Λ ≥ 0` on `Re s > 1` (Hadamard zero pairs) and `Re ψ(y) ≤ log y` give
   `G(x) ≤ 4√x` for `x ≥ 2`. If `G^{(2j+1)}(x₁) > 0`, convexity of `G^{(2j)}` makes it grow
   linearly; for `j = 0` this beats `√x`, for `j ≥ 1` it makes `G^{(2j−1)}` eventually positive,
   contradicting the induction hypothesis. Hence `(−1)^k G^{(k)} ≥ 0`.
3. *`F` is completely monotone.* `F` is real on `(1, ∞)` (conjugation symmetry of `Λ` and of
   `s(s−1)Γ_ℝ`); `F₁ = F/F(2)` is positive there (intermediate values). From `F₁' = −G F₁` and
   Leibniz, `(−1)^{k+1}F₁^{(k+1)} = Σ_i C(k,i)((−1)^i G^{(i)})((−1)^{k−i}F₁^{(k−i)}) ≥ 0`.
4. *Bernstein–Widder.* `t ↦ F₁(5/4 + t)` is completely monotone on `(0, ∞)` with a finite limit at
   `0`, so it is `∫ e^{−tr} dτ(r)` with `τ` finite on `[0, ∞)`. With
   `μ = exp_*(e^{5r/4} τ)` (carried by `[1, ∞)`), `F₁(s) = ∫ u^{−s} dμ` for real `s > 5/4`, and on
   `Re s > 5/4` by the identity theorem (the complex Laplace transform of `τ` is holomorphic).
5. *Rigidity.* Write `Λ/F(2) = c₀ + s(s−1)P(s)` (`P = dslope (dslope Λ₁ 0) 1`, entire, using
   `Λ₁(1) = Λ₁(0)`), and `h(s) = 2(k(s) − 1)/s = Γ_ℝ(s) − 2/s` with
   `k(s) = π^{−s/2}Γ(1 + s/2)`, holomorphic on `Re s > −2`. Then
   `E = P + (c₀/2)(h(s) − h(s−1))` is holomorphic on `−1/2 ≤ Re s ≤ 3/2`, bounded by
   `C₀ exp(‖s‖³)` there, and `E − (c₀/2)Γ_ℝ(s) + (c₀/2)Γ_ℝ(s − 1) = Λ₁(s)/(s(s−1))`, which is
   `Γ_ℝ(s)D_μ(s)` on `Re s = 3/2` and `Γ_ℝ(1−s)D_μ(1−s)` on `Re s = −1/2`. Positive-measure
   rigidity from the bare functional equation gives `μ = m Σ_{k≥1} δ_k`, so `F = F(2) m ζ` on
   `Re s > 5/4`, and on `Re s > 1` by analytic continuation; `m ≠ 0` since `F₁(2) = 1`.

## Scope
The input from multiplicative positivity is used only through the vertical sections of
`Re(−F'/F)` and Hadamard positivity of `Λ'/Λ`; the pole budget `κ = 1` enters through the
functional equation of a completion with exactly one factor `s(s − 1)`.
