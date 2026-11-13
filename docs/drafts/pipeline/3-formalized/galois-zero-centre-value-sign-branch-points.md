# The centre value is the equation of the sign branch points of the heat cover

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Questions:** review-1211 §2.19 Q5 (the group generated: its sign part; position of the
  branch points); link of tier 3 to the coefficient field `K_J` of tier 1.

`H_τ(z) = ∫ Φ(x) e^{τx²} e^{izx} dx`, `c(τ) = H_τ(0)`, `μ₂ₙ = ∫ Φ(x) x^{2n} dx`.

## Theorems

1. **Heat equation in complex time.** `∂_τ H_τ^{(k)}(z) = −H_τ^{(k+2)}(z)` for all complex
   `τ`, `z` and all `k`; hence `∂_τ^n H_τ(z) = (−1)^n H_τ^{(2n)}(z)`.
2. **Time order.** At a collision of order `2k` at `(τ₀, z₀)` the function `τ ↦ H_τ(z₀)` has a
   zero of order exactly `k` at `τ₀`. At a collision of order `m` its time derivatives of
   order `i` with `2i < m` vanish.
3. **Sign branch points.** `c` has a zero of order `k` at `τ₀` iff `(τ₀, 0)` is a collision of
   order `2k`. There the profile `Q_{2k}` has `2k` roots, none `0`, and `−Z_ρ(s) = Z_ρ(−s)` on
   every sheet: the turn of the time flips the sign of `k` pairs of zeros.
4. **Coefficient field.** `c^{(n)}(0) = μ₂ₙ`, `c(τ) = Σ μ₂ₙ τⁿ/n!`, and
   `c^{(n)}(0)/c(0)` is the normalized even moment `μ₂ₙ/μ₀`, a generator of `K_J`.
5. **Singular points.** At a point of the cover both partial derivatives of `H` vanish iff the
   point is a collision of order at least three.
6. **Folds.** At a collision of order two there is an analytic `T` near `z₀` with
   `T(z₀) = τ₀`, `H_{T(z)}(z) = 0` and `T'(z₀) = 0`.
7. RH iff no positive real number is a branch time.

## Proof

1. Differentiate under the integral: `∂_τ` multiplies the kernel by `x² = −(ix)²`; on the
   disc `|τ − τ₀| < 1` the derivative is dominated by `|x|^{k+2} Φ(x) e^{(|τ₀|+1)x²} e^{|Im z||x|}`.
   Iterate.
2. By 1, `∂_τ^i H_τ₀(z₀) = (−1)^i H_τ₀^{(2i)}(z₀)`, which vanishes for `2i < 2k` and not for
   `i = k`.
3. The odd derivatives of the even function `H_τ₀` vanish at `0`; the even ones are, by 1, the
   derivatives of `c` up to sign. The profile of even order does not vanish at `0`. The sign
   law is the monodromy law at a central collision.
4. `H_0^{(2n)}(0) = ∫ Φ (ix)^{2n} = (−1)^n μ₂ₙ`; `c` is entire, so its Taylor series converges.
5. `∂_z H = 0` iff the order is `≥ 2`; then `∂_τ H = −H'' = 0` iff the order is `≥ 3`.
6. `∂_τ H(τ₀, z₀) = −H_τ₀''(z₀) ≠ 0`; the analytic implicit function theorem gives `T`.
   Differentiating `H(T(z), z) = 0` at `z₀`: `T'(z₀) ∂_τ H + ∂_z H = 0` and `∂_z H = 0`.
7. `RHTower.riemannHypothesis_iff_forall_zeros_simple` and `H_t = riemannHeat t`.

## Formalization

`GaloisTheoryOfZeros/TheCentreValueIsTheEquationOfTheSignBranchPoints.lean`:
`hasDerivAt_time_iteratedDeriv_complexHeat`, `iteratedDeriv_time_complexHeat`,
`IsCollision.analyticOrderAt_time`, `IsCollision.iteratedDeriv_time_eq_zero`, `centreValue`,
`isCollision_center_iff`, `center_monodromy_of_analyticOrderAt`,
`iteratedDeriv_centreValue_zero`, `iteratedDeriv_centreValue_zero_div`, `hasSum_centreValue`,
`deriv_eq_zero_and_deriv_time_eq_zero_iff`, `exists_time_of_isCollision_two`,
`riemannHypothesis_iff_forall_pos_not_mem_branchTimes`.

Checked with `lake --old env lean`; umbrella import wired.
