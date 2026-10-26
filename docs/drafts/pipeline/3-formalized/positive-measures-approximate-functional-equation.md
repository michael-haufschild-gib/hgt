# Positive measures with an approximate functional equation lie near the integers

- **ID:** positive-measures-approximate-functional-equation
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** `docs/reports/review-2510/hard-obstacles-summary.md`, first milestone (6) ("a
  quantitative stability theorem for the theta law") and §4.5 "Nonlinear rigidity: stability theory
  for the theta law beyond sublinear-defect Hamburger stability, measuring how far a positive measure
  with an approximate law lies from integer counting"; walls ledger 14.12.
- **Statement.** Let `ν ≥ 0` be a Borel measure with `ν(−∞, 1) = 0` and `∫ u^{−3/2} dν < ∞`. Let `E`
  be continuous on `1/2 ≤ Re s ≤ 3/2`, holomorphic inside, `O(1/(1+t²))`, with
  `Γ_ℝ(s) D_ν(s) = E(s) + β Γ_ℝ(s−1)` on `Re s = 3/2` and
  `E(s) − E(1−s) = −β(Γ_ℝ(s−1) − Γ_ℝ(−s)) + Γ_ℝ(s) g(Im s/2)` on `Re s = 1/2`. If `g` is measurable,
  polynomially bounded and integrable, then
  `∫ (sin πu/(πu))² dν(u) ≤ (6/π) ‖g‖₁`.
  The left side vanishes exactly when `ν` is carried by the positive integers.

## Lean
`GaloisForLFunctions.ArithmeticPositiveDuality.integral_sinc_sq_le_of_critical_line_defect`
(`formal/GaloisForLFunctions/ArithmeticPositiveDuality/ApproximateFunctionalEquationNearIntegers.lean`),
with `measureSeries_eq_of_theta_defect`, `fejer_pairing_identity_of_theta_defect`,
`tendsto_integral_fejerPolarKernel_neg`, `abs_integral_fejerDefectKernel_le`. Axioms: `propext`,
`Classical.choice`, `Quot.sound`. Wired into `ArithmeticPositiveDuality.lean`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized

## Proof
1. The critical-line defect enters the theta law as
   `θ_ν(x) = x^{−1/2}θ_ν(1/x) − β + βx^{−1/2} + K(x)`,
   `K(x) = (1/2π) ∫ x^{−(1/4+it)} Γ_ℝ(1/2+2it) g(t) dt` (`critical_line_even_theta_relation_defect`).
2. Laplace integration against `t e^{−πt²x}` on `x > 0`: the two theta pieces give `L_ν(t)` and `F_ν(t)`
   (Fubini on `[1,∞) × (0,∞)`), the polar part `−β/(πt) + β`, and `K` gives
   `J(t) = (1/2π) ∫ g(v) k(2v, t) dv`. Hence `L_ν = F_ν − β/(πt) + β + J` on `t > 0`, and on
   `Re t > 0` by the identity theorem.
3. Real parts against the Fejér window `2(1−|τ|)` on `t = ε + iτ`, integrated over `[−1,1]`:
   `2 ∫ e^{−2πuε} sinc² dν = S_ε − P_ε − D_ε`, with `S_ε` the series side, `P_ε` the polar side and
   `D_ε = ∫ 2(1−|τ|) Re J(ε+iτ) dτ`.
4. `S_ε = O(√ε)` because every pole `u ≥ 1` lies outside the window; `P_ε → 2Re(−β) + 2Re β = 0`
   (the imaginary part of `β` contributes an odd integrand); the left side tends to `2 ∫ sinc² dν`.
5. `‖J(τ)‖ ≤ (3/2π)‖τ‖^{−1/2}‖g‖₁` and `‖ε+iτ‖ ≥ |τ|`, so folding `[−1,1]` onto `[0,1]`,
   `|D_ε| ≤ 2·2·(3/2π)‖g‖₁ ∫_0^1 τ^{−1/2} dτ = (12/π)‖g‖₁`. Divide by 2.

## Scope
The bound controls support, not weights: equality of the integer weights in the exact case needs the
periodicity of `F_ν` on integer-supported measures, which a defect breaks at the level of residues.
