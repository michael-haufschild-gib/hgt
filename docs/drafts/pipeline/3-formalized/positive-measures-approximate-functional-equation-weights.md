# Positive measures with an approximate functional equation have near-constant integer weights

- **ID:** positive-measures-approximate-functional-equation-weights
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** `docs/reports/review-2510/hard-obstacles-summary.md`, first milestone (6) ("a
  quantitative stability theorem for the theta law") and §4.5 ("measuring how far a positive measure
  with an approximate law lies from integer counting"); walls ledger 14.12. Completes
  `positive-measures-approximate-functional-equation`, whose bound controls support only.
- **Statement.** Under the hypotheses of `positive-measures-approximate-functional-equation`
  (`ν ≥ 0` on `[1,∞)`, `∫ u^{−3/2} dν < ∞`, `Γ_ℝ(s)D_ν(s) = E(s) + βΓ_ℝ(s−1)` on `Re s = 3/2`,
  `E(s) − E(1−s) = −β(Γ_ℝ(s−1) − Γ_ℝ(−s)) + Γ_ℝ(s) g(Im s/2)` on `Re s = 1/2`, `g` measurable,
  polynomially bounded, integrable), for every real `n ≥ 1`
  `|∫ (1 − |u − n|)⁺ dν(u) − 2 Re β| ≤ (18/π + 4κ/π²) ‖g‖₁`, `κ = 4^{−1/4} π^{−1/4} Γ(1/4)`,
  and `|Im β| ≤ (κ/π) ‖g‖₁`. With the off-lattice bound `∫ sinc²(πu) dν ≤ (6/π)‖g‖₁`, `ν` is within
  `O(‖g‖₁)` of `2 Re β · Σ_{k≥1} δ_k` in tent mass at every height and in off-lattice mass.

## Lean
`GaloisForLFunctions.ArithmeticPositiveDuality.abs_integral_unitTent_sub_le_of_critical_line_defect`
(`formal/GaloisForLFunctions/ArithmeticPositiveDuality/ApproximateFunctionalEquationNearCounting.lean`),
with `abs_half_integral_unitTent_sub_le_of_theta_defect`, `tent_pairing_identity_of_theta_defect`,
`tendsto_poissonSmoothing`, `intervalIntegral_shiftedTentPolarKernel`,
`abs_intervalIntegral_shiftedTentDefectKernel_le`, `im_eq_of_theta_defect`, `norm_defectKernel_four_le`.
Axioms: `propext`, `Classical.choice`, `Quot.sound`. Wired into `ArithmeticPositiveDuality.lean`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized

## Proof
1. The defective theta law `θ_ν(x) = x^{−1/2}θ_ν(1/x) − β + βx^{−1/2} + K(x)` gives, by Laplace
   integration, `L_ν(t) = F_ν(t) − β/(πt) + β + J(t)` on `Re t > 0`.
2. Real parts on `t = ε + i(n+s)`, weighted by `1 − |s|` on `[−1,1]` (Fubini on `[−1,1] × ν`):
   - series side `(1/2) ∫ (W_ε(u−n) + W_ε(−u−n)) dν`, `W_ε(v) = (1/π)∫(1−|s|) ε/(ε²+(s−v)²) ds`;
     `W_ε(v) → (1−|v|)⁺` by Poisson smoothing; `W_ε ≤ 1` and `W_ε(v) ≤ 4/v²` for `|v| ≥ 2` give the
     uniform majorant `(n+2)²/u²`, so the series side tends to `(1/2) ∫ tent_n dν`;
   - dual side `∫ e^{−2πuε} cos(2πun) sinc²(πu) dν`, at most `∫ sinc² dν ≤ (6/π)‖g‖₁`;
   - polar side `Re β − Re β · W_ε(−n) − (Im β/π) q_ε`, with `W_ε(−n) → 0` and
     `0 ≤ q_ε = ∫(1−|s|)(n+s)/(ε²+(n+s)²) ds ≤ 2`;
   - defect side: `‖J(t)‖ ≤ (3/2π)‖t‖^{−1/2}‖g‖₁` and `(1−|s|)² ≤ n+s ≤ ‖t‖` give `≤ (3/π)‖g‖₁`.
3. Letting `ε → 0⁺`: `|(1/2)∫ tent_n dν − Re β| ≤ (6/π + 3/π)‖g‖₁ + (2/π)|Im β|`.
4. At `x = 4` the theta values are real and `4^{−1/2} = 1/2`, so `Im β = 2 Im K(4)`;
   `|4^{−(1/4+it)}| = 4^{−1/4}` and `|Γ_ℝ(1/2+2it)| ≤ π^{−1/4}Γ(1/4)` give `‖K(4)‖ ≤ (κ/2π)‖g‖₁`.
