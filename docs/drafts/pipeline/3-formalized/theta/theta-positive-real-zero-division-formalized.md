# Positive theta-source flow that removes one real Xi zero pair — Lean certificate

- **Paper card:** `theta-positive-real-zero-division.md`
- **Lean module:** `GaloisForLFunctions.RHTower.ThetaZeroDivisionSource`
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** targeted `lake build`; `lake env lean` audit clean; `#print axioms` =
  `propext`, `Classical.choice`, `Quot.sound` for all audited theorems; no `sorry`.

`k = thetaCuspFullSource`, `F = XiC` (`sourceTransform_thetaSourceC`: `∫ e^{-izx} k = XiC z` on ℂ),
`g_γ = thetaZeroDivision γ` (formula (1)), `G_γ = thetaZeroDivisionTransform γ`,
`k_{ε,γ} = thetaZeroDivisionFlow γ ε`, `F_{ε,γ} = thetaZeroDivisionFlowTransform γ ε`.

| Card item | Lean theorem |
|-|-|
| (1) `g_γ` real, even | `thetaZeroDivision`, `zeroDivision_thetaSourceC_ofReal`, `thetaZeroDivision_neg` |
| smooth (even join `g'(0+) = 0` at `F(γ)=0`) | `contDiff_thetaZeroDivision`, `zeroDivision_eq_joinedDivision`, `joinedDivision_neg` |
| strictly positive everywhere, via (4) | `thetaZeroDivision_pos`, `thetaSineIntegral_eq_integral_one_sub_cos`, `deriv_thetaCuspFullSource_neg_of_pos` |
| every exponential moment | `integrable_exp_abs_mul_thetaZeroDivision`, `expMomentSource_zeroDivision` |
| (5) `g_γ/k → 0`, `sup g_γ/k < ∞` (rate `e^{-2|x|}`) | `tendsto_thetaZeroDivision_div`, `exists_thetaZeroDivision_le`, `norm_outwardSine_thetaSourceC_le_tail` |
| ODE `g'' + γ² g = γ² k` on ℝ | `thetaZeroDivision_green`, `iteratedDeriv_two_joinedDivision` |
| (2) `G_γ` entire, `G_γ(z)(1 - z²/γ²) = F(z)`, quotient off `±γ` | `differentiable_thetaZeroDivisionTransform`, `thetaZeroDivisionTransform_mul`, `thetaZeroDivisionTransform_eq_div` |
| general Fourier division `(α²-z²)Ĝ = α²(F(z)-F(α))` | `ExpMomentSource.sourceTransform_zeroDivision`, `integral_cos_mul_sin_sub`, `ExpMomentSource.integral_cos_mul_outwardSine` |
| `∫ g_γ = ∫ k` | `integral_thetaZeroDivision` |
| flow positive, even, smooth, exponentially decaying | `thetaZeroDivisionFlow_pos`, `thetaZeroDivisionFlow_neg`, `contDiff_thetaZeroDivisionFlow`, `integrable_exp_abs_mul_thetaZeroDivisionFlow` |
| (3) `F_{ε,γ}(z) = G_γ(z)[1 - (1-ε)z²/γ²]` | `thetaZeroDivisionFlowTransform_eq` |
| moving pair `±γ/√(1-ε)`, outward, escaping as `ε ↑ 1` | `thetaZeroDivisionFlowTransform_moving_zero`, `strictMonoOn_movingZero`, `tendsto_movingZero` |
| every other zero kept, multiplicity ≥ original | `thetaZeroDivisionFlowTransform_eq_zero`, `analyticOrderAt_XiC_le_flow` |
| at `ε = 1` one copy of `±γ` removed; simple pair deleted | `analyticOrderAt_thetaZeroDivisionTransform_add_one`, `thetaZeroDivisionTransform_ne_zero_of_simple` |
| mass constant along the flow | `integral_thetaZeroDivisionFlow`, `thetaZeroDivisionFlowTransform_zero` |
| unconditional instances (real zeros from Hardy) | `exists_positive_thetaZeroDivision` |
