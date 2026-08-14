import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualNegativeContourDerivative

noncomputable section

open Complex Set MeasureTheory Filter

namespace RHTower

/-- Negative-quarter contour restores the square conductor: at small scale the
exact dual carrier changes at rate `Y^(1/4)/tau^(3/2)`. -/
theorem exists_norm_deriv_smoothAFEZetaSquareDualWeight_le_small_scale :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {tau Y : ℝ}, 4 ≤ tau → 0 < Y →
      ‖deriv (fun u : ℝ => smoothAFEZetaSquareDualWeight u Y) tau‖ ≤
        A * Y ^ (1 / 4 : ℝ) /
          (tau * (tau ^ (1 / 4 : ℝ)) ^ 2) := by
  obtain ⟨C, hC, hpointCarrier⟩ :=
    exists_norm_smoothAFEZetaChiShiftRatioSqQuarterHeightDerivative_le
  let q : ℝ → ℝ := fun v =>
    (1 + |v|) ^ 5 * Real.exp (-(v ^ 2))
  let M : ℝ := ∫ v : ℝ, q v
  let Q : ℝ := Real.exp ((1 / 4 : ℝ) ^ 2) / (1 / 4 : ℝ)
  let a : ℝ := 1 / (2 * Real.pi)
  let A : ℝ := a * (C * Q) * M
  have hq : Integrable q := integrable_one_add_abs_pow_five_mul_exp_neg_sq
  have hq0 : ∀ v, 0 ≤ q v := fun v => by
    dsimp only [q]
    positivity
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact integral_nonneg hq0
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro tau Y htau hY
  have htau0 : 0 < tau := by linarith
  have hr0 : 0 < tau ^ (1 / 4 : ℝ) :=
    Real.rpow_pos_of_pos htau0 _
  let D : ℝ := (C * Q) * Y ^ (1 / 4 : ℝ) /
    (tau * (tau ^ (1 / 4 : ℝ)) ^ 2)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hmajor : Integrable (fun v : ℝ => D * q v) := hq.const_mul D
  have hint :
      ‖∫ v : ℝ,
          smoothAFEZetaSquareDualWeightNegQuarterHeightDerivativeIntegrand
            tau Y v‖ ≤
        ∫ v : ℝ, D * q v := by
    apply norm_integral_le_of_norm_le hmajor
    exact Filter.Eventually.of_forall fun v => by
      have hc := hpointCarrier htau v
      have hm := norm_smoothAFEMellinIntegrand_neg_quarter_le hY v
      unfold smoothAFEZetaSquareDualWeightNegQuarterHeightDerivativeIntegrand
      rw [norm_mul]
      calc
        ‖smoothAFEZetaChiShiftRatioSqQuarterHeightDerivative tau v‖ *
            ‖smoothAFEMellinIntegrand Y
              (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I)‖
          ≤ (C * (1 + |v|) ^ 5 /
              (tau * (tau ^ (1 / 4 : ℝ)) ^ 2)) *
            ((Y ^ (1 / 4 : ℝ) * Q) * Real.exp (-(v ^ 2))) := by gcongr
        _ = D * q v := by
          dsimp only [D, q]
          ring
  rw [(hasDerivAt_smoothAFEZetaSquareDualWeight_via_neg_quarter hY tau).deriv]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
  calc
    a * ‖∫ v : ℝ,
          smoothAFEZetaSquareDualWeightNegQuarterHeightDerivativeIntegrand
            tau Y v‖
        ≤ a * ∫ v : ℝ, D * q v := by gcongr
    _ = a * (D * M) := by rw [integral_const_mul]
    _ = A * Y ^ (1 / 4 : ℝ) /
          (tau * (tau ^ (1 / 4 : ℝ)) ^ 2) := by
      dsimp only [A, D]
      ring

end RHTower
