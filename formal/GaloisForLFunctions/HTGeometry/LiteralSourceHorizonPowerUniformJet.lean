import GaloisForLFunctions.HTGeometry.HorizonPowerThirdWithinDerivative

/-! The literal source power has a frequency-uniform cubic Taylor remainder. -/

namespace GaloisForLFunctions.HTGeometry
open Set Metric
noncomputable section
set_option autoImplicit false

/-- Every unit closed frequency ball admits the exact degree-two source-power
Taylor jet on the physical half-cutoff, with a genuine uniform cubic tail. -/
theorem exists_literalSourceHorizonPower_uniformJet3 (α₀ : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧
      HasUniformJet3 (closedBall α₀ 1) (1 / 2)
        literalSourceHorizonPower
        (fun α => literalSourceHorizonPower α 0)
        (fun α => literalSourceHorizonPowerFirst α 0)
        (fun α => literalSourceHorizonPowerSecond α 0 / 2) C := by
  obtain ⟨C, hC0, hC⟩ := exists_horizonPowerThirdCore_uniform_bound α₀
  have hjet := hasUniformJet3_of_deriv3_bound (S := closedBall α₀ 1)
    (b := (1 / 2 : ℝ)) (F := literalSourceHorizonPower) (C := C) (by norm_num)
    (fun α _ => literalSourceHorizonPower_contDiffOn α)
    (fun α hα z hz => by
      rw [literalSourceHorizonPower_iteratedDerivWithin_three α hz]
      exact hC α hα z hz)
  refine ⟨C / 2, div_nonneg hC0 (by norm_num), ?_⟩
  intro α hα z hz
  have hfirst : derivWithin (literalSourceHorizonPower α) (Icc 0 (1 / 2)) 0 =
      literalSourceHorizonPowerFirst α 0 := by
    simpa only [iteratedDerivWithin_one] using
      (literalSourceHorizonPower_iteratedDerivWithin_one α (by norm_num))
  have hsecond : iteratedDerivWithin 2 (literalSourceHorizonPower α) (Icc 0 (1 / 2)) 0 =
      literalSourceHorizonPowerSecond α 0 :=
    literalSourceHorizonPower_iteratedDerivWithin_two α (by norm_num)
  have h := hjet α hα z hz
  simp only at h ⊢
  rw [hfirst, hsecond] at h
  exact h

end
end GaloisForLFunctions.HTGeometry
