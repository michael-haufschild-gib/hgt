import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsFisherCurveFibers

/-! # A closed exact decoder for two successive normalized observations -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- The zero branch includes the pure slow source without dividing by its vanishing Fisher value. -/
def egbFixedChargeAGibbsFisherRatioDecoder (a b : ℝ) : ℝ :=
  if a = 0 then 0 else 255 / ((25 / 36 : ℝ) * (16 / b - 1 / a) - 30)

private theorem nonzero_ratio_reconstruction (t : ℝ) (ht : t ≠ 0) :
    (25 / 36 : ℝ) * (16 / egbFixedChargeAGibbsTunableFisherCurve (t / 4) -
      1 / egbFixedChargeAGibbsTunableFisherCurve t) - 30 = 255 / t ^ 2 := by
  have hd : 1 + t ^ 2 ≠ 0 := (show 0 < 1 + t ^ 2 by positivity).ne'
  have hn : 1 + (t / 4) ^ 2 ≠ 0 := (show 0 < 1 + (t / 4) ^ 2 by positivity).ne'
  unfold egbFixedChargeAGibbsTunableFisherCurve
  field_simp
  <;> ring

/-- The decoder exactly returns the squared fast-to-slow parameter for every real chart coordinate. -/
theorem egbFixedChargeAGibbsFisherRatioDecoder_exact (t : ℝ) :
    egbFixedChargeAGibbsFisherRatioDecoder (egbFixedChargeAGibbsTunableFisherCurve t)
      (egbFixedChargeAGibbsTunableFisherCurve (t / 4)) = t ^ 2 := by
  unfold egbFixedChargeAGibbsFisherRatioDecoder
  by_cases ht : t = 0
  · subst t
    rw [egbFixedChargeAGibbsTunableFisherCurve_endpoints.1]
    norm_num
  · have hf : egbFixedChargeAGibbsTunableFisherCurve t ≠ 0 := by
      intro h
      exact ht ((egbFixedChargeAGibbsTunableFisherCurve_zero_iff t).1 h)
    rw [if_neg hf, nonzero_ratio_reconstruction t ht]
    field_simp

/-- Every pair on the realized Fisher curve decodes to a nonnegative source ratio. -/
theorem egbFixedChargeAGibbsFisherRatioDecoder_nonneg (t : ℝ) :
    0 ≤ egbFixedChargeAGibbsFisherRatioDecoder (egbFixedChargeAGibbsTunableFisherCurve t)
      (egbFixedChargeAGibbsTunableFisherCurve (t / 4)) := by
  rw [egbFixedChargeAGibbsFisherRatioDecoder_exact]
  exact sq_nonneg t

end
end GaloisForLFunctions.HTGeometry
