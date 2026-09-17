import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Generic continuity rule for the third derivative of a logarithm. -/

namespace GaloisForLFunctions.HTGeometry

theorem continuousAt_log_third_form
    {X : Type*} [TopologicalSpace X] {x : X}
    (H H₁ H₂ H₃ : X → ℝ)
    (hH : ContinuousAt H x) (hH₁ : ContinuousAt H₁ x)
    (hH₂ : ContinuousAt H₂ x) (hH₃ : ContinuousAt H₃ x)
    (hne : H x ≠ 0) :
    ContinuousAt (fun y => H₃ y / H y - 3 * H₂ y * H₁ y / H y ^ 2 +
      2 * H₁ y ^ 3 / H y ^ 3) x := by
  have hthree : ContinuousAt (fun _ : X => (3 : ℝ)) x := continuousAt_const
  have htwo : ContinuousAt (fun _ : X => (2 : ℝ)) x := continuousAt_const
  have hm := ((hthree.mul hH₂).mul hH₁).div (hH.pow 2) (pow_ne_zero 2 hne)
  have hp := (htwo.mul (hH₁.pow 3)).div (hH.pow 3) (pow_ne_zero 3 hne)
  exact ((hH₃.div hH hne).sub hm).add hp

end GaloisForLFunctions.HTGeometry
