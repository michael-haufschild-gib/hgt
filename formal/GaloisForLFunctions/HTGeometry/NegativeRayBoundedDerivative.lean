import GaloisForLFunctions.HTGeometry.BoundedComplexDerivative

/-! A backward unit interval controls the actual derivative everywhere on the negative ray. -/
open Set
namespace GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Uniform value and second-derivative bounds control the first derivative up to the finite endpoint. -/
theorem norm_complex_deriv_le_of_bounded_negative {f g h : ℝ → ℂ} {C M : ℝ}
    (hf : ∀ t < 0, HasDerivAt f (g t) t) (hg : ∀ t < 0, HasDerivAt g (h t) t)
    (hh : ContinuousOn h (Iio (0:ℝ)))
    (hC : ∀ t < 0, ‖f t‖ ≤ C) (hM : ∀ t < 0, ‖h t‖ ≤ M)
    (t : ℝ) (ht : t < 0) : ‖g t‖ ≤ 4*C+M := by
  have hx (x : ℝ) (hx : x ∈ Icc (-t) (-t+1)) : -x < 0 := by linarith [hx.1]
  have hfr (x : ℝ) (hxi : x ∈ Icc (-t) (-t+1)) :
      HasDerivAt (fun x : ℝ => f (-x)) (-g (-x)) x := by
    simpa only [Function.comp_def,neg_one_smul] using
      (hf (-x) (hx x hxi)).scomp x (hasDerivAt_id x).neg
  have hgr (x : ℝ) (hxi : x ∈ Icc (-t) (-t+1)) :
      HasDerivAt (fun x : ℝ => -g (-x)) (h (-x)) x := by
    simpa only [Function.comp_def,Pi.neg_apply,neg_one_smul,neg_neg] using!
      ((hg (-x) (hx x hxi)).scomp x (hasDerivAt_id x).neg).neg
  have hhr : ContinuousOn (fun x : ℝ => h (-x)) (Icc (-t) (-t+1)) :=
    hh.comp continuous_neg.continuousOn (fun x hxi => hx x hxi)
  have hb := norm_complex_deriv_le_of_bounded hfr hgr hhr
    (fun x hxi => hC (-x) (hx x hxi)) (fun x hxi => hM (-x) (hx x hxi))
  simpa only [neg_neg,norm_neg] using hb

end
end GaloisForLFunctions.HTGeometry
