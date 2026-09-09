import GaloisForLFunctions.HTGeometry.HalfPlaneHardyCauchyTotality

/-!
# Exact Cauchy evaluation for bounded upper-half-plane multipliers

The literal boundary multiplier reproduces its analytic value in every Hardy
Cauchy evaluation. The contour formula proves the identity first on Cauchy
features; their dense span and continuity supply all Hardy vectors. This gives
the actual adjoint eigenvectors needed to distinguish causal and reverse time.
-/

open Complex MeasureTheory Set Filter Topology
open scoped InnerProductSpace
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

local instance : CompleteSpace UpperHardyL2 := RHTower.isClosed_hardyL2.completeSpace_coe

private theorem upper_minus_conj_ne_zero (v : {v : ℂ // 0 < v.im})
    {z : ℂ} (hz : 0 ≤ z.im) : z - (starRingEnd ℂ) v.val ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.sub_im,Complex.conj_im,Complex.zero_im] at hi
  linarith [v.property]

private theorem product_kernel_formula (F : ClosedUpperHalfPlaneMultiplier)
    (v w : {z : ℂ // 0 < z.im}) :
    (∫ x : ℝ, (F.fn (x:ℂ) / ((x:ℂ)-(starRingEnd ℂ) v.val)) / ((x:ℂ)-w.val)) =
      2 * (Real.pi:ℂ) * I * (F.fn w.val / (w.val-(starRingEnd ℂ) v.val)) := by
  apply integral_div_sub_eq_of_upperHalfPlane_farDecay
    (u := fun z => F.fn z / (z-(starRingEnd ℂ) v.val)) (w := w.val)
    (M := 2*F.bound) (R := 2*‖v.val‖+1)
  · intro z hz
    exact (F.diff z hz).div (differentiableAt_id.sub_const _) (upper_minus_conj_ne_zero v hz)
  · linarith [norm_nonneg v.val]
  · intro z hz hzR
    have hzn : 0 < ‖z‖ := by linarith [norm_nonneg v.val]
    have hh : ‖v.val‖ ≤ ‖z‖/2 := by linarith
    have hden : ‖z‖/2 ≤ ‖z-(starRingEnd ℂ) v.val‖ := by
      have h := norm_sub_norm_le z ((starRingEnd ℂ) v.val)
      rw [RCLike.norm_conj] at h
      linarith
    have hhalf : 0 < ‖z‖/2 := by linarith
    calc
      ‖F.fn z / (z-(starRingEnd ℂ) v.val)‖ = ‖F.fn z‖ / ‖z-(starRingEnd ℂ) v.val‖ := norm_div _ _
      _ ≤ F.bound / ‖z-(starRingEnd ℂ) v.val‖ :=
        div_le_div_of_nonneg_right (F.norm_le z hz) (norm_nonneg _)
      _ ≤ F.bound / (‖z‖/2) := div_le_div_of_nonneg_left F.bound_nonneg hhalf hden
      _ = 2*F.bound/‖z‖ := by ring
  · exact w.property

/-- Exact contour evaluation of every bounded analytic multiplier on each Cauchy feature. -/
theorem closedUpperMultiplier_CauchyFeature_formula (F : ClosedUpperHalfPlaneMultiplier)
    (v w : {z : ℂ // 0 < z.im}) :
    upperHardyCauchyEval w.val w.property (F.hardyMul (lowerCauchyFeatureAt v.val v.property)) =
      2 * (Real.pi:ℂ) * I * (F.fn w.val / (w.val-(starRingEnd ℂ) v.val)) := by
  rw [upperHardyCauchyEval_apply]
  calc
    (∫ x : ℝ, ((F.hardyMul (lowerCauchyFeatureAt v.val v.property)).val : ℝ → ℂ) x /
        ((x:ℂ)-w.val)) =
      ∫ x : ℝ, (F.fn (x:ℂ) / ((x:ℂ)-(starRingEnd ℂ) v.val)) / ((x:ℂ)-w.val) := by
        apply integral_congr_ae
        filter_upwards [F.coe_boundaryMul (lowerCauchyFeatureAt v.val v.property).val,
          coe_lowerCauchyFeatureAt v.property] with x hx hv
        change (F.boundaryMul (lowerCauchyFeatureAt v.val v.property).val : ℝ → ℂ) x /
          ((x:ℂ)-w.val) = _
        rw [hx,hv]
        rfl
    _ = _ := product_kernel_formula F v w

private def constantOneMultiplier : ClosedUpperHalfPlaneMultiplier where
  fn _ := 1
  bound := 1
  bound_nonneg := by norm_num
  diff _ _ := differentiableAt_const _
  norm_le _ _ := by simp

private theorem constant_one_hardy (u : UpperHardyL2) : constantOneMultiplier.hardyMul u = u := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [constantOneMultiplier.coe_boundaryMul u.val] with x hx
  change (constantOneMultiplier.boundaryMul u.val : ℝ → ℂ) x = u.val x
  simpa only [constantOneMultiplier,ClosedUpperHalfPlaneMultiplier.boundary,one_mul] using hx

private theorem multiplier_eval_feature (F : ClosedUpperHalfPlaneMultiplier)
    (v w : {z : ℂ // 0 < z.im}) :
    upperHardyCauchyEval w.val w.property (F.hardyMul (lowerCauchyFeatureAt v.val v.property)) =
      F.fn w.val * upperHardyCauchyEval w.val w.property (lowerCauchyFeatureAt v.val v.property) := by
  have h := closedUpperMultiplier_CauchyFeature_formula constantOneMultiplier v w
  rw [constant_one_hardy] at h
  rw [closedUpperMultiplier_CauchyFeature_formula,h]
  change 2*(Real.pi:ℂ)*I*(F.fn w.val/(w.val-(starRingEnd ℂ) v.val)) =
    F.fn w.val*(2*(Real.pi:ℂ)*I*(1/(w.val-(starRingEnd ℂ) v.val)))
  ring

/-- Every actual Hardy Cauchy evaluation intertwines boundary multiplication and analytic value. -/
theorem upperHardyCauchyEval_closedUpperMultiplier (F : ClosedUpperHalfPlaneMultiplier)
    (w : {z : ℂ // 0 < z.im}) (u : UpperHardyL2) :
    upperHardyCauchyEval w.val w.property (F.hardyMul u) =
      F.fn w.val * upperHardyCauchyEval w.val w.property u := by
  let T : UpperHardyL2 →L[ℂ] ℂ := (upperHardyCauchyEval w.val w.property).comp F.hardyMul -
    F.fn w.val • upperHardyCauchyEval w.val w.property
  let W : Submodule ℂ UpperHardyL2 := T.toLinearMap.ker
  have hclosed : IsClosed (W : Set UpperHardyL2) := isClosed_singleton.preimage T.continuous
  have hspan : Submodule.span ℂ (Set.range (fun v : {z : ℂ // 0 < z.im} =>
      lowerCauchyFeatureAt v.val v.property)) ≤ W := by
    rw [Submodule.span_le,Set.range_subset_iff]
    intro v
    change upperHardyCauchyEval w.val w.property (F.hardyMul (lowerCauchyFeatureAt v.val v.property)) -
      F.fn w.val * upperHardyCauchyEval w.val w.property (lowerCauchyFeatureAt v.val v.property) = 0
    rw [multiplier_eval_feature,sub_self]
  have hc := Submodule.topologicalClosure_minimal _ hspan hclosed
  rw [topologicalClosure_span_lowerCauchyFeatureAt_eq_top] at hc
  have hu := hc (show u ∈ (⊤ : Submodule ℂ UpperHardyL2) from trivial)
  change upperHardyCauchyEval w.val w.property (F.hardyMul u) -
    F.fn w.val * upperHardyCauchyEval w.val w.property u = 0 at hu
  exact sub_eq_zero.mp hu

/-- Cauchy features are exact adjoint eigenvectors of every actual bounded analytic multiplier. -/
theorem adjoint_closedUpperMultiplier_feature (F : ClosedUpperHalfPlaneMultiplier)
    (w : {z : ℂ // 0 < z.im}) :
    F.hardyMul.adjoint (lowerCauchyFeatureAt w.val w.property) =
      (starRingEnd ℂ) (F.fn w.val) • lowerCauchyFeatureAt w.val w.property := by
  apply ext_inner_right ℂ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_left,
    _root_.inner_smul_left (lowerCauchyFeatureAt w.val w.property) u ((starRingEnd ℂ) (F.fn w.val)),
    Complex.conj_conj]
  exact upperHardyCauchyEval_closedUpperMultiplier F w u

end
end GaloisForLFunctions.HTGeometry.FokasLenells
