import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSquareResidualModularBounds

/-! Uniform height-power bounds for the original residual on the full fundamental domain. -/
open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
open D4BMModularCore D4BMGlobalAngularResponse D4BMAngularSeries
noncomputable section

/-- Every fixed complex height weight preserves boundedness on the original fundamental domain. -/
theorem squareResidual_fd_weighted_bound (q : XiZeroCopy) (w : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : UpperHalfPlane, z ∈ fd →
      ‖(z.im:ℂ)^w * squareResidual q (coordinates z)‖ ≤ C := by
  have hc : Continuous (fun z : UpperHalfPlane => squareResidual q (coordinates z)) :=
    (squareResidual_continuousOn q).comp_continuous (by
      apply continuous_pi; intro i; fin_cases i
      · exact UpperHalfPlane.continuous_re
      · exact UpperHalfPlane.continuous_im) (fun z => z.im_pos)
  have hw : Continuous (fun z : UpperHalfPlane => (z.im:ℂ)^w) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr z.im_pos.ne')).comp
      UpperHalfPlane.continuous_im.continuousAt
  obtain ⟨A,hA⟩ := (truncated_cell_compact 4).exists_bound_of_continuousOn (hw.mul hc).continuousOn
  obtain ⟨B,hB,hb⟩ := weighted_squareRemainder_bounded (center q) w 3 (by norm_num)
  refine ⟨max 0 (max A (B/2)),le_max_left _ _,?_⟩
  intro z hz
  by_cases hy : z.im ≤ 4
  · exact (hA z ⟨hz,hy⟩).trans ((le_max_left _ _).trans (le_max_right _ _))
  · have h3 : 3 < z.im := by linarith
    rw [squareResidual_high q _ h3,← mul_div_assoc,norm_div]
    norm_num only [Complex.norm_ofNat]
    exact (div_le_div_of_nonneg_right (hb (coordinates z) h3.le) (by norm_num)).trans
      ((le_max_right _ _).trans (le_max_right _ _))

/-- Two endpoint weights dominate every complex height power with intermediate real part. -/
theorem squareResidual_fd_uniform_weight_bound (q : XiZeroCopy) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : ℂ) (z : UpperHalfPlane),
      a ≤ w.re → w.re ≤ b → z ∈ fd →
      ‖(z.im:ℂ)^w * squareResidual q (coordinates z)‖ ≤ C := by
  obtain ⟨A,hA,ha⟩ := squareResidual_fd_weighted_bound q (a:ℂ)
  obtain ⟨B,hB,hb⟩ := squareResidual_fd_weighted_bound q (b:ℂ)
  refine ⟨A+B,add_nonneg hA hB,?_⟩
  intro w z hwa hwb hz
  have hbound : z.im^w.re ≤ z.im^a + z.im^b := by
    by_cases h : z.im ≤ 1
    · exact (Real.rpow_le_rpow_of_exponent_ge z.im_pos h hwa).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg z.im_pos.le _))
    · exact (Real.rpow_le_rpow_of_exponent_le (le_of_not_ge h) hwb).trans
        (le_add_of_nonneg_left (Real.rpow_nonneg z.im_pos.le _))
  have ha' := ha z hz
  have hb' := hb z hz
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos z.im_pos,Complex.ofReal_re] at ha' hb'
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos z.im_pos]
  calc
    _ ≤ (z.im^a + z.im^b)*‖squareResidual q (coordinates z)‖ :=
      mul_le_mul_of_nonneg_right hbound (norm_nonneg _)
    _ ≤ A+B := by rw [add_mul]; exact add_le_add ha' hb'

end
end RHTower.D4BMJointSource
