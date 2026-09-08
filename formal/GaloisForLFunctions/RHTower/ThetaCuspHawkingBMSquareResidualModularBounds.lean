import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSquareResidualModular
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMWeightedSquareCuspBound
import GaloisForLFunctions.HTGeometry.UpperHalfPlaneStripIntegral

/-! Global and full-cusp bounds for the actual modular extension of the native residual. -/
open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups
namespace RHTower.D4BMJointSource
open D4BMModularCore D4BMGlobalAngularResponse D4BMAngularSeries
noncomputable section

/-- Compact lower-cell control and the complete tail bound give one native uniform bound. -/
theorem squareResidual_cell_bound (q : XiZeroCopy) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : UpperHalfPlane, z ∈ fd → ‖squareResidual q (coordinates z)‖ ≤ C := by
  have hc : Continuous (fun z : UpperHalfPlane => squareResidual q (coordinates z)) :=
    (squareResidual_continuousOn q).comp_continuous (by
      apply continuous_pi; intro i; fin_cases i
      · exact UpperHalfPlane.continuous_re
      · exact UpperHalfPlane.continuous_im) (fun z => z.im_pos)
  obtain ⟨A,hA⟩ := (truncated_cell_compact 4).exists_bound_of_continuousOn hc.continuousOn
  obtain ⟨B,hB,hb⟩ := squareRemainder_bounded (center q) 3 (by norm_num)
  refine ⟨max 0 (max A (B/2)),le_max_left _ _,?_⟩
  intro z hz
  by_cases hy : z.im ≤ 4
  · exact (hA z ⟨hz,hy⟩).trans ((le_max_left _ _).trans (le_max_right _ _))
  · have h3 : 3 < z.im := by linarith
    rw [squareResidual_high q _ h3,norm_div]
    norm_num only [Complex.norm_ofNat]
    exact (div_le_div_of_nonneg_right (hb (coordinates z) h3.le) (by norm_num)).trans
      ((le_max_right _ _).trans (le_max_right _ _))

/-- The constructed modular residual is uniformly bounded on the whole upper half-plane. -/
theorem globalSquareResidual_bounded (q : XiZeroCopy) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : UpperHalfPlane, ‖globalSquareResidual q z‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := squareResidual_cell_bound q
  refine ⟨C,hC,?_⟩
  intro z
  obtain ⟨A,hA⟩ := exists_smul_mem_fd z
  have he := globalSquareResidual_invariant q (QuotientGroup.mk A) z
  simp only [PSL2Z_mk_smul] at he
  rw [← he,globalSquareResidual_eq_on_fd q _ hA]
  exact hb _ hA

/-- On the entire high modular strip the extension retains the literal original residual. -/
theorem globalSquareResidual_eq_high_strip (q : XiZeroCopy) (z : UpperHalfPlane)
    (hz : z ∈ modularStrip) (hy : 3 < z.im) :
    globalSquareResidual q z = squareResidual q (coordinates z) := by
  by_cases hx : z.re ≤ 1/2
  · apply globalSquareResidual_eq_on_fd
    constructor
    · change 1 ≤ z.re*z.re+z.im*z.im
      nlinarith [sq_nonneg z.re]
    · exact abs_le.mpr ⟨by linarith [hz.1],hx⟩
  · let z' := T^(-1:ℤ) • z
    have hi : z'.im = z.im := by
      change (T^(-1:ℤ) • z).im = z.im
      rw [ModularGroup.im_T_zpow_smul]
    have hr : z'.re = z.re-1 := by
      change (T^(-1:ℤ) • z).re = z.re-1
      rw [ModularGroup.re_T_zpow_smul]
      norm_num
      ring
    have hf : z' ∈ fd := by
      constructor
      · change 1 ≤ z'.re*z'.re+z'.im*z'.im
        rw [hi]
        nlinarith [sq_nonneg z'.re]
      · rw [hr]
        exact abs_le.mpr ⟨by linarith,by linarith [hz.2]⟩
    have he := globalSquareResidual_invariant q (cuspTranslation (-1)) z
    change globalSquareResidual q z' = globalSquareResidual q z at he
    rw [← he,globalSquareResidual_eq_on_fd q z' hf]
    exact squareResidual_translate q (-1) z

/-- Every complex height weight is bounded on the actual full high-strip source. -/
theorem globalSquareResidual_strip_weighted_bound (q : XiZeroCopy) (w : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : UpperHalfPlane, z ∈ modularStrip → 3 < z.im →
      ‖(z.im:ℂ)^w*globalSquareResidual q z‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := weighted_squareRemainder_bounded (center q) w 3 (by norm_num)
  refine ⟨C/2,by positivity,?_⟩
  intro z hz hy
  rw [globalSquareResidual_eq_high_strip q z hz hy,squareResidual_high q _ hy,
    ← mul_div_assoc,norm_div]
  norm_num only [Complex.norm_ofNat]
  exact div_le_div_of_nonneg_right (hb (coordinates z) hy.le) (by norm_num)

end
end RHTower.D4BMJointSource
