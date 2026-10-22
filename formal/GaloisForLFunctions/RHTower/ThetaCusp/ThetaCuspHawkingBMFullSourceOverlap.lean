import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMGlobalScalarLift
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMGlobalAngularModularity
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMForcingRegularity
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices

/-!
The entire modular group preserves the literal Xi scalar. Every closed-cell overlap carries equal full-forcing germs, including elliptic corner overlaps.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups ContDiff
namespace RHTower.D4BMModularCore
open D4BMGlobalAngularResponse D4BMAngularSeries
noncomputable section

private theorem scalar_S (q : XiZeroCopy) (z : UpperHalfPlane) :
    scalar (center q) (coordinates (S • z)) = scalar (center q) (coordinates z) := by
  have h := xi_scalar_invert q ⟨z.re,z.im,z.im_pos⟩
  rw [UpperHalfPlane.modular_S_smul]
  simpa [coordinates,d4BMEisensteinInvertCoordinate,
    Complex.inv_re,Complex.inv_im,Complex.normSq_apply,sq,neg_div] using h

private theorem scalar_T (q : XiZeroCopy) (z : UpperHalfPlane) :
    scalar (center q) (coordinates (T • z)) = scalar (center q) (coordinates z) := by
  simp only [coordinates,ModularGroup.re_T_smul,ModularGroup.im_T_smul]
  simpa [scalar] using
    d4BM_completedEisensteinCuspLeg_scalar_periodic (center q) z.im z.re

/-- The literal Xi scalar is invariant under the entire modular group. -/
theorem xi_scalar_modular (q : XiZeroCopy) (A : SL(2, ℤ)) (z : UpperHalfPlane) :
    scalar (center q) (coordinates (A • z)) = scalar (center q) (coordinates z) := by
  have hA : A ∈ Subgroup.closure {S,T} := by simp [SpecialLinearGroup.SL2Z_generators]
  suffices ∀ z : UpperHalfPlane,
      scalar (center q) (coordinates (A • z)) = scalar (center q) (coordinates z) from this z
  induction hA using Subgroup.closure_induction with
  | mem g hg =>
    simp only [mem_insert_iff,mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact scalar_S q
    · exact scalar_T q
  | one => intro w; simp
  | mul g h _ _ ig ih => intro w; rw [mul_smul,ig,ih]
  | inv g _ ig => intro w; simpa using (ig (g⁻¹ • w)).symm

/-- A modular element with nonzero lower-left entry sends height y below 1/y. -/
theorem nonparabolic_height_le (A : SL(2, ℤ)) (hc : A 1 0 ≠ 0) (z : UpperHalfPlane) :
    (A • z).im ≤ 1/z.im := by
  rw [ModularGroup.im_smul_eq_div_normSq,denom_apply]
  rw [show 1/z.im = z.im/z.im^(2 : ℕ) by field_simp]
  gcongr
  rw [show Complex.normSq ((A 1 0)*z+(A 1 1)) =
    ((A 1 0 : ℝ)*z.re+(A 1 1 : ℝ))^(2 : ℕ)+(A 1 0 : ℝ)^(2 : ℕ)*z.im^(2 : ℕ) by
      simp [Complex.normSq_apply]; ring]
  have hs : (1 : ℝ) ≤ (A 1 0 : ℝ)^(2 : ℕ) := by
    exact_mod_cast (one_le_sq_iff_one_le_abs _).mpr (Int.one_le_abs hc)
  nlinarith [sq_nonneg ((A 1 0 : ℝ)*z.re+(A 1 1 : ℝ))]

/-- Every nontranslation overlap of the closed cell lies strictly below the cutoff in both charts. -/
theorem nonparabolic_cell_overlap_low (A : SL(2, ℤ)) (hc : A 1 0 ≠ 0)
    (z : UpperHalfPlane) (hz : z ∈ fd) (hAz : A • z ∈ fd) :
    z.im < 2 ∧ (A • z).im < 2 := by
  have hy : 1/2 < z.im := by
    nlinarith [three_le_four_mul_im_sq_of_mem_fd hz,z.im_pos]
  have hAy : 1/2 < (A • z).im := by
    nlinarith [three_le_four_mul_im_sq_of_mem_fd hAz,(A • z).im_pos]
  have hci : A⁻¹ 1 0 ≠ 0 := by
    simpa [Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two] using neg_ne_zero.mpr hc
  have hb := nonparabolic_height_le A hc z
  have hbi := nonparabolic_height_le A⁻¹ hci (A • z)
  simp only [inv_smul_smul] at hbi
  constructor
  · exact hbi.trans_lt ((div_lt_iff₀ (A • z).im_pos).mpr (by linarith))
  · exact hb.trans_lt ((div_lt_iff₀ z.im_pos).mpr (by linarith))

/-- The entire original forcing agrees on a neighborhood of every closed-cell modular overlap. -/
theorem forcing_cell_overlap_germ (q : XiZeroCopy) (branch : Bool) (A : SL(2, ℤ))
    (z : UpperHalfPlane) (hz : z ∈ fd) (hAz : A • z ∈ fd) :
    (fun w : UpperHalfPlane => forcing q branch (coordinates (A • w))) =ᶠ[𝓝 z]
      (fun w => forcing q branch (coordinates w)) := by
  by_cases hc : A 1 0 = 0
  · obtain ⟨n,hn⟩ := exists_eq_T_zpow_of_c_eq_zero hc
    apply Filter.Eventually.of_forall
    intro w
    change forcing q branch (coordinates (A • w)) = forcing q branch (coordinates w)
    rw [hn]
    have h := (forcing_periodic q branch).zsmul n (coordinates w)
    convert h using 1
    congr 1
    ext i
    fin_cases i <;>
      simp only [coordinates,Pi.add_apply,Pi.smul_apply,
        ModularGroup.re_T_zpow_smul,ModularGroup.im_T_zpow_smul] <;> simp
  · obtain ⟨hl,hr⟩ := nonparabolic_cell_overlap_low A hc z hz hAz
    have hleft : ∀ᶠ w : UpperHalfPlane in 𝓝 z, w.im < 2 :=
      (isOpen_lt UpperHalfPlane.continuous_im continuous_const).mem_nhds hl
    have hright : ∀ᶠ w : UpperHalfPlane in 𝓝 z, (A • w).im < 2 :=
      (isOpen_lt (UpperHalfPlane.continuous_im.comp (show Continuous (fun w : UpperHalfPlane => A • w) from by
          simp_rw [sl_moeb]; exact continuous_const_smul _))
        continuous_const).mem_nhds hr
    filter_upwards [hleft,hright] with w hw hAw
    rw [forcing_low q branch _ hAw,forcing_low q branch _ hw,xi_scalar_modular]

/-- The original chart forcing is smooth before gluing its compatible modular germs. -/
theorem forcing_chartSmooth (q : XiZeroCopy) (branch : Bool) :
    ChartSmooth (fun z => forcing q branch (coordinates z)) := by
  intro z
  have h := (forcingField_contDiffOn q branch).contDiffAt
    (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
  apply h.congr_of_eventuallyEq
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
  simp [forcingField,coordinates,UpperHalfPlane.ofComplex_apply_of_im_pos hw]

end
end RHTower.D4BMModularCore
