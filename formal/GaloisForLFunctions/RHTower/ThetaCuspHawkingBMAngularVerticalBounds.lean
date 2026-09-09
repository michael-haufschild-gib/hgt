import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalCoreCutoff

/-! Cusp bounds for the actual vertical derivative of the complete physical angular field. -/
open Complex Real Set Filter Topology MeasureTheory
open scoped ContDiff
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
namespace RHTower.D4BMAngularSeries
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Every derivative-stable Fourier family has a uniformly bounded vertical derivative above fixed positive height. -/
theorem value_vertical_bounded (u nu : ℂ) (a : ℝ) (d : ℕ) (negative : Bool)
    (l : ℝ) (hl : 0 < l) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin 2 → ℝ, l ≤ z 1 →
      ‖coordDeriv 1 (value u nu a d negative) z‖ ≤ C := by
  obtain ⟨A,hA,h0⟩ := weighted_value_bounded u nu 0 (a-1) d negative l hl
  obtain ⟨B,hB,h1⟩ := weighted_value_bounded u (nu+1) 0 a (d+1) negative l hl
  obtain ⟨C,hC,h2⟩ := weighted_value_bounded u (nu-1) 0 a (d+1) negative l hl
  simp only [Complex.cpow_zero,one_mul] at h0 h1 h2
  refine ⟨‖(a:ℂ)‖*A+‖(Real.pi:ℂ)‖*(B+C),by positivity,?_⟩
  intro z hz
  rw [value_coordDeriv_one u nu a d negative z (hl.trans_le hz)]
  calc
    _ ≤ ‖(a:ℂ)*value u nu (a-1) d negative z‖+
        ‖(Real.pi:ℂ)*(value u (nu+1) a (d+1) negative z+value u (nu-1) a (d+1) negative z)‖ :=
      norm_sub_le _ _
    _ ≤ _ := by
      rw [norm_mul,norm_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left (h0 z hz) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add (h1 z hz) (h2 z hz))) (norm_nonneg _))

end
end RHTower.D4BMAngularSeries

namespace RHTower.D4BMGlobalAngularResponse
open D4BMAngularSeries
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The actual full tail derivative retains both signed Fourier families and their original factor two. -/
theorem tail_vertical_eq (u : ℂ) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    coordDeriv 1 (tail u) z = 2*(coordDeriv 1 (value u u (1/2) 0 false) z+
      coordDeriv 1 (value u u (1/2) 0 true) z) := by
  have he : tail u =ᶠ[𝓝 z] fun w => 2*(value u u (1/2) 0 false w+value u u (1/2) 0 true w) := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz] with w hw
    simp only [tail,d4BMCompletedEisensteinCuspTailPart,d4BMCompletedEisensteinFullSignedZeroWord,
      signedTail_eq_value _ _ _ _ _ w hw,Nat.cast_zero,zero_add]
  have h0 := (value_hasFDerivAt u u (1/2) 0 false z hz).differentiableAt
  have h1 := (value_hasFDerivAt u u (1/2) 0 true z hz).differentiableAt
  unfold coordDeriv
  rw [he.fderiv_eq,fderiv_const_mul (h0.fun_add h1),fderiv_fun_add h0 h1]
  simp only [smul_apply,add_apply,smul_eq_mul]

/-- The complete untruncated scalar tail has a bounded ordinary vertical derivative in every positive cusp. -/
theorem tail_vertical_bounded (u : ℂ) (l : ℝ) (hl : 0 < l) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin 2 → ℝ, l ≤ z 1 → ‖coordDeriv 1 (tail u) z‖ ≤ C := by
  obtain ⟨A,hA,ha⟩ := value_vertical_bounded u u (1/2) 0 false l hl
  obtain ⟨B,hB,hb⟩ := value_vertical_bounded u u (1/2) 0 true l hl
  refine ⟨2*(A+B),by positivity,?_⟩
  intro z hz
  rw [tail_vertical_eq u z (hl.trans_le hz),norm_mul]
  norm_num only [Complex.norm_ofNat]
  exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add (ha z hz) (hb z hz))) (by norm_num)

end
end RHTower.D4BMGlobalAngularResponse
