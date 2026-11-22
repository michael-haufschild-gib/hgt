import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Diameter of a chordal cap in a real Hilbert space -/
open Real
namespace GaloisForLFunctions.HTGeometry.AngularError
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Two equal-length vectors at chord error 2 sin θ from the same
direction are at most 2 sin(2θ) apart, in units of their common length. -/
theorem common_chord {x y z : E} {θ : ℝ} (ht : 0≤θ) (hθ : 2*θ≤π/2)
    (hx : ‖x‖=‖y‖) (hz : ‖z‖=‖y‖)
    (hxy : ‖x-y‖ ≤ 2*sin θ*‖y‖) (hzy : ‖z-y‖ ≤ 2*sin θ*‖y‖) :
    ‖x-z‖ ≤ 2*sin (2*θ)*‖y‖ := by
  by_cases h : ‖y‖=0
  · have h₁ := norm_eq_zero.mp (hx.trans h)
    have h₂ := norm_eq_zero.mp (hz.trans h)
    simp only [h₁,h₂,sub_self,norm_zero,h,mul_zero,le_refl]
  have hR := lt_of_le_of_ne (norm_nonneg y) (Ne.symm h)
  have hs := sin_nonneg_of_nonneg_of_le_pi ht (by linarith only [ht,hθ,pi_pos])
  have hc := cos_nonneg_of_mem_Icc ⟨by linarith only [ht,pi_pos],hθ⟩
  have hdouble := sin_nonneg_of_nonneg_of_le_pi (mul_nonneg two_pos.le ht) (by linarith only [hθ,pi_pos])
  have proj (v : E) (hv : ‖v‖=‖y‖) (hd : ‖v-y‖≤2*sin θ*‖y‖) :
      cos (2*θ)*‖y‖^2 ≤ inner ℝ v y := by
    have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (mul_nonneg two_pos.le hs) hR.le)).mpr hd
    rw [norm_sub_sq_real,hv] at hsq
    rw [cos_two_mul_eq_one_sub]
    nlinarith only [hsq]
  have hm := real_inner_le_norm (x+z) y
  rw [inner_add_left] at hm
  have hmid : 2*cos (2*θ)*‖y‖ ≤ ‖x+z‖ := by
    apply le_of_mul_le_mul_right (a := ‖y‖) _ hR
    nlinarith only [proj x hx hxy,proj z hz hzy,hm]
  have hsq := (sq_le_sq₀ (mul_nonneg (mul_nonneg two_pos.le hc) hR.le) (norm_nonneg _)).mpr hmid
  have hp := parallelogram_law_with_norm_mul (𝕜 := ℝ) x z
  rw [hx,hz] at hp
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (mul_nonneg two_pos.le hdouble) hR.le)).mp
  have hid := congrArg (fun k : ℝ => 4*‖y‖^2*k) (sin_sq_add_cos_sq (2*θ))
  nlinarith only [hsq,hp,hid]

end GaloisForLFunctions.HTGeometry.AngularError
