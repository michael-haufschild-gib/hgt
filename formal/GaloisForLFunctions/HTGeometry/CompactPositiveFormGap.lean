import GaloisForLFunctions.HTGeometry.BoundedPerturbedFriedrichsOperator
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-!
# Coercivity of positive identity-minus-compact forms

An injective positive compact perturbation of the identity has a quantitative
quadratic lower bound. The Fredholm alternative first controls its operator
norm from below; the positive-operator square inequality converts that bound
into coercivity of its form. No finite-dimensional truncation is needed.
-/

open Complex
open scoped InnerProduct
noncomputable section
namespace GaloisForLFunctions.HTGeometry
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem positiveOperator_norm_apply_sq_le (B : H →L[ℂ] H)
    (hB : ContinuousLinearMap.IsPositive B) (x : H) :
    ‖B x‖^2 ≤ ‖B‖ * (inner ℂ (B x) x).re := by
  have ho := positiveOperator_sq_le_norm_smul B hB
  have hp : ContinuousLinearMap.IsPositive (((‖B‖ : ℂ) • B)-B*B) :=
    (ContinuousLinearMap.le_def _ _).mp ho
  have hh := hp.re_inner_nonneg_left x
  change 0 ≤ (inner ℂ ((‖B‖ : ℂ) • B x-B (B x)) x).re at hh
  rw [inner_sub_left,Complex.sub_re,inner_smul_left] at hh
  have he : (inner ℂ (B (B x)) x).re = ‖B x‖^2 := by
    rw [hB.inner_left_eq_inner_right,inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [he] at hh
  simp only [Complex.conj_ofReal,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero] at hh
  linarith

/-- A positive injective identity-minus-compact form defines a Hilbert norm
equivalent to the original norm. -/
theorem exists_positive_form_scale_of_compact (K : H →L[ℂ] H)
    (hK : IsCompactOperator K)
    (hpos : ContinuousLinearMap.IsPositive (1-K))
    (hker : ∀ x : H, (1-K) x = 0 → x = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : H,
      ‖x‖^2 ≤ C * (inner ℂ ((1-K) x) x).re := by
  have hno : ¬ Module.End.HasEigenvalue K.toLinearMap 1 := by
    intro he
    obtain ⟨x,hx,hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot he
    apply hne
    apply hker
    have heq := Module.End.mem_eigenspace_iff.mp hx
    simpa only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,
      one_smul,heq,sub_self]
  obtain ⟨d,hd⟩ := hK.antilipschitz_of_not_hasEigenvalue (one_ne_zero : (1 : ℂ) ≠ 0) hno
  let r : ℝ := (d : ℝ)+1
  have hr : 0 < r := by dsimp only [r]; positivity
  let C : ℝ := r^2*(‖1-K‖+1)
  refine ⟨C,mul_pos (sq_pos_of_pos hr) (by positivity),fun x => ?_⟩
  have hbound : ‖x‖ ≤ r*‖(1-K) x‖ := by
    have hh := hd.le_mul_dist x 0
    simp only [dist_zero_right,map_zero,ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.one_apply,one_smul,
      norm_sub_rev] at hh
    have hextra := mul_nonneg (norm_nonneg (x-K x)) (by positivity : 0 ≤ (1 : ℝ))
    change ‖x‖ ≤ r*‖x-K x‖
    dsimp only [r]
    nlinarith
  have hs : ‖x‖^2 ≤ r^2*‖(1-K) x‖^2 := by
    have hh := (sq_le_sq₀ (norm_nonneg x) (mul_nonneg hr.le (norm_nonneg _))).mpr hbound
    simpa only [mul_pow] using hh
  have hnorm := positiveOperator_norm_apply_sq_le (1-K) hpos x
  have hscaled := mul_le_mul_of_nonneg_left hnorm (sq_nonneg r)
  have hq := hpos.re_inner_nonneg_left x
  change 0 ≤ (inner ℂ ((1-K) x) x).re at hq
  dsimp only [C]
  nlinarith [mul_nonneg (sq_nonneg r) hq]

end GaloisForLFunctions.HTGeometry
