import GaloisForLFunctions.HTGeometry.GaussianIntervalPositivity
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Standard Gaussian sublevel probability for a univariate polynomial

Every real point in the strict sublevel set lies within r of the real part of
a complex root. Each covering interval has Gaussian mass at most 2r.
-/
open MeasureTheory ProbabilityTheory Polynomial Set
namespace GaloisForLFunctions.HTGeometry
noncomputable section

private theorem radius_pow_le_product (R : Multiset ℂ) (x : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (h : ∀ z ∈ R, r ≤ ‖x-z‖) : r^R.card ≤ ‖(R.map (x-·)).prod‖ := by
  induction R using Multiset.induction_on with
  | empty => simp
  | cons a R ih =>
    rw [Multiset.card_cons,Multiset.map_cons,Multiset.prod_cons,norm_mul,pow_succ']
    exact mul_le_mul (h a (Multiset.mem_cons_self _ _))
      (ih (fun z hz => h z (Multiset.mem_cons_of_mem hz))) (pow_nonneg hr _) (norm_nonneg _)

private theorem near_root_of_polynomial_sublevel (p : ℂ[X]) {x : ℝ} (r : ℝ) (hr : 0 ≤ r)
    (h : ‖p.eval (x:ℂ)‖ < ‖p.leadingCoeff‖*r^p.natDegree) :
    ∃ z ∈ p.roots, |x-z.re| ≤ r := by
  by_contra! hfar
  have hsplit := IsAlgClosed.splits p
  have hl (z) (hz : z ∈ p.roots) : r ≤ ‖(x:ℂ)-z‖ := by
    apply (hfar z hz).le.trans
    exact Complex.abs_re_le_norm ((x:ℂ)-z)
  have he := mul_le_mul_of_nonneg_left (radius_pow_le_product p.roots (x:ℂ) r hr hl)
    (norm_nonneg p.leadingCoeff)
  rw [hsplit.eval_eq_prod_roots (x:ℂ),norm_mul,hsplit.natDegree_eq_card_roots] at h
  exact (not_lt_of_ge he) h

private theorem standard_gaussian_le_volume (s : Set ℝ) : gaussianReal 0 1 s ≤ volume s := by
  rw [gaussianReal_apply 0 one_ne_zero]
  have hpdf (x : ℝ) : gaussianPDF 0 1 x ≤ 1 := by
    change ENNReal.ofReal (gaussianPDFReal 0 1 x) ≤ 1
    rw [ENNReal.ofReal_le_one,gaussianPDFReal_def]
    have hroot : 1 ≤ Real.sqrt (2*Real.pi) := by
      apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
      linarith only [Real.pi_gt_three]
    have hExp : Real.exp (-(x-0)^2/(2*(1:ℝ))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by norm_num))
    simp only [NNReal.coe_one,mul_one]
    exact mul_le_one₀ (inv_le_one_of_one_le₀ hroot) (Real.exp_nonneg _) (by simpa using hExp)
  calc
    _ ≤ ∫⁻ _x in s, (1:ENNReal) := lintegral_mono hpdf
    _ = _ := by simp

/-- A univariate polynomial with complex roots has a small standard Gaussian
sublevel set at radius r to the power of its degree, relative to its leading
coefficient. -/
theorem gaussian_polynomial_sublevel (p : ℂ[X]) (r : ℝ) (hr : 0 ≤ r) :
    (gaussianReal 0 1).real {x : ℝ | ‖p.eval (x:ℂ)‖ < ‖p.leadingCoeff‖*r^p.natDegree} ≤
      2*p.natDegree*r := by
  classical
  let R := p.roots.toFinset
  let B (z : R) := Icc (z.val.re-r) (z.val.re+r)
  have hsub : {x : ℝ | ‖p.eval (x:ℂ)‖ < ‖p.leadingCoeff‖*r^p.natDegree} ⊆ ⋃ z : R, B z := by
    intro x hx
    obtain ⟨z,hz,hclose⟩ := near_root_of_polynomial_sublevel p r hr hx
    refine mem_iUnion.mpr ⟨⟨z,Multiset.mem_toFinset.mpr hz⟩,?_⟩
    obtain ⟨hl,hh⟩ := abs_le.mp hclose
    exact ⟨by change _ ≤ x; linarith,by change x ≤ _; linarith⟩
  have hi (z : R) : (gaussianReal 0 1).real (B z) ≤ 2*r := by
    have h := ENNReal.toReal_mono (measure_Icc_lt_top.ne) (standard_gaussian_le_volume (B z))
    change _ ≤ volume.real (B z) at h
    rw [show volume.real (B z) = 2*r by
      change volume.real (Icc (z.val.re - r) (z.val.re + r)) = 2*r
      rw [Real.volume_real_Icc_of_le (by linarith)]; ring] at h
    exact h
  have hcard : R.card ≤ p.natDegree := p.roots.toFinset_card_le.trans p.card_roots'
  have hR : (R.card:ℝ) ≤ p.natDegree := by exact_mod_cast hcard
  calc
    _ ≤ (gaussianReal 0 1).real (⋃ z : R, B z) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ z : R, (gaussianReal 0 1).real (B z) := measureReal_iUnion_fintype_le B
    _ ≤ ∑ _z : R, (2*r) := Finset.sum_le_sum fun z _ => hi z
    _ = R.card*(2*r) := by simp
    _ ≤ _ := by linarith only [mul_le_mul_of_nonneg_right hR hr]

#print axioms gaussian_polynomial_sublevel
end
end GaloisForLFunctions.HTGeometry
