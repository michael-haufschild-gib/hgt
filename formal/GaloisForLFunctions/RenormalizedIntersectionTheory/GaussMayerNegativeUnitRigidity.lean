import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerDerivativeCone

/-!
# Negative-unit rigidity of the actual Mayer remainder

For a positive real source parameter, the actual derivative of `R(w)1`
is strictly negative on `[0,1]`. Positivity of the normalized source
functional and compact extrema force every negative-unit derivative
eigenfunction to vanish at zero. The common first-branch contribution
then contracts oscillation and makes its normalized derivative constant.

Both complex components and the analytic identity principle recover the
exact function: every such derivative eigenfunction is a scalar multiple
of `1-(1+z)^(-w)`. The actual response identity excludes a nonzero
negative-unit eigenfunction of the remainder itself.
-/

open Complex Metric Set Filter Topology
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCutoff
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerParameter
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerDerivative
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerPositive
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerNegativePole

private theorem branch_constant_derivative {w : ℝ} (hw : 0 < w) {n : ℕ}
    (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    -deriv (plane (branch (w : ℂ) hw n hn (constant 1))) (x : ℂ) =
      ((w*((n : ℝ)+x)^(-w-1) : ℝ) : ℂ) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : 0 < (n : ℝ)+x := by linarith only [hn',hx.1]
  have hu : ((n : ℝ)+x)⁻¹ ∈ Icc (0 : ℝ) 1 :=
    ⟨(inv_pos.mpr ha).le,(inv_le_one₀ ha).mpr (by linarith only [hn',hx.1])⟩
  have huD := interval_mem_smallDisc hu
  have huout := closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 3/2) huD
  have hd : deriv (plane (constant 1)) ((((n : ℝ)+x)⁻¹ : ℝ) : ℂ) = 0 :=
    derivativeEvaluation_constant _ huD 1
  have hv : plane (constant 1) ((((n : ℝ)+x)⁻¹ : ℝ) : ℂ) = 1 := by
    rw [plane_eq (constant 1) ⟨_,huout⟩]
    rfl
  rw [neg_deriv_branch_real hw hn (constant 1) hx,hv,hd,mul_one,mul_zero,add_zero]

/-- The actual constant-response derivative is strictly negative and real on the source interval. -/
theorem remainder_constant_derivative {w : ℝ} (hw : 0 < w) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    (deriv (plane (remainder (w : ℂ) (constant 1))) (x : ℂ)).im = 0 ∧
    (deriv (plane (remainder (w : ℂ) (constant 1))) (x : ℂ)).re < 0 := by
  have hs := (hasSum_deriv_branch (w := (w : ℂ)) hw (constant 1) (x : ℂ) (interval_mem_smallDisc hx)).neg
  have hre := Complex.reCLM.hasSum hs
  have him := Complex.imCLM.hasSum hs
  have hterms (n : ℕ) :
      -deriv (plane (branch (w : ℂ) hw (n+1) (Nat.succ_pos n) (constant 1))) (x : ℂ) =
        ((w*(((n+1 : ℕ) : ℝ)+x)^(-w-1) : ℝ) : ℂ) :=
    branch_constant_derivative hw (Nat.succ_pos n) hx
  have him0 : HasSum (fun _ : ℕ => (0 : ℝ))
      (-deriv (plane (remainder (w : ℂ) (constant 1))) (x : ℂ)).im := by
    convert him using 1
    · funext n
      change (0 : ℝ) = (-deriv (plane (branch (w : ℂ) hw (n+1)
        (Nat.succ_pos n) (constant 1))) (x : ℂ)).im
      rw [hterms,Complex.ofReal_im]
    · rfl
  have himzero := him0.unique hasSum_zero
  have hsplit := hre.summable.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at hsplit
  rw [hre.tsum_eq] at hsplit
  have hnonneg (n : ℕ) :
      0 ≤ (-deriv (plane (branch (w : ℂ) hw (n+1) (Nat.succ_pos n)
        (constant 1))) (x : ℂ)).re := by
    rw [hterms,Complex.ofReal_re]
    exact mul_nonneg hw.le (Real.rpow_nonneg (add_nonneg (Nat.cast_nonneg (n+1)) hx.1) _)
  have htail : 0 ≤ ∑' k : ℕ, (-deriv (plane (branch (w : ℂ) hw
      (k+1+1) (Nat.succ_pos (k+1)) (constant 1))) (x : ℂ)).re :=
    tsum_nonneg fun k => hnonneg (k+1)
  have hfirst : 0 < (-deriv (plane (branch (w : ℂ) hw 1 le_rfl
      (constant 1))) (x : ℂ)).re := by
    rw [branch_constant_derivative hw le_rfl hx,Complex.ofReal_re]
    exact mul_pos hw (Real.rpow_pos_of_pos (by norm_num; linarith only [hx.1]) _)
  change (-deriv (plane (branch (w : ℂ) hw 1 le_rfl (constant 1))) (x : ℂ)).re +
    (∑' k : ℕ, (-deriv (plane (branch (w : ℂ) hw (k+1+1)
      (Nat.succ_pos (k+1)) (constant 1))) (x : ℂ)).re) =
        (-deriv (plane (remainder (w : ℂ) (constant 1))) (x : ℂ)).re at hsplit
  simp only [Complex.neg_im] at himzero
  refine ⟨neg_eq_zero.mp himzero,?_⟩
  simp only [Complex.neg_re] at hsplit htail hfirst
  linarith only [hfirst,htail,hsplit]

#print axioms remainder_constant_derivative
/-- The actual negative derivative, normalized by the positive successor response. -/
def averagedDerivative (w x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : DiscSpace →L[ℂ] ℂ :=
  (-(ground w x : ℂ)⁻¹) •
    ((derivativeEvaluation (x : ℂ) (interval_mem_smallDisc hx)).comp (remainder (w : ℂ)))

private theorem averagedDerivative_apply (w x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1)
    (f : DiscSpace) : averagedDerivative w x hx f =
      -(ground w x : ℂ)⁻¹*deriv (plane (remainder (w : ℂ) f)) (x : ℂ) := rfl

private theorem averagedDerivative_real (w x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1)
    (f : DiscSpace) : (averagedDerivative w x hx f).re =
      -(deriv (plane (remainder (w : ℂ) f)) (x : ℂ)).re/ground w x := by
  rw [averagedDerivative_apply]
  have hi : -(ground w x : ℂ)⁻¹ = ((-(ground w x)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [hi]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [div_eq_mul_inv]
  ring

private theorem averagedDerivative_response {w : ℝ} (hw : 0 < w) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    averagedDerivative w x hx (MayerCancellation.response (w : ℂ)) = 1 := by
  change -(ground w x : ℂ)⁻¹*derivativeEvaluation (x : ℂ) (interval_mem_smallDisc hx)
    (remainder (w : ℂ) (MayerCancellation.response (w : ℂ))) = 1
  rw [MayerCancellation.remainder_response hw,map_sub,derivativeEvaluation_constant,
    zero_sub,neg_mul_neg]
  change (ground w x : ℂ)⁻¹*deriv (plane (MayerCancellation.response (w : ℂ))) (x : ℂ) = 1
  rw [deriv_response_real w hx,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (ground_pos hw hx).ne')]

private theorem averagedDerivative_nonneg {w : ℝ} (hw : 0 < w) (f : DiscSpace)
    (hf0 : f.1 zeroPoint = 0)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ (deriv (plane f) (t : ℂ)).re)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    0 ≤ (averagedDerivative w x hx f).re := by
  have hm := monotoneOn_real_plane f hf (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1)
    (by norm_num : (1/2 : ℝ) ∈ Icc (0 : ℝ) 1) (by norm_num : (0 : ℝ) ≤ 1/2)
  have hm' : 0 ≤ (plane f (1/2 : ℂ)).re := by
    simpa [plane_zero,hf0] using hm
  have hs := source_minorization hw f hf0 hf hx
  have hn : 0 ≤ -(deriv (plane (remainder (w : ℂ) f)) (x : ℂ)).re := by
    simpa only [Complex.neg_re] using
      (mul_nonneg (ground_pos hw hx).le hm').trans hs
  rw [averagedDerivative_real]
  exact div_nonneg hn (ground_pos hw hx).le

private theorem averagedDerivative_constant {w : ℝ} (hw : 0 < w) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    (averagedDerivative w x hx (constant 1)).im = 0 ∧
      0 < (averagedDerivative w x hx (constant 1)).re := by
  obtain ⟨hi,hr⟩ := remainder_constant_derivative hw hx
  refine ⟨?_,?_⟩
  · rw [averagedDerivative_apply]
    have he : -(ground w x : ℂ)⁻¹ = ((-(ground w x)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [he]
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,hi,mul_zero,zero_mul,add_zero]
  · rw [averagedDerivative_real]
    exact div_pos (neg_pos.mpr hr) (ground_pos hw hx)

private theorem response_zero (w : ℂ) : (MayerCancellation.response w).1 zeroPoint = 0 := by
  rw [MayerCancellation.response_apply]
  change 1-(1+0 : ℂ)^(-w) = 0
  simp only [add_zero,Complex.one_cpow,sub_self]

/-- Source positivity and the exact response give unit-mass bounds for every centered normalized jet. -/
theorem averagedDerivative_bounds {w : ℝ} (hw : 0 < w) (f : DiscSpace)
    (hf0 : f.1 zeroPoint = 0) {m M : ℝ}
    (hb : ∀ t ∈ Icc (0 : ℝ) 1,
      m ≤ normalizedDerivative w f t ∧ normalizedDerivative w f t ≤ M)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    m ≤ (averagedDerivative w x hx f).re ∧
      (averagedDerivative w x hx f).re ≤ M := by
  have hzlo : (f-(m : ℂ) • MayerCancellation.response (w : ℂ)).1 zeroPoint = 0 := by
    change f.1 zeroPoint-(m : ℂ)*(MayerCancellation.response (w : ℂ)).1 zeroPoint = 0
    rw [hf0,response_zero,mul_zero,sub_zero]
  have hzhi : ((M : ℂ) • MayerCancellation.response (w : ℂ)-f).1 zeroPoint = 0 := by
    change (M : ℂ)*(MayerCancellation.response (w : ℂ)).1 zeroPoint-f.1 zeroPoint = 0
    rw [hf0,response_zero,mul_zero,sub_zero]
  have hdlo : ∀ t ∈ Icc (0 : ℝ) 1,
      0 ≤ (deriv (plane (f-(m : ℂ) • MayerCancellation.response (w : ℂ))) (t : ℂ)).re := by
    intro t ht
    have h := (le_div_iff₀ (ground_pos hw ht)).mp ((hb t ht).1)
    change 0 ≤ (derivativeEvaluation (t : ℂ) (interval_mem_smallDisc ht)
      (f-(m : ℂ) • MayerCancellation.response (w : ℂ))).re
    rw [map_sub,map_smul]
    change 0 ≤ (deriv (plane f) (t : ℂ)-
      (m : ℂ)*deriv (plane (MayerCancellation.response (w : ℂ))) (t : ℂ)).re
    rw [deriv_response_real w ht]
    simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    exact sub_nonneg.mpr h
  have hdhi : ∀ t ∈ Icc (0 : ℝ) 1,
      0 ≤ (deriv (plane ((M : ℂ) • MayerCancellation.response (w : ℂ)-f)) (t : ℂ)).re := by
    intro t ht
    have h := (div_le_iff₀ (ground_pos hw ht)).mp ((hb t ht).2)
    change 0 ≤ (derivativeEvaluation (t : ℂ) (interval_mem_smallDisc ht)
      ((M : ℂ) • MayerCancellation.response (w : ℂ)-f)).re
    rw [map_sub,map_smul]
    change 0 ≤ ((M : ℂ)*deriv (plane (MayerCancellation.response (w : ℂ))) (t : ℂ)-
      deriv (plane f) (t : ℂ)).re
    rw [deriv_response_real w ht]
    simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    exact sub_nonneg.mpr h
  have hlo := averagedDerivative_nonneg hw _ hzlo hdlo hx
  have hhi := averagedDerivative_nonneg hw _ hzhi hdhi hx
  rw [map_sub,map_smul,averagedDerivative_response hw hx] at hlo hhi
  simp only [smul_eq_mul,mul_one,Complex.sub_re,Complex.ofReal_re] at hlo hhi
  exact ⟨by linarith only [hlo],by linarith only [hhi]⟩

#print axioms averagedDerivative_bounds

private theorem averagedDerivative_negative_eigen_real {w : ℝ} (f : DiscSpace)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (he : deriv (plane (remainder (w : ℂ) f)) (x : ℂ) = -deriv (plane f) (x : ℂ)) :
    (averagedDerivative w x hx f).re = normalizedDerivative w f x := by
  rw [averagedDerivative_real,he,Complex.neg_re,neg_neg]
  rfl

private theorem real_evaluation_zero_of_negative_derivative_eigen {w : ℝ} (hw : 0 < w)
    (f : DiscSpace)
    (he : ∀ x ∈ Icc (0 : ℝ) 1,
      deriv (plane (remainder (w : ℂ) f)) (x : ℂ) = -deriv (plane f) (x : ℂ)) :
    (f.1 zeroPoint).re = 0 := by
  let a : ℂ := f.1 zeroPoint
  let g : DiscSpace := f-a • constant 1
  have hg0 : g.1 zeroPoint = 0 := by
    change a-a*1 = 0
    ring
  have hdg (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      deriv (plane g) (x : ℂ) = deriv (plane f) (x : ℂ) := by
    change derivativeEvaluation (x : ℂ) (interval_mem_smallDisc hx) (f-a • constant 1) =
      derivativeEvaluation (x : ℂ) (interval_mem_smallDisc hx) f
    rw [map_sub,map_smul,derivativeEvaluation_constant,smul_zero,sub_zero]
  have hrel (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      (averagedDerivative w x hx g).re = normalizedDerivative w g x-
        a.re*(averagedDerivative w x hx (constant 1)).re := by
    change (averagedDerivative w x hx (f-a • constant 1)).re = _
    rw [map_sub,map_smul]
    simp only [smul_eq_mul,Complex.sub_re,Complex.mul_re]
    rw [(averagedDerivative_constant hw hx).1,mul_zero,sub_zero,
      averagedDerivative_negative_eigen_real f hx (he x hx)]
    unfold normalizedDerivative
    rw [hdg x hx]
  have hn : (Icc (0 : ℝ) 1).Nonempty := ⟨0,by norm_num⟩
  obtain ⟨u,hu,hmin⟩ := isCompact_Icc.exists_isMinOn hn (normalizedDerivative_continuous hw g)
  obtain ⟨v,hv,hmax⟩ := isCompact_Icc.exists_isMaxOn hn (normalizedDerivative_continuous hw g)
  have hb (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      normalizedDerivative w g u ≤ normalizedDerivative w g x ∧
      normalizedDerivative w g x ≤ normalizedDerivative w g v := ⟨hmin hx,hmax hx⟩
  have hlo := (averagedDerivative_bounds hw g hg0 hb hu).1
  have hhi := (averagedDerivative_bounds hw g hg0 hb hv).2
  rw [hrel u hu] at hlo
  rw [hrel v hv] at hhi
  have hle : a.re ≤ 0 := by
    by_contra hh
    have hp := mul_pos (lt_of_not_ge hh) (averagedDerivative_constant hw hu).2
    linarith only [hlo,hp]
  have hge : 0 ≤ a.re := by
    by_contra hh
    have hp := mul_neg_of_neg_of_pos (lt_of_not_ge hh) (averagedDerivative_constant hw hv).2
    linarith only [hhi,hp]
  exact le_antisymm hle hge

/-- A negative-unit derivative eigenfunction must already vanish at zero; no centering premise is needed. -/
theorem evaluation_zero_of_negative_derivative_eigen {w : ℝ} (hw : 0 < w)
    (f : DiscSpace)
    (he : ∀ x ∈ Icc (0 : ℝ) 1,
      deriv (plane (remainder (w : ℂ) f)) (x : ℂ) = -deriv (plane f) (x : ℂ)) :
    f.1 zeroPoint = 0 := by
  have hr := real_evaluation_zero_of_negative_derivative_eigen hw f he
  have hIe : ∀ x ∈ Icc (0 : ℝ) 1,
      deriv (plane (remainder (w : ℂ) (I • f))) (x : ℂ) =
        -deriv (plane (I • f)) (x : ℂ) := by
    intro x hx
    change derivativeEvaluation (x : ℂ) (interval_mem_smallDisc hx)
      (remainder (w : ℂ) (I • f)) =
        -derivativeEvaluation (x : ℂ) (interval_mem_smallDisc hx) (I • f)
    rw [map_smul,map_smul,map_smul]
    change I*deriv (plane (remainder (w : ℂ) f)) (x : ℂ) =
      -(I*deriv (plane f) (x : ℂ))
    rw [he x hx,mul_neg]
  have hi := real_evaluation_zero_of_negative_derivative_eigen hw (I • f) hIe
  change (I*f.1 zeroPoint).re = 0 at hi
  simp only [Complex.mul_re,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_sub] at hi
  exact Complex.ext hr (neg_eq_zero.mp hi)

#print axioms evaluation_zero_of_negative_derivative_eigen

private theorem contraction_lt_one {w : ℝ} (hw : 0 < w) : contraction w < 1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hw])

private theorem minorized_negative_eigen_real {w : ℝ} (f : DiscSpace)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (he : deriv (plane (remainder (w : ℂ) f)) (x : ℂ) = -deriv (plane f) (x : ℂ)) :
    (minorizedDerivative w x hx f).re =
      normalizedDerivative w f x-(plane f (1/2 : ℂ)).re := by
  rw [minorizedDerivative_apply,he,neg_mul_neg]
  have hi : (ground w x : ℂ)⁻¹ = (((ground w x)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [hi]
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  unfold normalizedDerivative
  rw [div_eq_mul_inv]
  ring

private theorem normalizedDerivative_constant_of_negative_eigen {w : ℝ} (hw : 0 < w)
    (f : DiscSpace) (hf0 : f.1 zeroPoint = 0)
    (he : ∀ x ∈ Icc (0 : ℝ) 1,
      deriv (plane (remainder (w : ℂ) f)) (x : ℂ) = -deriv (plane f) (x : ℂ)) :
    ∃ c : ℝ, ∀ x ∈ Icc (0 : ℝ) 1, normalizedDerivative w f x = c := by
  have hn : (Icc (0 : ℝ) 1).Nonempty := ⟨0,by norm_num⟩
  obtain ⟨u,hu,hmin⟩ := isCompact_Icc.exists_isMinOn hn (normalizedDerivative_continuous hw f)
  obtain ⟨v,hv,hmax⟩ := isCompact_Icc.exists_isMaxOn hn (normalizedDerivative_continuous hw f)
  have hb (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      normalizedDerivative w f u ≤ normalizedDerivative w f x ∧
      normalizedDerivative w f x ≤ normalizedDerivative w f v := ⟨hmin hx,hmax hx⟩
  have hlo := (minorizedDerivative_bounds hw f hf0 hb hu).1
  have hhi := (minorizedDerivative_bounds hw f hf0 hb hv).2
  rw [minorized_negative_eigen_real f hu (he u hu)] at hlo
  rw [minorized_negative_eigen_real f hv (he v hv)] at hhi
  have hle : normalizedDerivative w f v ≤ normalizedDerivative w f u := by
    by_contra hh
    have hp := mul_pos (sub_pos.mpr (contraction_lt_one hw)) (sub_pos.mpr (lt_of_not_ge hh))
    nlinarith only [hlo,hhi,hp]
  have heq := le_antisymm hle (hmin hv)
  exact ⟨normalizedDerivative w f u,fun x hx =>
    le_antisymm ((hmax hx).trans_eq heq) (hmin hx)⟩

private theorem real_plane_response_of_constant_jet {w : ℝ} (hw : 0 < w)
    (f : DiscSpace) (hf0 : f.1 zeroPoint = 0) (c : ℝ)
    (hc : ∀ t ∈ Icc (0 : ℝ) 1, normalizedDerivative w f t = c)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (plane f (x : ℂ)).re = c*(1-(1+x)^(-w)) := by
  have hu0 : (plane (f-(c : ℂ) • MayerCancellation.response (w : ℂ)) (0 : ℂ)).re = 0 := by
    rw [plane_zero]
    change (f.1 zeroPoint-(c : ℂ)*(MayerCancellation.response (w : ℂ)).1 zeroPoint).re = 0
    rw [hf0,response_zero,mul_zero,sub_zero,Complex.zero_re]
  have hd : ∀ t ∈ Icc (0 : ℝ) 1,
      (deriv (plane (f-(c : ℂ) • MayerCancellation.response (w : ℂ))) (t : ℂ)).re = 0 := by
    intro t ht
    have h := (div_eq_iff (ground_pos hw ht).ne').mp (hc t ht)
    change (derivativeEvaluation (t : ℂ) (interval_mem_smallDisc ht)
      (f-(c : ℂ) • MayerCancellation.response (w : ℂ))).re = 0
    rw [map_sub,map_smul]
    change (deriv (plane f) (t : ℂ)-
      (c : ℂ)*deriv (plane (MayerCancellation.response (w : ℂ))) (t : ℂ)).re = 0
    rw [deriv_response_real w ht]
    simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    exact sub_eq_zero.mpr h
  have hv := real_plane_zero_of_real_deriv_zero _ hu0 hd hx
  have hxout := closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 3/2)
    (interval_mem_smallDisc hx)
  have hsplit : plane (f-(c : ℂ) • MayerCancellation.response (w : ℂ)) (x : ℂ) =
      plane f (x : ℂ)-(c : ℂ)*plane (MayerCancellation.response (w : ℂ)) (x : ℂ) := by
    rw [plane_eq _ ⟨x,hxout⟩,plane_eq f ⟨x,hxout⟩,
      plane_eq (MayerCancellation.response (w : ℂ)) ⟨x,hxout⟩]
    rfl
  rw [hsplit,response_real w hx] at hv
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hv
  exact sub_eq_zero.mp hv

/-- Every negative-unit derivative eigenfunction is a scalar multiple of the exact successor response. -/
theorem negative_derivative_eigen_response {w : ℝ} (hw : 0 < w) (f : DiscSpace)
    (he : ∀ x ∈ Icc (0 : ℝ) 1,
      deriv (plane (remainder (w : ℂ) f)) (x : ℂ) = -deriv (plane f) (x : ℂ)) :
    ∃ c : ℂ, f = c • MayerCancellation.response (w : ℂ) := by
  have hf0 := evaluation_zero_of_negative_derivative_eigen hw f he
  have hI0 : (I • f).1 zeroPoint = 0 := by
    change I*f.1 zeroPoint = 0
    rw [hf0,mul_zero]
  have hIe : ∀ x ∈ Icc (0 : ℝ) 1,
      deriv (plane (remainder (w : ℂ) (I • f))) (x : ℂ) =
        -deriv (plane (I • f)) (x : ℂ) := by
    intro x hx
    change derivativeEvaluation (x : ℂ) (interval_mem_smallDisc hx)
      (remainder (w : ℂ) (I • f)) =
        -derivativeEvaluation (x : ℂ) (interval_mem_smallDisc hx) (I • f)
    rw [map_smul,map_smul,map_smul]
    change I*deriv (plane (remainder (w : ℂ) f)) (x : ℂ) =
      -(I*deriv (plane f) (x : ℂ))
    rw [he x hx,mul_neg]
  obtain ⟨c,hc⟩ := normalizedDerivative_constant_of_negative_eigen hw f hf0 he
  obtain ⟨d,hd⟩ := normalizedDerivative_constant_of_negative_eigen hw (I • f) hI0 hIe
  refine ⟨(c : ℂ)-I*(d : ℂ),sub_eq_zero.mp ?_⟩
  apply eq_zero_of_real_interval
  intro x hx
  have hr := real_plane_response_of_constant_jet hw f hf0 c hc hx
  have hi := real_plane_response_of_constant_jet hw (I • f) hI0 d hd hx
  have hxout := closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 3/2)
    (interval_mem_smallDisc hx)
  have hsI : plane (I • f) (x : ℂ) = I*plane f (x : ℂ) := by
    rw [plane_eq _ ⟨x,hxout⟩,plane_eq f ⟨x,hxout⟩]
    rfl
  rw [hsI,Complex.mul_re,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_sub] at hi
  have hsplit : plane (f-((c : ℂ)-I*(d : ℂ)) • MayerCancellation.response (w : ℂ)) (x : ℂ) =
      plane f (x : ℂ)-((c : ℂ)-I*(d : ℂ))*plane (MayerCancellation.response (w : ℂ)) (x : ℂ) := by
    rw [plane_eq _ ⟨x,hxout⟩,plane_eq f ⟨x,hxout⟩,
      plane_eq (MayerCancellation.response (w : ℂ)) ⟨x,hxout⟩]
    rfl
  rw [hsplit,response_real w hx]
  apply Complex.ext
  · simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,Complex.zero_re]
    linarith only [hr]
  · simp only [Complex.sub_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,one_mul,zero_add,Complex.zero_im]
    linarith only [hi]

/-- The actual remainder has no negative-unit eigenfunction at a positive real source parameter. -/
theorem remainder_negative_eigen_eq_zero {w : ℝ} (hw : 0 < w) (f : DiscSpace)
    (he : remainder (w : ℂ) f = -f) : f = 0 := by
  have hd : ∀ x ∈ Icc (0 : ℝ) 1,
      deriv (plane (remainder (w : ℂ) f)) (x : ℂ) = -deriv (plane f) (x : ℂ) := by
    intro x hx
    have h := congrArg (derivativeEvaluation (x : ℂ) (interval_mem_smallDisc hx)) he
    rw [map_neg] at h
    exact h
  obtain ⟨c,hc⟩ := negative_derivative_eigen_response hw f hd
  have hc0 : c = 0 := by
    have h := congrArg (fun g : DiscSpace => g.1 zeroPoint) he
    rw [hc,map_smul,MayerCancellation.remainder_response hw] at h
    change c*(1-(MayerCancellation.response (w : ℂ)).1 zeroPoint) =
      -(c*(MayerCancellation.response (w : ℂ)).1 zeroPoint) at h
    simpa only [response_zero,sub_zero,mul_one,mul_zero,neg_zero] using h
  rw [hc,hc0,zero_smul]

#print axioms negative_derivative_eigen_response
#print axioms remainder_negative_eigen_eq_zero

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerNegativePole
