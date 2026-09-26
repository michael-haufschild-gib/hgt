import GaloisForLFunctions.RHTower.AnharmonicChebyshevCubicDescentCriterion

open Complex

namespace RHTower

private theorem chebyshevQ_re_zero_iff_neg_conj (s : ℂ) :
    (chebyshevAnharmonicQ s).re = 0 ↔
      chebyshevAnharmonicQ s = -starRingEnd ℂ (chebyshevAnharmonicQ s) := by
  constructor
  · intro h
    apply Complex.ext
    · simp [h]
    · simp
  · intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith

theorem chebyshevAnharmonicQ_re_zero_iff_fiberBranches
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    (chebyshevAnharmonicQ s).re = 0 ↔
      1 - starRingEnd ℂ s = s ∨
      1 - starRingEnd ℂ s = chebyshevAnharmonicW s ∨
      1 - starRingEnd ℂ s = chebyshevAnharmonicWTwo s := by
  have hconj0 : starRingEnd ℂ s ≠ 0 := by
    intro h
    apply hs0
    simpa using congrArg (starRingEnd ℂ) h
  have hconj1 : starRingEnd ℂ s ≠ 1 := by
    intro h
    apply hs1
    simpa using congrArg (starRingEnd ℂ) h
  have hz0 : 1 - starRingEnd ℂ s ≠ 0 := by
    intro h
    apply hconj1
    exact (sub_eq_zero.mp h).symm
  have hz1 : 1 - starRingEnd ℂ s ≠ 1 := by
    intro h
    apply hconj0
    linear_combination -h
  rw [← chebyshevAnharmonicQ_fiber_iff hs0 hs1 hz0 hz1]
  change (chebyshevAnharmonicQ s).re = 0 ↔
    chebyshevAnharmonicQ (chebyshevAnharmonicSigma (starRingEnd ℂ s)) =
      chebyshevAnharmonicQ s
  rw [chebyshevAnharmonicQ_sigma hconj0 hconj1,
    chebyshevAnharmonicQ_map_conj]
  constructor
  · intro h
    exact ((chebyshevQ_re_zero_iff_neg_conj s).mp h).symm
  · intro h
    exact (chebyshevQ_re_zero_iff_neg_conj s).mpr h.symm

private theorem criticalLine_branch_iff (s : ℂ) :
    1 - starRingEnd ℂ s = s ↔ s.re = 1 / 2 := by
  constructor
  · intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith
  · intro h
    apply Complex.ext
    · simp [h]
      ring
    · simp

private theorem unitCircle_branch_iff {s : ℂ} (hs0 : s ≠ 0) :
    1 - starRingEnd ℂ s = chebyshevAnharmonicW s ↔
      starRingEnd ℂ s * s = 1 := by
  constructor
  · intro h
    have hm := congrArg (fun z : ℂ => z * s) h
    simp only [chebyshevAnharmonicW] at hm
    rw [div_mul_cancel₀ _ hs0] at hm
    linear_combination -hm
  · intro h
    apply (eq_div_iff hs0).2
    linear_combination -h

private theorem shiftedUnitCircle_branch_iff {s : ℂ} (hs1 : s ≠ 1) :
    1 - starRingEnd ℂ s = chebyshevAnharmonicWTwo s ↔
      starRingEnd ℂ (1 - s) * (1 - s) = 1 := by
  have hsub : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  constructor
  · intro h
    have hm := congrArg (fun z : ℂ => z * (1 - s)) h
    simp only [chebyshevAnharmonicWTwo, div_eq_mul_inv, one_mul] at hm
    rw [inv_mul_cancel₀ hsub] at hm
    simpa only [map_sub, map_one] using hm
  · intro h
    apply (eq_div_iff hsub).2
    simpa only [map_sub, map_one] using h

theorem chebyshevAnharmonicQ_re_zero_iff_realityLocus
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    (chebyshevAnharmonicQ s).re = 0 ↔
      s.re = 1 / 2 ∨
      starRingEnd ℂ s * s = 1 ∨
      starRingEnd ℂ (1 - s) * (1 - s) = 1 := by
  rw [chebyshevAnharmonicQ_re_zero_iff_fiberBranches hs0 hs1,
    criticalLine_branch_iff, unitCircle_branch_iff hs0,
    shiftedUnitCircle_branch_iff hs1]

private theorem conjugate_mul_self_eq_one_iff_norm_eq_one (z : ℂ) :
    starRingEnd ℂ z * z = 1 ↔ ‖z‖ = 1 := by
  have heq : starRingEnd ℂ z * z = (normSq z : ℂ) := by
    exact normSq_eq_conj_mul_self.symm
  rw [heq, normSq_eq_norm_sq]
  constructor
  · intro h
    have hr : ‖z‖ ^ 2 = 1 := by exact_mod_cast h
    nlinarith [norm_nonneg z]
  · intro h
    simp [h]

theorem chebyshevAnharmonicQ_re_zero_iff_line_or_circles
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    (chebyshevAnharmonicQ s).re = 0 ↔
      s.re = 1 / 2 ∨ ‖s‖ = 1 ∨ ‖1 - s‖ = 1 := by
  rw [chebyshevAnharmonicQ_re_zero_iff_realityLocus hs0 hs1,
    conjugate_mul_self_eq_one_iff_norm_eq_one,
    conjugate_mul_self_eq_one_iff_norm_eq_one]

theorem xiZeroCopy_chebyshevAnharmonicQ_re_zero_iff_criticalLine (q : XiZeroCopy) :
    (chebyshevAnharmonicQ (q.1 : ℂ)).re = 0 ↔ (q.1 : ℂ).re = 1 / 2 := by
  let s : ℂ := q.1
  have him : 1 < s.im ^ (2 : ℕ) := by
    simpa only [s] using xiZeroCopy_one_lt_im_sq q
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at him
    norm_num at him
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at him
    norm_num at him
  rw [chebyshevAnharmonicQ_re_zero_iff_line_or_circles hs0 hs1]
  constructor
  · intro h
    rcases h with hline | hcircle | hcircle
    · exact hline
    · have hsq : normSq s = 1 := by
        rw [normSq_eq_norm_sq, hcircle]
        norm_num
      rw [normSq_apply] at hsq
      nlinarith only [him, hsq, sq_nonneg s.re]
    · have hsq : normSq (1 - s) = 1 := by
        rw [normSq_eq_norm_sq, hcircle]
        norm_num
      rw [normSq_apply] at hsq
      simp only [sub_re, one_re, sub_im, one_im, zero_sub] at hsq
      nlinarith only [him, hsq, sq_nonneg (1 - s.re)]
  · intro h
    exact Or.inl h

end RHTower
