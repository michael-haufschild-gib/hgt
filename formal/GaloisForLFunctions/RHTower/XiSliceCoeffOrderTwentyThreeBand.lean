import GaloisForLFunctions.RHTower.XiHorizontalSliceConeCriterion
import GaloisForLFunctions.RHTower.XiHorizontalSlicePolyaFrequencyCone
import GaloisForLFunctions.RHTower.XiReciprocalCentreUnconditionalRung
import GaloisForLFunctions.RHTower.PrimeArchLogHeightDefectOrderTwentyThreeEndpointOptimization

/-!
# All-order slice positivity on the order-23 height band

The optimized order-23 source budget puts every off-line zero of `ξ` at squared ordinate at least
`431349/2000`, so at ordinate modulus at least `367/25 = 14.68`
(`orderTwentyThreeOptimizedHeightSq_le_im_sq_of_xiZeroCopy_offLine`).  An off-line zero also has
`|Re ρ − ½| < ½`.  At any height `|t| ≤ 709/50 = 14.18` every zero therefore lies in the visibility
cone `|Re ρ − ½| ≤ |Im ρ − t|`, and the cone criterion gives:

**Theorem** (`xiSliceCoeff_nonneg_of_abs_le_orderTwentyThree`).  For `|t| ≤ 709/50`, every
Taylor coefficient of `ξ(½+x+it)ξ(½−x+it)` at `0`, i.e. every higher Laguerre expression of `Ξ`
at `t`, is nonnegative.

This is the source-side input to the slice receivers: on this band the low-order signs hold at every
height with no hypothesis.  It extends the band `|t| ≤ 233/20` of `xiSliceCoeff_nonneg_of_abs_le`.

**Centre** (`xi_centre_pfSeq_fortyFive`).  At the centre the same threshold puts every zero in the
order-`45` visibility cone, since `(431349/2000)(1 − cos(π/46)) ≥ ½`.  So the Taylor coefficients of
`ξ(½ + x)` form a `PF_45` sequence, unconditionally (previously `PF_37`).  Since `PF_∞` at the centre
is equivalent to RH, this advances the unconditional order of the single-height criterion.
Through the Hessenberg–Wronski identity the first `46` coefficients of `1/Ξ(σ)` in `σ²` are
nonnegative (`evenRecipCoeff_XiC_nonneg_of_le_fortyFive`, previously `38`).

**Turán band** (`xiSliceCoeff_pfSeq_two_of_abs_le_orderTwentyThree`).  For `|t| ≤ 342/25 = 13.68`
every off-line zero is at ordinate distance `≥ 1` from `t`, inside the `√3`-cone, so the slice
coefficients `c_{2n}(t)` form a `PF_2` sequence.  In particular the Turán inequalities
`c_{2n}(t)² ≥ c_{2n−2}(t) c_{2n+2}(t)` hold at every such height.
-/

open scoped ComplexOrder
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- **All-order slice positivity on `|t| ≤ 709/50`.** -/
theorem xiSliceCoeff_nonneg_of_abs_le_orderTwentyThree {t : ℝ} (ht : |t| ≤ 709 / 50) (n : ℕ) :
    0 ≤ xiSliceCoeff t n := by
  refine xiSliceCoeff_nonneg_of_cone (fun q => ?_) n
  by_cases hoff : (q.1 : ℂ).re = 1 / 2
  · rw [hoff, sub_self, abs_zero]
    exact abs_nonneg _
  · have hh := orderTwentyThreeOptimizedHeightSq_le_im_sq_of_xiZeroCopy_offLine q hoff
    unfold xiOrderTwentyThreeOptimizedHeightSq at hh
    have hstrip := xiZeroCopy_re_mem_open_unit q
    have h1 : |(q.1 : ℂ).re - 1 / 2| < 1 / 2 := by
      rw [abs_lt]
      constructor <;> linarith [hstrip.1, hstrip.2]
    have h2 : (367 / 25 : ℝ) ≤ |(q.1 : ℂ).im| := by
      by_contra h
      push Not at h
      have habs := abs_nonneg ((q.1 : ℂ).im)
      have hsq : (q.1 : ℂ).im ^ 2 = |(q.1 : ℂ).im| ^ 2 := (sq_abs _).symm
      nlinarith
    have h3 := abs_sub_abs_le_abs_sub ((q.1 : ℂ).im) t
    linarith

/-- `1 − cos (π/46) ≥ 232/10⁵`, from `cos x ≤ 1 − x²/2 + 5x⁴/96` and `3.14 < π < 3.15`. -/
theorem one_sub_cos_pi_div_fortySix_ge : (232 / 100000 : ℝ) ≤ 1 - Real.cos (Real.pi / 46) := by
  have hπlo := Real.pi_gt_d2
  have hπhi := Real.pi_lt_d2
  set θ := Real.pi / 46 with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθlo : 3.14 / 46 < θ := by
    rw [hθ]
    exact div_lt_div_of_pos_right hπlo (by norm_num)
  have hθhi : θ < 3.15 / 46 := by
    rw [hθ]
    exact div_lt_div_of_pos_right hπhi (by norm_num)
  have hθ1 : |θ| ≤ 1 := by
    rw [abs_of_nonneg hθ0]
    linarith
  have hb := Real.cos_bound hθ1
  rw [abs_of_nonneg hθ0] at hb
  have hb2 := (abs_le.mp hb).2
  have h2 : (3.14 / 46 : ℝ) ^ 2 < θ ^ 2 := pow_lt_pow_left₀ hθlo (by norm_num) (by norm_num)
  have h4 : θ ^ 4 < (3.15 / 46 : ℝ) ^ 4 := pow_lt_pow_left₀ hθhi hθ0 (by norm_num)
  norm_num at h2 h4
  linarith

/-- Every zero copy lies in the order-`45` visibility cone at the centre: critical zeros trivially,
off-line zeros because `Im² ≥ 431349/2000` and `(Re − ½)² < ¼`. -/
theorem pf45Cone_centre (q : XiZeroCopy) :
    Real.cos (Real.pi / (((45 : ℕ) : ℝ) + 1)) *
      (((q.1 : ℂ).im) ^ 2 + ((q.1 : ℂ).re - 1 / 2) ^ 2) ≤
        ((q.1 : ℂ).im) ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 := by
  rw [show (((45 : ℕ) : ℝ) + 1) = 46 by norm_num]
  have hcos1 := Real.cos_le_one (Real.pi / 46)
  have hL := one_sub_cos_pi_div_fortySix_ge
  by_cases hoff : (q.1 : ℂ).re = 1 / 2
  · rw [hoff, sub_self]
    have := sq_nonneg ((q.1 : ℂ).im)
    nlinarith
  · have hh := orderTwentyThreeOptimizedHeightSq_le_im_sq_of_xiZeroCopy_offLine q hoff
    unfold xiOrderTwentyThreeOptimizedHeightSq at hh
    have hstrip := xiZeroCopy_re_mem_open_unit q
    have hc2 : ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 := by
      nlinarith [hstrip.1, hstrip.2]
    have h1 : (431349 / 2000 : ℝ) * (232 / 100000) ≤
        (q.1 : ℂ).im ^ 2 * (1 - Real.cos (Real.pi / 46)) :=
      mul_le_mul hh hL (by norm_num) (by positivity)
    have h2 : ((q.1 : ℂ).re - 1 / 2) ^ 2 * (1 + Real.cos (Real.pi / 46)) ≤
        ((q.1 : ℂ).re - 1 / 2) ^ 2 * 2 :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
    nlinarith

/-- **The Taylor coefficients of `ξ` at the centre form a `PF_45` sequence, unconditionally.** -/
theorem xi_centre_pfSeq_fortyFive : PFSeq 45 (evenTaylorRe (fun x => xi (1 / 2 + x))) :=
  xi_centre_pfSeq_of_cone (by norm_num) pf45Cone_centre

/-- **Unconditionally, the first 46 reciprocal centre coefficients are nonnegative.** -/
theorem evenRecipCoeff_XiC_nonneg_of_le_fortyFive {m : ℕ} (hm : m ≤ 45) :
    0 ≤ evenRecipCoeff XiC m :=
  evenRecipCoeff_XiC_nonneg_of_pfSeq xi_centre_pfSeq_fortyFive hm

/-- **`PF_2` of the slice on `|t| ≤ 342/25`.** -/
theorem xiSliceCoeff_pfSeq_two_of_abs_le_orderTwentyThree {t : ℝ} (ht : |t| ≤ 342 / 25) :
    PFSeq 2 (fun n => (xiSliceCoeff t (2 * n)).re) := by
  refine xiSliceCoeff_pfSeq_of_cone (by norm_num) fun q => ?_
  rw [show ((2 : ℕ) : ℝ) + 1 = 3 by norm_num, Real.cos_pi_div_three]
  by_cases hoff : (q.1 : ℂ).re = 1 / 2
  · rw [hoff, sub_self]
    nlinarith [sq_nonneg ((q.1 : ℂ).im - t)]
  · have hh := orderTwentyThreeOptimizedHeightSq_le_im_sq_of_xiZeroCopy_offLine q hoff
    unfold xiOrderTwentyThreeOptimizedHeightSq at hh
    have hstrip := xiZeroCopy_re_mem_open_unit q
    have hc2 : ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 := by
      nlinarith [hstrip.1, hstrip.2]
    have h2 : (367 / 25 : ℝ) ≤ |(q.1 : ℂ).im| := by
      by_contra h
      push Not at h
      have habs := abs_nonneg ((q.1 : ℂ).im)
      have hsq : (q.1 : ℂ).im ^ 2 = |(q.1 : ℂ).im| ^ 2 := (sq_abs _).symm
      nlinarith
    have h3 := abs_sub_abs_le_abs_sub ((q.1 : ℂ).im) t
    have h4 : 1 ≤ |(q.1 : ℂ).im - t| := by linarith
    have h5 : 1 ≤ ((q.1 : ℂ).im - t) ^ 2 := by
      rw [← sq_abs]; nlinarith
    nlinarith

#print axioms xi_centre_pfSeq_fortyFive

end

end RHTower
