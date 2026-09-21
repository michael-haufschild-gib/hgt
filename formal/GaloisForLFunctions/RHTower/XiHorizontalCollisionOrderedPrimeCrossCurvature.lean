import GaloisForLFunctions.RHTower.SourceHorizontalGammaSixPairedDefectGaussHodgeCurvature

/-!
# Ordered-prime cross curvature for horizontal collision

The canonical Gamma-six source pairs reflected defects at one clock and is exchange-symmetric.
This module retains the order of the actual prime clocks `2` and `3` before scalarization.  The
difference of its two cross-curvatures is a signed source observable with no zero-dependent label
or inserted sign.  A coefficient-faithful singular landing in the Gauss--Hodge collision carrier
remains the hard HC problem.
-/

open Real Set

namespace RHTower

noncomputable section

/-- Difference of `(2,3)` and `(3,2)` cross-curvatures of literal Gamma-six boundary defects. -/
def sourceHorizontalGammaSixTwoThreeCrossOrientation (a : ℝ) : ℝ :=
  (-sourceHorizontalGammaSixUnitForwardBoundaryDefect (Real.log 2 * a) *
      sourceHorizontalGammaSixUnitReflectedBoundaryDefect (Real.log 3 * a)) -
    (-sourceHorizontalGammaSixUnitForwardBoundaryDefect (Real.log 3 * a) *
      sourceHorizontalGammaSixUnitReflectedBoundaryDefect (Real.log 2 * a))

/-- Exact factorization of the ordered-prime orientation. -/
theorem sourceHorizontalGammaSixTwoThreeCrossOrientation_eq (a : ℝ) :
    sourceHorizontalGammaSixTwoThreeCrossOrientation a =
      (Real.exp (Real.log 2 * a) - Real.exp (Real.log 3 * a)) *
        (Real.exp (Real.log 2 * a) - 1) *
        (Real.exp (Real.log 3 * a) - 1) /
          (Real.exp (Real.log 2 * a) * Real.exp (Real.log 3 * a)) := by
  rw [sourceHorizontalGammaSixTwoThreeCrossOrientation,
    sourceHorizontalGammaSixUnitForwardBoundaryDefect_eq,
    sourceHorizontalGammaSixUnitReflectedBoundaryDefect_eq,
    sourceHorizontalGammaSixUnitForwardBoundaryDefect_eq,
    sourceHorizontalGammaSixUnitReflectedBoundaryDefect_eq,
    Real.exp_neg, Real.exp_neg]
  field_simp [Real.exp_ne_zero]
  ring

/-- Reversing the centered horizontal direction reverses the ordered-prime orientation. -/
theorem sourceHorizontalGammaSixTwoThreeCrossOrientation_neg (a : ℝ) :
    sourceHorizontalGammaSixTwoThreeCrossOrientation (-a) =
      -sourceHorizontalGammaSixTwoThreeCrossOrientation a := by
  rw [sourceHorizontalGammaSixTwoThreeCrossOrientation_eq,
    sourceHorizontalGammaSixTwoThreeCrossOrientation_eq]
  simp only [mul_neg, Real.exp_neg]
  field_simp [Real.exp_ne_zero]
  ring

private theorem log_two_lt_log_three : Real.log 2 < Real.log 3 := by
  apply Real.strictMonoOn_log
  · exact mem_Ioi.mpr (by norm_num)
  · exact mem_Ioi.mpr (by norm_num)
  · norm_num

/-- Positive centered rate makes the ordered `(2,3)` source orientation strictly negative. -/
theorem sourceHorizontalGammaSixTwoThreeCrossOrientation_neg_of_pos
    {a : ℝ} (ha : 0 < a) :
    sourceHorizontalGammaSixTwoThreeCrossOrientation a < 0 := by
  rw [sourceHorizontalGammaSixTwoThreeCrossOrientation_eq]
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hthree : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hP_lt_Q : Real.exp (Real.log 2 * a) < Real.exp (Real.log 3 * a) := by
    rw [Real.exp_lt_exp]
    exact mul_lt_mul_of_pos_right log_two_lt_log_three ha
  have hP_gt_one : 1 < Real.exp (Real.log 2 * a) := by
    rw [← Real.exp_zero, Real.exp_lt_exp]
    exact mul_pos htwo ha
  have hQ_gt_one : 1 < Real.exp (Real.log 3 * a) := by
    rw [← Real.exp_zero, Real.exp_lt_exp]
    exact mul_pos hthree ha
  have hnum :
      (Real.exp (Real.log 2 * a) - Real.exp (Real.log 3 * a)) *
          (Real.exp (Real.log 2 * a) - 1) *
          (Real.exp (Real.log 3 * a) - 1) < 0 := by
    exact mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (sub_neg.mpr hP_lt_Q) (sub_pos.mpr hP_gt_one))
      (sub_pos.mpr hQ_gt_one)
  exact div_neg_of_neg_of_pos hnum
    (mul_pos (Real.exp_pos _) (Real.exp_pos _))

/-- Negative centered rate makes the ordered `(2,3)` source orientation strictly positive. -/
theorem sourceHorizontalGammaSixTwoThreeCrossOrientation_pos_of_neg
    {a : ℝ} (ha : a < 0) :
    0 < sourceHorizontalGammaSixTwoThreeCrossOrientation a := by
  rw [sourceHorizontalGammaSixTwoThreeCrossOrientation_eq]
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hthree : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hQ_lt_P : Real.exp (Real.log 3 * a) < Real.exp (Real.log 2 * a) := by
    rw [Real.exp_lt_exp]
    exact mul_lt_mul_of_neg_right log_two_lt_log_three ha
  have hP_lt_one : Real.exp (Real.log 2 * a) < 1 := by
    rw [← Real.exp_zero, Real.exp_lt_exp]
    exact mul_neg_of_pos_of_neg htwo ha
  have hQ_lt_one : Real.exp (Real.log 3 * a) < 1 := by
    rw [← Real.exp_zero, Real.exp_lt_exp]
    exact mul_neg_of_pos_of_neg hthree ha
  have hnum : 0 <
      (Real.exp (Real.log 2 * a) - Real.exp (Real.log 3 * a)) *
          (Real.exp (Real.log 2 * a) - 1) *
          (Real.exp (Real.log 3 * a) - 1) := by
    exact mul_pos_of_neg_of_neg
      (mul_neg_of_pos_of_neg (sub_pos.mpr hQ_lt_P) (sub_neg.mpr hP_lt_one))
      (sub_neg.mpr hQ_lt_one)
  exact div_pos hnum (mul_pos (Real.exp_pos _) (Real.exp_pos _))

/-- Ordered-prime cross curvature vanishes exactly at neutral horizontal rate. -/
theorem sourceHorizontalGammaSixTwoThreeCrossOrientation_eq_zero_iff (a : ℝ) :
    sourceHorizontalGammaSixTwoThreeCrossOrientation a = 0 ↔ a = 0 := by
  constructor
  · intro h
    rcases lt_trichotomy a 0 with ha | ha | ha
    · have hpos := sourceHorizontalGammaSixTwoThreeCrossOrientation_pos_of_neg ha
      linarith
    · exact ha
    · have hneg := sourceHorizontalGammaSixTwoThreeCrossOrientation_neg_of_pos ha
      linarith
  · rintro rfl
    norm_num [sourceHorizontalGammaSixTwoThreeCrossOrientation,
      sourceHorizontalGammaSixUnitForwardBoundaryDefect_eq,
      sourceHorizontalGammaSixUnitReflectedBoundaryDefect_eq]

/-- At every retained Xi copy, ordered source orientation vanishes exactly on critical line. -/
theorem sourceHorizontalGammaSixTwoThreeCrossOrientation_centeredRate_eq_zero_iff
    (q : XiZeroCopy) :
    sourceHorizontalGammaSixTwoThreeCrossOrientation
        (primeDepthBVWoldXiCenteredRate q.1) = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [sourceHorizontalGammaSixTwoThreeCrossOrientation_eq_zero_iff,
    primeDepthBVWoldXiCenteredRate]
  constructor <;> intro h <;> linarith

/-- Critical-line conjugation reverses the ordered-prime source orientation at every Xi copy. -/
theorem sourceHorizontalGammaSixTwoThreeCrossOrientation_centeredRate_lineConj
    (q : XiZeroCopy) :
    sourceHorizontalGammaSixTwoThreeCrossOrientation
        (primeDepthBVWoldXiCenteredRate (xiZeroCopyLineConjEquiv q).1) =
      -sourceHorizontalGammaSixTwoThreeCrossOrientation
        (primeDepthBVWoldXiCenteredRate q.1) := by
  rw [show primeDepthBVWoldXiCenteredRate (xiZeroCopyLineConjEquiv q).1 =
      -primeDepthBVWoldXiCenteredRate q.1 by
    change primeDepthBVWoldXiCenteredRate (xiZeroLineConjEquiv q.1) =
      -primeDepthBVWoldXiCenteredRate q.1
    exact primeDepthBVWoldXiCenteredRate_reflection q.1]
  exact sourceHorizontalGammaSixTwoThreeCrossOrientation_neg _

/-- **Scalarization no-go.** Every finite Xi-copy carrier stable under critical-line
conjugation has zero total ordered-prime orientation.  Hence this source-defined sign survives
only before reflection-stable scalar aggregation. -/
theorem sum_sourceHorizontalGammaSixTwoThreeCrossOrientation_eq_zero_of_lineConj_stable
    (S : Finset XiZeroCopy)
    (hS : ∀ q ∈ S, xiZeroCopyLineConjEquiv q ∈ S) :
    ∑ q ∈ S, sourceHorizontalGammaSixTwoThreeCrossOrientation
      (primeDepthBVWoldXiCenteredRate q.1) = 0 := by
  classical
  refine Finset.sum_involution (s := S)
    (fun q _ => xiZeroCopyLineConjEquiv q) ?_ ?_ ?_ ?_
  · intro q _
    rw [sourceHorizontalGammaSixTwoThreeCrossOrientation_centeredRate_lineConj]
    ring
  · intro q _ hq hfix
    have h := sourceHorizontalGammaSixTwoThreeCrossOrientation_centeredRate_lineConj q
    rw [hfix] at h
    apply hq
    linarith
  · exact hS
  · intro q _
    exact DeningerMeyerGaussianGreen.xiZeroCopyLineConjEquiv_apply_apply q

end

end RHTower
