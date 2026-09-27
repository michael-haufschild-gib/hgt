import GaloisForLFunctions.RHTower.XiGaussianCertifiedPhaseGap
import GaloisForLFunctions.RHTower.PrimeArchValuationSectorCones

/-!
# Exact critical-reserve subtraction from the fourth reciprocal trace

Only critical-line copies are charged to the finite reserve. The off-critical
fourth trace and every off-critical quartet are bounded by the complete source
minus this reserve. No zero placement or vanishing residual is assumed.
-/

open scoped Real BigOperators
open Complex
noncomputable section

namespace RHTower

def xiFourthTraceCriticalAtom (q : XiZeroCopy) : ℝ :=
  if (xiSpectralPoint q).im = 0 then (xiZeroCopyReciprocalSquare q ^ 2).re else 0

def xiFourthTraceOffAtom (q : XiZeroCopy) : ℝ :=
  if (xiSpectralPoint q).im = 0 then 0 else (xiZeroCopyReciprocalSquare q ^ 2).re

def xiCriticalFourthTraceReserve (F : Finset XiZeroCopy) : ℝ :=
  ∑ q ∈ F, xiFourthTraceCriticalAtom q

def xiCriticalFourthTraceResidual (F : Finset XiZeroCopy) : ℝ :=
  normalizedPrimeArchMoment 1 - xiCriticalFourthTraceReserve F

theorem xiFourthTraceCriticalAtom_nonneg (q : XiZeroCopy) :
    0 ≤ xiFourthTraceCriticalAtom q := by
  unfold xiFourthTraceCriticalAtom
  split_ifs
  · exact xiFourthReciprocalTraceAtom_nonneg q
  · exact le_rfl

theorem xiFourthTraceOffAtom_nonneg (q : XiZeroCopy) :
    0 ≤ xiFourthTraceOffAtom q := by
  unfold xiFourthTraceOffAtom
  split_ifs
  · exact le_rfl
  · exact xiFourthReciprocalTraceAtom_nonneg q

theorem xiFourthTraceCriticalAtom_add_off (q : XiZeroCopy) :
    xiFourthTraceCriticalAtom q + xiFourthTraceOffAtom q =
      (xiZeroCopyReciprocalSquare q ^ 2).re := by
  unfold xiFourthTraceCriticalAtom xiFourthTraceOffAtom
  split_ifs <;> simp only [add_zero, zero_add]

theorem summable_xiFourthTraceCriticalAtom : Summable xiFourthTraceCriticalAtom := by
  apply Summable.of_nonneg_of_le xiFourthTraceCriticalAtom_nonneg
    (fun q => ?_) ((summable_xiZeroCopyReciprocalSquare_pow 1).mapL Complex.reCLM)
  change xiFourthTraceCriticalAtom q ≤ (xiZeroCopyReciprocalSquare q ^ 2).re
  have h := xiFourthTraceCriticalAtom_add_off q
  linarith only [h, xiFourthTraceOffAtom_nonneg q]

theorem summable_xiFourthTraceOffAtom : Summable xiFourthTraceOffAtom := by
  apply Summable.of_nonneg_of_le xiFourthTraceOffAtom_nonneg
    (fun q => ?_) ((summable_xiZeroCopyReciprocalSquare_pow 1).mapL Complex.reCLM)
  change xiFourthTraceOffAtom q ≤ (xiZeroCopyReciprocalSquare q ^ 2).re
  have h := xiFourthTraceCriticalAtom_add_off q
  linarith only [h, xiFourthTraceCriticalAtom_nonneg q]

/-- The exact complete source splits into its critical and off-critical positive charges. -/
theorem tsum_xiFourthTraceCritical_add_off_eq_source :
    (∑' q : XiZeroCopy, xiFourthTraceCriticalAtom q) +
      (∑' q : XiZeroCopy, xiFourthTraceOffAtom q) = normalizedPrimeArchMoment 1 := by
  rw [← summable_xiFourthTraceCriticalAtom.tsum_add summable_xiFourthTraceOffAtom]
  simp only [xiFourthTraceCriticalAtom_add_off, tsum_xiFourthReciprocalTraceAtom_eq_source]

/-- Every finite critical reserve can be removed before bounding the entire off-critical mass. -/
theorem tsum_xiFourthTraceOffAtom_le_residual (F : Finset XiZeroCopy) :
    (∑' q : XiZeroCopy, xiFourthTraceOffAtom q) ≤ xiCriticalFourthTraceResidual F := by
  have h := summable_xiFourthTraceCriticalAtom.sum_le_tsum F
    (fun q _ => xiFourthTraceCriticalAtom_nonneg q)
  have he := tsum_xiFourthTraceCritical_add_off_eq_source
  unfold xiCriticalFourthTraceResidual xiCriticalFourthTraceReserve
  linarith only [h, he]

theorem xiCriticalFourthTraceResidual_nonneg (F : Finset XiZeroCopy) :
    0 ≤ xiCriticalFourthTraceResidual F :=
  (tsum_nonneg xiFourthTraceOffAtom_nonneg).trans (tsum_xiFourthTraceOffAtom_le_residual F)

/-- An explicit strict source ceiling retains the full subtracted critical contribution. -/
theorem xiCriticalFourthTraceResidual_lt_source_cap (F : Finset XiZeroCopy) :
    xiCriticalFourthTraceResidual F <
      17 / 200000 - xiCriticalFourthTraceReserve F := by
  exact sub_lt_sub_right normalizedPrimeArchMoment_one_lt_seventeen_over_twoHundredThousand _

/-- Adding available critical copies can only lower the remaining source budget. -/
theorem xiCriticalFourthTraceResidual_antitone : Antitone xiCriticalFourthTraceResidual := by
  intro F E hFE
  unfold xiCriticalFourthTraceResidual xiCriticalFourthTraceReserve
  exact sub_le_sub_left
    (Finset.sum_le_sum_of_subset_of_nonneg hFE (fun q _ _ => xiFourthTraceCriticalAtom_nonneg q)) _

theorem xiFourthTraceOffAtom_lineConj (q : XiZeroCopy) :
    xiFourthTraceOffAtom (xiZeroCopyLineConjEquiv q) = xiFourthTraceOffAtom q := by
  simp only [xiFourthTraceOffAtom, xiSpectralPoint_lineConj, Complex.conj_im,
    neg_eq_zero, xiFourthReciprocalTraceAtom_lineConj]

theorem xiFourthTraceOffAtom_conj (q : XiZeroCopy) :
    xiFourthTraceOffAtom (xiZeroCopyConjEquiv q) = xiFourthTraceOffAtom q := by
  simp only [xiFourthTraceOffAtom, xiSpectralPoint_copyConj, Complex.neg_im,
    Complex.conj_im, neg_neg, xiFourthReciprocalTraceAtom_conj]

/-- All four copies of every possible off-critical zero spend only the residual budget. -/
theorem four_mul_xiFourthTraceAtom_le_residual (F : Finset XiZeroCopy)
    (q : {q : XiZeroCopy // (xiSpectralPoint q).im ≠ 0}) :
    4 * (xiZeroCopyReciprocalSquare q.1 ^ 2).re ≤ xiCriticalFourthTraceResidual F := by
  have hoff : (q.1.1 : ℂ).re ≠ 1 / 2 := by
    intro h
    apply q.property
    rw [xiSpectralPoint_im_eq, h, sub_self]
  have h := four_mul_le_tsum_of_quartet_invariant xiFourthTraceOffAtom_nonneg
    summable_xiFourthTraceOffAtom xiFourthTraceOffAtom_lineConj xiFourthTraceOffAtom_conj q.1 hoff
  simp only [xiFourthTraceOffAtom, if_neg q.property] at h
  exact h.trans (tsum_xiFourthTraceOffAtom_le_residual F)

/-- The pointwise sector estimate controls reciprocal fourth absolute weight. -/
theorem xiFourthTraceAtom_ge_reciprocal_norm_four (q : XiZeroCopy) :
    (41 / 42 : ℝ) * (1 / ‖xiSpectralPoint q‖ ^ 4) ≤
      (xiZeroCopyReciprocalSquare q ^ 2).re := by
  have h := sectorFactor_mul_norm_xiZeroCopyReciprocalSquare_pow_le_re q 2
  have hn : ‖xiZeroCopyReciprocalSquare q‖ ^ 2 = 1 / ‖xiSpectralPoint q‖ ^ 4 := by
    rw [xiZeroCopyReciprocalSquare, norm_pow, norm_inv, ← pow_mul]
    simp only [inv_pow, one_div]
  rw [hn] at h
  have hc : (1 - (2 : ℝ) ^ 2 / 168) = 41 / 42 := by ring
  simpa only [Nat.cast_ofNat, hc] using h

end RHTower
