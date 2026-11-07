import GaloisForLFunctions.RHTower.XiCenteredOrderTwentyTwoSourceBudgetClosure
import GaloisForLFunctions.ThetaCuspSections.ExplicitCurrentCore

/-!
# A zero gap paid by the complete fourth reciprocal trace

Conjugate zero copies are distinct and have equal nonnegative fourth-trace
mass. The complete source budget excludes any on-line zero of ordinate at
most twelve; verified height 67 excludes the remaining case.
-/

open Complex
noncomputable section
namespace GaloisForLFunctions.ThetaCuspSections
open _root_.RHTower
open GaloisForLFunctions.VerifiedHeightRungs HadamardBudget

/-- A conjugate pair spends twice its fourth reciprocal atom from the full source. -/
theorem twice_fourthReciprocalAtom_le_source (q : XiZeroCopy) :
    2 * (xiZeroCopyReciprocalSquare q ^ (2 : ℕ)).re ≤ normalizedPrimeArchMoment 1 := by
  classical
  have hs : Summable fun r : XiZeroCopy => (xiZeroCopyReciprocalSquare r ^ (2 : ℕ)).re :=
    (summable_xiZeroCopyReciprocalSquare_pow 1).mapL Complex.reCLM
  have hh := hs.sum_le_tsum {q, xiZeroCopyConjEquiv q}
    (fun r _ => xiFourthReciprocalTraceAtom_nonneg r)
  rw [Finset.sum_insert (by simpa using xiZeroCopy_ne_conj q),
    Finset.sum_singleton, xiFourthReciprocalTraceAtom_conj,
    tsum_xiFourthReciprocalTraceAtom_eq_source] at hh
  linarith only [hh]

/-- The complete source's fourth-trace budget excludes every zero below ordinate twelve. -/
theorem xiZeroCopy_twelve_lt_abs_im (q : XiZeroCopy) : 12 < |(q.1 : ℂ).im| := by
  by_contra h
  have hb : |(q.1 : ℂ).im| ≤ 12 := not_lt.mp h
  have hline : (q.1 : ℂ).re = 1 / 2 := by
    by_contra hoff
    have hfar := lt_abs_im_of_rhVerifiedThrough rhVerifiedThrough_sixtySeven
      (xi_xiZeroCopy_eq_zero q) (xiZeroCopy_re_pos q) (xiZeroCopy_re_lt_one q) hoff
    linarith only [hb, hfar]
  have hλ : xiSpectralPoint q = (((q.1 : ℂ).im : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [xiSpectralPoint, hline]
  have hatom : (xiZeroCopyReciprocalSquare q ^ (2 : ℕ)).re =
      ((q.1 : ℂ).im ^ (4 : ℕ))⁻¹ := by
    simp only [xiZeroCopyReciprocalSquare, hλ, ← Complex.ofReal_inv,
      ← Complex.ofReal_pow, Complex.ofReal_re, ← pow_mul, inv_pow]
  have hγ := xi_divisor_support_im_ne_zero q.1
  have hpow : (q.1 : ℂ).im ^ (4 : ℕ) ≤ 12 ^ (4 : ℕ) := by
    have hh := pow_le_pow_left₀ (abs_nonneg (q.1 : ℂ).im) hb 4
    have he : |(q.1 : ℂ).im| ^ (4 : ℕ) = (q.1 : ℂ).im ^ (4 : ℕ) := by
      calc
        _ = (|(q.1 : ℂ).im| ^ 2) ^ 2 := by ring
        _ = ((q.1 : ℂ).im ^ 2) ^ 2 := by rw [sq_abs]
        _ = _ := by ring
    rwa [he] at hh
  have hpos : 0 < (q.1 : ℂ).im ^ (4 : ℕ) := by positivity
  have hpaid := twice_fourthReciprocalAtom_le_source q
  rw [hatom] at hpaid
  have hlo := inv_anti₀ hpos hpow
  have hhi := normalizedPrimeArchMoment_one_lt_nine_over_oneHundredThousand
  norm_num at hlo
  linarith only [hpaid, hlo, hhi]

#print axioms twice_fourthReciprocalAtom_le_source
#print axioms xiZeroCopy_twelve_lt_abs_im

end GaloisForLFunctions.ThetaCuspSections
