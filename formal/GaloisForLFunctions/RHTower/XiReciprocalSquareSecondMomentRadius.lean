import GaloisForLFunctions.RHTower.XiEndpointSchwarzPairHeightGap
import GaloisForLFunctions.RHTower.PrimeArchValuationSectorCones

/-!
# Xi reciprocal-square radius from the second source moment

The sectorial second source-moment bound and Schwarz-pair occupancy give the strict pointwise
radius `‖alpha⁻²‖ < 1/150`.  This yields the centered spectral gap `‖alpha‖² > 150`, the
frequency gap `|Re alpha| > 207/20`, and a uniform geometric envelope for every later absolute
moment.  The module is kept separate from the foundational endpoint height gap so only consumers
of the stronger sector-cone estimate pay for that dependency.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- The sectorial second source moment controls the full second absolute mass. -/
theorem xiShiftAbsoluteMass_one_lt_secondMomentBudget :
    xiShiftAbsoluteMass 1 <
      (42 / 41 : ℝ) * (17 / 200000 : ℝ) := by
  have hsector :=
    sectorFactor_mul_xiShiftAbsoluteMass_le_normalizedPrimeArchMoment 1
  norm_num at hsector
  nlinarith [normalizedPrimeArchMoment_one_lt_seventeen_over_twoHundredThousand]

/-- Schwarz-pair occupancy converts the global second-moment budget into a pointwise radius. -/
theorem norm_xiZeroCopyReciprocalSquare_lt_one_div_oneHundredFifty
    (q : XiZeroCopy) :
    ‖xiZeroCopyReciprocalSquare q‖ < (1 / 150 : ℝ) := by
  have hCinv : ∀ r : XiZeroCopy,
      ‖xiZeroCopyReciprocalSquare (xiZeroCopyConjEquiv r)‖ ^ (2 : ℕ) =
        ‖xiZeroCopyReciprocalSquare r‖ ^ (2 : ℕ) := by
    intro r
    rw [xiZeroCopyReciprocalSquare, xiZeroCopyReciprocalSquare,
      xiSpectralPoint_copyConj, norm_pow, norm_pow, norm_inv, norm_inv,
      norm_neg, RCLike.norm_conj]
  have horbit := two_mul_le_tsum_of_conj_invariant
    (f := fun r : XiZeroCopy => ‖xiZeroCopyReciprocalSquare r‖ ^ (2 : ℕ))
    (fun r => sq_nonneg _) (summable_xiShiftAbsoluteMass 1) hCinv q
  have horbit' : 2 * ‖xiZeroCopyReciprocalSquare q‖ ^ (2 : ℕ) ≤
      xiShiftAbsoluteMass 1 := by
    simpa only [xiShiftAbsoluteMass, Nat.reduceAdd] using horbit
  have hmass := xiShiftAbsoluteMass_one_lt_secondMomentBudget
  have hsq : ‖xiZeroCopyReciprocalSquare q‖ ^ (2 : ℕ) < (1 / 150 : ℝ) ^ (2 : ℕ) := by
    nlinarith [horbit']
  nlinarith [norm_nonneg (xiZeroCopyReciprocalSquare q)]

/-- The reciprocal-square pointwise radius is exactly a strict centered spectral gap. -/
theorem oneHundredFifty_lt_norm_xiSpectralPoint_sq (q : XiZeroCopy) :
    (150 : ℝ) < ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
  have hrec := norm_xiZeroCopyReciprocalSquare_lt_one_div_oneHundredFifty q
  rw [xiZeroCopyReciprocalSquare, norm_pow, norm_inv, inv_pow,
    inv_eq_one_div] at hrec
  have hnorm : 0 < ‖xiSpectralPoint q‖ :=
    norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have hsq : 0 < ‖xiSpectralPoint q‖ ^ (2 : ℕ) := sq_pos_of_pos hnorm
  rw [div_lt_iff₀ hsq] at hrec
  norm_num at hrec ⊢
  nlinarith

/-- Removing the transverse critical-strip width from the radial gap leaves a strict frequency
square gap `599/4 = 150 - 1/4`. -/
theorem fiveHundredNinetyNine_fourths_lt_xiSpectralPoint_re_sq
    (q : XiZeroCopy) :
    (599 / 4 : ℝ) < (xiSpectralPoint q).re ^ (2 : ℕ) := by
  have hrad := oneHundredFifty_lt_norm_xiSpectralPoint_sq q
  have him := xiSpectralPoint_im_mem_openHalf q
  rw [Complex.sq_norm, normSq_apply] at hrad
  have himsq : (xiSpectralPoint q).im ^ (2 : ℕ) < (1 / 2 : ℝ) ^ (2 : ℕ) := by
    have hprod : 0 <
        ((1 / 2 : ℝ) - (xiSpectralPoint q).im) *
          ((1 / 2 : ℝ) + (xiSpectralPoint q).im) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  nlinarith

/-- In particular, every centered Xi frequency lies strictly beyond `207/20`.  This boundary is
larger than the current moment-tail positivity band, so a Taylor-disk argument cannot yet meet a
divisor pole. -/
theorem twoHundredSeven_twentieths_lt_abs_xiSpectralPoint_re
    (q : XiZeroCopy) :
    (207 / 20 : ℝ) < |(xiSpectralPoint q).re| := by
  have hs := fiveHundredNinetyNine_fourths_lt_xiSpectralPoint_re_sq q
  by_contra h
  have hle : |(xiSpectralPoint q).re| ≤ (207 / 20 : ℝ) := le_of_not_gt h
  have hsle : |(xiSpectralPoint q).re| ^ (2 : ℕ) ≤ (207 / 20 : ℝ) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (abs_nonneg _) hle 2
  rw [sq_abs] at hsle
  nlinarith

/-- The second-moment radius contracts every shifted absolute-moment tail. -/
theorem xiShiftAbsoluteTail_le_secondMomentRadius (s n : ℕ) :
    (∑' q : XiZeroCopy,
        ‖xiZeroCopyReciprocalSquare q‖ ^ (s + 1 + n)) ≤
      (1 / 150 : ℝ) ^ n * xiShiftAbsoluteMass s := by
  have hleft : Summable
      (fun q : XiZeroCopy =>
        ‖xiZeroCopyReciprocalSquare q‖ ^ (s + 1 + n)) := by
    have h := (summable_xiZeroCopyReciprocalSquare_pow (s + n)).norm
    simpa only [norm_pow, show s + n + 1 = s + 1 + n by omega] using h
  rw [xiShiftAbsoluteMass, ← tsum_mul_left]
  exact hleft.tsum_le_tsum (fun q => by
    rw [pow_add]
    have hpow : ‖xiZeroCopyReciprocalSquare q‖ ^ n ≤ (1 / 150 : ℝ) ^ n :=
      pow_le_pow_left₀ (norm_nonneg _)
        (norm_xiZeroCopyReciprocalSquare_lt_one_div_oneHundredFifty q).le n
    exact (mul_le_mul_of_nonneg_left hpow
      (pow_nonneg (norm_nonneg _) (s + 1))).trans_eq (mul_comm _ _))
    ((summable_xiShiftAbsoluteMass s).mul_left ((1 / 150 : ℝ) ^ n))

/-- Every centered Xi moment obeys the second-moment-radius absolute-tail envelope. -/
theorem abs_normalizedPrimeArchMoment_add_le_secondMomentRadius
    (s n : ℕ) :
    |normalizedPrimeArchMoment (s + n)| ≤
      (1 / 150 : ℝ) ^ n * xiShiftAbsoluteMass s := by
  have hpow := summable_xiZeroCopyReciprocalSquare_pow (s + n)
  rw [normalizedPrimeArchMoment_eq_re_xiCentralReciprocalMoment,
    ← tsum_xiZeroCopyReciprocalSquare_pow]
  calc
    |(∑' q : XiZeroCopy,
        xiZeroCopyReciprocalSquare q ^ (s + n + 1)).re| ≤
        ‖∑' q : XiZeroCopy,
          xiZeroCopyReciprocalSquare q ^ (s + n + 1)‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ∑' q : XiZeroCopy,
        ‖xiZeroCopyReciprocalSquare q ^ (s + n + 1)‖ :=
      norm_tsum_le_tsum_norm hpow.norm
    _ = ∑' q : XiZeroCopy,
        ‖xiZeroCopyReciprocalSquare q‖ ^ (s + 1 + n) := by
      apply tsum_congr
      intro q
      rw [norm_pow]
      congr 1
      omega
    _ ≤ (1 / 150 : ℝ) ^ n * xiShiftAbsoluteMass s :=
      xiShiftAbsoluteTail_le_secondMomentRadius s n

end

end RHTower
