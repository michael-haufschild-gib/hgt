import GaloisForLFunctions.RHTower.XiReciprocalSquareSecondMomentRadius
import GaloisForLFunctions.RHTower.SuzukiCoalescingXiSourceRate

/-!
# Complete shifted source tower for the actual LI clock limit

The extra endpoint factor retains one more shifted denominator than an ordinary
reciprocal moment. Its exact source is the difference of two consecutive
shifted moments. Every degree admits the same sharp reciprocal-radius bound,
and existing complete-source continuity supplies its central boundary value.
-/

open Complex Filter Topology
namespace RHTower
noncomputable section

/-- Multiplicity-copy source atom retaining the endpoint's second denominator. -/
def liEvenCrossActualClockSourceAtom (v : ℝ) (j : ℕ) (q : XiZeroCopy) : ℂ :=
  xiZeroCopyReciprocalSquare q ^ (j + 1) /
    (1 + (v : ℂ) * xiZeroCopyReciprocalSquare q) ^ (j + 2)

/-- Literal weighted source moment for each coefficient of the normalized current. -/
def liEvenCrossActualClockSourceMoment (v : ℝ) (j : ℕ) : ℝ :=
  (xiShiftedReciprocalMoment v j -
    (v : ℂ) * xiShiftedReciprocalMoment v (j + 1)).re

theorem norm_liEvenCrossActualClockSourceAtom_le
    {v : ℝ} (hv : 0 ≤ v) (j : ℕ) (q : XiZeroCopy) :
    ‖liEvenCrossActualClockSourceAtom v j q‖ ≤
      ‖xiZeroCopyReciprocalSquare q‖ ^ (j + 1) := by
  unfold liEvenCrossActualClockSourceAtom
  rw [norm_div, norm_pow, norm_pow]
  apply div_le_self (pow_nonneg (norm_nonneg _) _)
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
    (one_le_norm_one_add_mul_xiZeroCopyReciprocalSquare hv q) (j + 2)
  simpa only [one_pow] using h

theorem summable_norm_liEvenCrossActualClockSourceAtom
    {v : ℝ} (hv : 0 ≤ v) (j : ℕ) :
    Summable (fun q => ‖liEvenCrossActualClockSourceAtom v j q‖) := by
  have h := (summable_xiZeroCopyReciprocalSquare_pow j).norm
  apply h.of_nonneg_of_le (fun q => norm_nonneg _)
  intro q
  simpa only [norm_pow] using norm_liEvenCrossActualClockSourceAtom_le hv j q

theorem summable_liEvenCrossActualClockSourceAtom
    {v : ℝ} (hv : 0 ≤ v) (j : ℕ) :
    Summable (liEvenCrossActualClockSourceAtom v j) :=
  (summable_norm_liEvenCrossActualClockSourceAtom hv j).of_norm

theorem liEvenCrossActualClockSourceAtom_eq_shifted_difference
    {v : ℝ} (hv : 0 ≤ v) (j : ℕ) (q : XiZeroCopy) :
    liEvenCrossActualClockSourceAtom v j q =
      xiShiftedReciprocalSquare v q ^ (j + 1) -
        (v : ℂ) * xiShiftedReciprocalSquare v q ^ (j + 2) := by
  let a : ℂ := xiZeroCopyReciprocalSquare q
  let d : ℂ := 1 + (v : ℂ) * a
  have hd : d ≠ 0 := one_add_mul_xiZeroCopyReciprocalSquare_ne_zero hv q
  change a ^ (j + 1) / d ^ (j + 2) =
    (a / d) ^ (j + 1) - (v : ℂ) * (a / d) ^ (j + 2)
  rw [div_pow, div_pow, show j + 2 = (j + 1) + 1 by omega,
    pow_succ a, pow_succ d]
  field_simp [hd]
  dsimp only [d]
  ring

theorem liEvenCrossActualClockSourceMoment_eq_re_tsum
    {v : ℝ} (hv : 0 ≤ v) (j : ℕ) :
    liEvenCrossActualClockSourceMoment v j =
      (∑' q, liEvenCrossActualClockSourceAtom v j q).re := by
  unfold liEvenCrossActualClockSourceMoment xiShiftedReciprocalMoment
  have h₀ := summable_xiShiftedReciprocalSquare_pow hv j
  have h₁ := summable_xiShiftedReciprocalSquare_pow hv (j + 1)
  have heq : (∑' q, liEvenCrossActualClockSourceAtom v j q) =
      (∑' q, xiShiftedReciprocalSquare v q ^ (j + 1)) -
        (v : ℂ) * (∑' q, xiShiftedReciprocalSquare v q ^ (j + 2)) := by
    rw [← h₁.tsum_mul_left (v : ℂ), ← h₀.tsum_sub (h₁.mul_left (v : ℂ))]
    apply tsum_congr
    intro q
    exact liEvenCrossActualClockSourceAtom_eq_shifted_difference hv j q
  rw [heq]

/-- Complete-source bound uniform in the nonnegative mass and every natural degree. -/
theorem abs_liEvenCrossActualClockSourceMoment_le
    {v : ℝ} (hv : 0 ≤ v) (j : ℕ) :
    |liEvenCrossActualClockSourceMoment v j| ≤
      (1 / 150 : ℝ) ^ j * xiShiftAbsoluteMass 0 := by
  rw [liEvenCrossActualClockSourceMoment_eq_re_tsum hv]
  calc
    |(∑' q, liEvenCrossActualClockSourceAtom v j q).re| ≤
        ‖∑' q, liEvenCrossActualClockSourceAtom v j q‖ := Complex.abs_re_le_norm _
    _ ≤ ∑' q, ‖liEvenCrossActualClockSourceAtom v j q‖ :=
      norm_tsum_le_tsum_norm (summable_norm_liEvenCrossActualClockSourceAtom hv j)
    _ ≤ ∑' q, ‖xiZeroCopyReciprocalSquare q‖ ^ (j + 1) :=
      (summable_norm_liEvenCrossActualClockSourceAtom hv j).tsum_le_tsum
        (norm_liEvenCrossActualClockSourceAtom_le hv j)
        (by simpa only [norm_pow] using
          (summable_xiZeroCopyReciprocalSquare_pow j).norm)
    _ ≤ (1 / 150 : ℝ) ^ j * xiShiftAbsoluteMass 0 := by
      simpa only [zero_add, show 1 + j = j + 1 by omega] using
        xiShiftAbsoluteTail_le_secondMomentRadius 0 j

theorem liEvenCrossActualClockSourceMoment_zero (j : ℕ) :
    liEvenCrossActualClockSourceMoment 0 j = normalizedPrimeArchMoment j := by
  simp [liEvenCrossActualClockSourceMoment,
    xiShiftedReciprocalMoment_zero_eq_normalizedPrimeArchMoment]

/-- Fixed-degree source continuity; no growing-order differentiation is invoked. -/
theorem liEvenCrossActualClockSourceMoment_tendsto_zero (j : ℕ) :
    Tendsto (fun v : ℝ => liEvenCrossActualClockSourceMoment v j)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (normalizedPrimeArchMoment j)) := by
  have h₀ := (tendsto_xiShiftedReciprocalMoment_nhdsGE_zero j).mono_left
    (nhdsWithin_mono 0 (show Set.Ioi (0 : ℝ) ⊆ Set.Ici 0 by
      intro v hv; change 0 < v at hv; exact hv.le))
  have h₁ := (tendsto_xiShiftedReciprocalMoment_nhdsGE_zero (j + 1)).mono_left
    (nhdsWithin_mono 0 (show Set.Ioi (0 : ℝ) ⊆ Set.Ici 0 by
      intro v hv; change 0 < v at hv; exact hv.le))
  have hv : Tendsto (fun v : ℝ => (v : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlim := Complex.continuous_re.continuousAt.tendsto.comp (h₀.sub (hv.mul h₁))
  simpa only [zero_mul, sub_zero, Complex.ofReal_re,
    liEvenCrossActualClockSourceMoment, Function.comp_def] using hlim

end
end RHTower
