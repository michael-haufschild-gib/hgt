import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitShortDilationAction

/-!
# A direct test of dilation invariance

On a short initial interval both sawtooths are negative, so their
correlation is strictly positive. The centered Mellin action then has
strictly negative first variation. Its coefficient group law therefore
does not give invariance of this isolated quadratic action.
-/

noncomputable section
open MeasureTheory Set

namespace RHTower

private theorem sawtooth_small_time {t : ℝ}
    (ht : 0 ≤ t) (htop : t ≤ Real.log (4 / 3 : ℝ)) :
    logarithmicCenteredSawtooth t ≤ -(1 / 6) := by
  have hlow : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr ht
  have hhigh : Real.exp t ≤ (4 / 3 : ℝ) := by
    simpa only [Real.exp_log (by positivity : (0 : ℝ) < 4 / 3)] using
      Real.exp_le_exp.mpr htop
  have hf : ⌊Real.exp t⌋₊ = 1 := (Nat.floor_eq_iff (Real.exp_pos t).le).mpr
    ⟨by simpa using hlow, by norm_num; linarith only [hhigh]⟩
  rw [logarithmicCenteredSawtooth, Int.fract,
    ← natCast_floor_eq_intCast_floor (Real.exp_pos t).le, hf, Nat.cast_one]
  linarith only [hhigh]

theorem logarithmicReciprocalSawtoothCorrelation_small_time_lower
    {T : ℝ} (hT : 0 ≤ T) (htop : T ≤ Real.log (4 / 3 : ℝ)) :
    T / 36 ≤ logarithmicReciprocalSawtoothCorrelation T := by
  have hi := intervalIntegrable_logarithmicReciprocalSawtooth T 0 T
  have hp (s : ℝ) (hs : s ∈ Icc 0 T) :
      (1 / 36 : ℝ) ≤ logarithmicCenteredSawtooth (T - s) * logarithmicCenteredSawtooth s := by
    have h1 := sawtooth_small_time (sub_nonneg.mpr hs.2) (by linarith only [htop, hs.1])
    have h2 := sawtooth_small_time hs.1 (hs.2.trans htop)
    have hprod := mul_le_mul
      (show (1 / 6 : ℝ) ≤ -logarithmicCenteredSawtooth (T - s) by linarith only [h1])
      (show (1 / 6 : ℝ) ≤ -logarithmicCenteredSawtooth s by linarith only [h2])
      (by positivity : (0 : ℝ) ≤ 1 / 6)
      (show 0 ≤ -logarithmicCenteredSawtooth (T - s) by linarith only [h1])
    nlinarith only [hprod]
  calc
    _ = ∫ _s in (0 : ℝ)..T, (1 / 36 : ℝ) := by simp; ring
    _ ≤ _ := intervalIntegral.integral_mono_on hT intervalIntegrable_const hi hp

private theorem small_time_cutoff {T : ℝ}
    (hT : 0 ≤ T) (htop : T ≤ Real.log (4 / 3 : ℝ)) :
    ⌊Real.exp (T / 2)⌋₊ = 1 := by
  have hlow : 1 ≤ Real.exp (T / 2) := Real.one_le_exp_iff.mpr (by linarith only [hT])
  have hsq : Real.exp (T / 2) ^ 2 ≤ (4 / 3 : ℝ) := by
    have he : Real.exp (T / 2) ^ 2 = Real.exp T := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    rw [he]
    simpa only [Real.exp_log (by positivity : (0 : ℝ) < 4 / 3)] using
      Real.exp_le_exp.mpr htop
  apply (Nat.floor_eq_iff (Real.exp_pos _).le).mpr
  constructor
  · simpa using hlow
  · norm_num
    nlinarith only [hsq, hlow]

theorem ccmPrimeDeficitShortCorrelationAction_small_time {T : ℝ}
    (hT : 0 ≤ T) (htop : T ≤ Real.log (4 / 3 : ℝ)) (z : ℝ) :
    ccmPrimeDeficitShortCorrelationAction T z =
      Real.exp (z * (T - 2)) * logarithmicReciprocalSawtoothCorrelation T := by
  simp [ccmPrimeDeficitShortCorrelationAction, small_time_cutoff hT htop]

theorem deriv_ccmPrimeDeficitShortCorrelationAction_neg_of_small_time
    {T : ℝ} (hT : 0 < T) (htop : T ≤ Real.log (4 / 3 : ℝ)) :
    deriv (ccmPrimeDeficitShortCorrelationAction T) 0 < 0 := by
  have hpair : 2 * ccmPrimeDeficitShortReciprocalPairing T =
      (T - 2) * logarithmicReciprocalSawtoothCorrelation T := by
    rw [ccmPrimeDeficitShortReciprocalPairing_eq_square]
    simp only [small_time_cutoff hT.le htop, Finset.Icc_self, Finset.sum_singleton,
      ArithmeticFunction.moebius_apply_one, Int.cast_one, one_mul, Nat.cast_one, Real.log_one, sub_zero]
    ring
  rw [(hasDerivAt_ccmPrimeDeficitShortCorrelationAction_zero T).deriv, hpair]
  have hlog := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 4 / 3)
  have hleft : T - 2 < 0 := by linarith only [htop, hlog]
  have hright : 0 < logarithmicReciprocalSawtoothCorrelation T :=
    (div_pos hT (by positivity)).trans_le
      (logarithmicReciprocalSawtoothCorrelation_small_time_lower hT.le htop)
  exact mul_neg_of_neg_of_pos hleft hright

theorem ccmPrimeDeficitShortCorrelationAction_not_invariant :
    ¬ ∀ z : ℝ, ccmPrimeDeficitShortCorrelationAction (Real.log (4 / 3 : ℝ)) z =
      ccmPrimeDeficitShortCorrelationAction (Real.log (4 / 3 : ℝ)) 0 := by
  intro h
  have hf : ccmPrimeDeficitShortCorrelationAction (Real.log (4 / 3 : ℝ)) =
      fun _ => ccmPrimeDeficitShortCorrelationAction (Real.log (4 / 3 : ℝ)) 0 := funext h
  have hn := deriv_ccmPrimeDeficitShortCorrelationAction_neg_of_small_time
    (Real.log_pos (by norm_num : (1 : ℝ) < 4 / 3)) le_rfl
  rw [hf, deriv_const] at hn
  exact lt_irrefl 0 hn

end RHTower
