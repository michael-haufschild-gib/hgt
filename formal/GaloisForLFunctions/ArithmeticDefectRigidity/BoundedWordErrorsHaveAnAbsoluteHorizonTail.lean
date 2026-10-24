import GaloisForLFunctions.ArithmeticDefectRigidity.CofactorSuccessorWordsHaveABoundaryCost
import GaloisForLFunctions.RHTower.Sieve.PSeriesTailAboveCutoff

/-!
# Bounded word errors have an absolute horizon-tail budget

The actual forcing's power envelope pays every newly entering cell beyond a cutoff, uniformly
in the final horizon. Word-boundary work is therefore controlled absolutely by its boundary
length times a negative power of the cutoff. This pays bounded successor/cofactor errors;
it does not replace the unbounded receiver by a bounded row.
-/

open Finset Filter Topology RHTower RHTower.Sieve
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- An explicit constant for forcing mass beyond a moving horizon cutoff. -/
def forcingHorizonTailBudget (ε : ℝ) : ℝ :=
  (pmPowerDampedDivisorDensity ε).re * forcingExpansionBudget ε * ((1 + ε) / ε)

theorem forcingHorizonTailBudget_nonneg (ε : SubcriticalDamping) :
    0 ≤ forcingHorizonTailBudget ε :=
  mul_nonneg
    (mul_nonneg (RHTower.pmPowerDampedDivisorDensity_re_pos ε.property.1).le
      (forcingExpansionBudget_nonneg ε))
    (div_nonneg (by linarith [ε.property.1]) ε.property.1.le)

/-- Complete positive forcing mass on the cells beyond `H`, up to arbitrary `T`. -/
def forcingHorizonTailMass (ε : ℝ) (H T : ℕ) : ℝ :=
  ∑ n ∈ Icc (H + 1) T, inversionDefect ε n / ((n : ℝ) * ((n : ℝ) + 1))

private theorem forcing_cell_le_power (ε : SubcriticalDamping) (n : ℕ) (hn : 1 ≤ n) :
    inversionDefect ε n / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      (pmPowerDampedDivisorDensity (ε : ℝ)).re * forcingExpansionBudget ε *
        (n : ℝ) ^ (-(1 + (ε : ℝ))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm := (RHTower.pmPowerDampedDivisorDensity_re_pos ε.property.1).le
  have hM := forcingExpansionBudget_nonneg ε
  have hpow : (n : ℝ) ^ (1 - (ε : ℝ)) =
      (n : ℝ) ^ (-(1 + (ε : ℝ))) * (n : ℝ) * (n : ℝ) := by
    rw [← Real.rpow_add_one hn0.ne', ← Real.rpow_add_one hn0.ne']
    congr 1
    ring
  calc
    _ ≤ ((pmPowerDampedDivisorDensity (ε : ℝ)).re * forcingExpansionBudget ε *
        (n : ℝ) ^ (1 - (ε : ℝ))) / ((n : ℝ) * ((n : ℝ) + 1)) :=
      div_le_div_of_nonneg_right (inversionDefect_le_power ε n hn) (by positivity)
    _ ≤ ((pmPowerDampedDivisorDensity (ε : ℝ)).re * forcingExpansionBudget ε *
        (n : ℝ) ^ (1 - (ε : ℝ))) / ((n : ℝ) * (n : ℝ)) :=
      div_le_div_of_nonneg_left
        (mul_nonneg (mul_nonneg hm hM) (Real.rpow_nonneg hn0.le _))
        (mul_pos hn0 hn0)
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hn0.le)
    _ = _ := by rw [hpow]; field_simp [hn0.ne']

/-- The absolute new-cell forcing cost decays as a negative power of the cutoff. -/
theorem forcingHorizonTailMass_le (ε : SubcriticalDamping) (H T : ℕ) :
    forcingHorizonTailMass ε H T ≤ forcingHorizonTailBudget ε *
      ((H + 1 : ℕ) : ℝ) ^ (-(ε : ℝ)) := by
  have hmM := mul_nonneg (RHTower.pmPowerDampedDivisorDensity_re_pos ε.property.1).le
    (forcingExpansionBudget_nonneg ε)
  calc
    forcingHorizonTailMass ε H T ≤ ∑ n ∈ Icc (H + 1) T,
        (pmPowerDampedDivisorDensity (ε : ℝ)).re * forcingExpansionBudget ε *
          (n : ℝ) ^ (-(1 + (ε : ℝ))) := by
      exact sum_le_sum fun n hn => forcing_cell_le_power ε n (by
        have := (mem_Icc.mp hn).1
        omega)
    _ = (pmPowerDampedDivisorDensity (ε : ℝ)).re * forcingExpansionBudget ε *
        ∑ n ∈ Icc (H + 1) T, (n : ℝ) ^ (-(1 + (ε : ℝ))) := by rw [mul_sum]
    _ ≤ (pmPowerDampedDivisorDensity (ε : ℝ)).re * forcingExpansionBudget ε *
        (((1 + (ε : ℝ)) / ((1 + (ε : ℝ)) - 1)) *
          ((H + 1 : ℕ) : ℝ) ^ (1 - (1 + (ε : ℝ)))) :=
      mul_le_mul_of_nonneg_left
        (sum_rpow_neg_tail_le (by linarith [ε.property.1]) (by omega : 1 ≤ H + 1)) hmM
    _ = _ := by
      rw [show (1 + (ε : ℝ)) - 1 = (ε : ℝ) by ring,
        show 1 - (1 + (ε : ℝ)) = -(ε : ℝ) by ring]
      unfold forcingHorizonTailBudget
      ring

/-- The signed work of a word's boundary error on newly entering cells. -/
def wordForcingHorizonTailWork (ε : ℝ) (w : CellWord) (H T : ℕ) : ℝ :=
  ∑ n ∈ Icc (H + 1) T,
    (pmPowerDampedCenteredDivisorPrefix ε (w.apply n) -
      pmPowerDampedCenteredDivisorPrefix ε (n / w.denominator)) * inversionDefect ε n /
        ((n : ℝ) * ((n : ℝ) + 1))

/-- Actual word-boundary errors have an absolute tail budget uniform in the final horizon. -/
theorem abs_wordForcingHorizonTailWork_le (ε : SubcriticalDamping) (w : CellWord) (H T : ℕ) :
    |wordForcingHorizonTailWork ε w H T| ≤
      (w.boundaryCost : ℝ) * forcingHorizonTailBudget ε *
        ((H + 1 : ℕ) : ℝ) ^ (-(ε : ℝ)) := by
  unfold wordForcingHorizonTailWork
  calc
    _ ≤ ∑ n ∈ Icc (H + 1) T,
        |(pmPowerDampedCenteredDivisorPrefix (ε : ℝ) (w.apply n) -
          pmPowerDampedCenteredDivisorPrefix (ε : ℝ) (n / w.denominator)) *
          inversionDefect ε n / ((n : ℝ) * ((n : ℝ) + 1))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Icc (H + 1) T,
        (w.boundaryCost : ℝ) * inversionDefect ε n / ((n : ℝ) * ((n : ℝ) + 1)) := by
      refine sum_le_sum fun n _ => ?_
      rw [abs_div, abs_mul, abs_of_nonneg (inversionDefect_nonneg ε.property.1 n),
        abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1) by positivity)]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (abs_receiver_word_sub_dilation_le ε w n)
          (inversionDefect_nonneg ε.property.1 n)) (by positivity)
    _ = (w.boundaryCost : ℝ) * forcingHorizonTailMass ε H T := by
      rw [forcingHorizonTailMass, mul_sum]
      exact sum_congr rfl fun n _ => by ring
    _ ≤ _ := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (forcingHorizonTailMass_le ε H T) (Nat.cast_nonneg _)

/-- The absolute tail budget tends to zero without any receiver normalization. -/
theorem tendsto_wordForcingHorizonTailBudget_zero (ε : SubcriticalDamping) (w : CellWord) :
    Tendsto (fun H : ℕ => (w.boundaryCost : ℝ) * forcingHorizonTailBudget ε *
      ((H + 1 : ℕ) : ℝ) ^ (-(ε : ℝ))) atTop (𝓝 0) := by
  have hp : Tendsto (fun H : ℕ => ((H + 1 : ℕ) : ℝ) ^ (-(ε : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop ε.property.1).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  simpa only [mul_zero] using hp.const_mul ((w.boundaryCost : ℝ) * forcingHorizonTailBudget ε)

/-- A single cutoff pays the word's absolute boundary work at every later final horizon. -/
theorem eventually_wordForcingHorizonTailWork_small (ε : SubcriticalDamping) (w : CellWord)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ H : ℕ in atTop, ∀ T : ℕ, |wordForcingHorizonTailWork ε w H T| < η := by
  filter_upwards [(tendsto_wordForcingHorizonTailBudget_zero ε w).eventually
    (isOpen_Iio.mem_nhds hη)] with H hH
  intro T
  exact (abs_wordForcingHorizonTailWork_le ε w H T).trans_lt hH

end GaloisForLFunctions.ArithmeticDefectRigidity
