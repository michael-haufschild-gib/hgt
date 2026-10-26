import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.LongModulusExactDecomposition
import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheOscillatingSmoothPowerIsPaidExactlyAtTheZerosOfZeta
import GaloisForLFunctions.RHTower.GaussSpikeMass

/-!
# Bounded pronic energy of the actual square-root Möbius head

The short sawtooth is bounded by the head of a power series. At the square-root
cutoff this gives the exact exponent `(1-ε)/2`, and the existing pronic comparison
retains the constants `(1+1/(1-ε))²(1+1/ε)` for every horizon.
-/

noncomputable section
open ArithmeticFunction
open scoped BigOperators

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
set_option autoImplicit false

/-- Absolute control is used only on the finite short-modulus head. -/
theorem abs_pmShortModulusSawtooth_le_power_sum (ε : ℝ) (n D : ℕ) :
    |pmShortModulusSawtooth ε n D| ≤ ∑ d ∈ Finset.Icc 1 D, (d : ℝ) ^ (-ε) := by
  unfold pmShortModulusSawtooth
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  have hd0 : 0 < d := by have h := (Finset.mem_Icc.mp hd).1; omega
  have hμ : |(moebius d : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]
    exact_mod_cast abs_moebius_le_one
  have hw : |pmLongModulusWeight ε d| ≤ (d : ℝ) ^ (-ε) := by
    rw [pmLongModulusWeight, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg d) _) hμ
  rw [abs_mul]
  calc
    _ ≤ (d : ℝ) ^ (-ε) * 1 :=
      mul_le_mul hw (SignedArithmeticEnergyIncidence.abs_natDiv_sub_div_le n d hd0)
        (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg d) _)
    _ = _ := mul_one _

private theorem abs_short_sqrt_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {n : ℕ} (hn : 1 ≤ n) :
    |pmShortModulusSawtooth ε n (Nat.sqrt n)| ≤
      (1 + 1 / (1 - ε)) * Real.sqrt n ^ (1 - ε) := by
  have hσ : 0 < 1 - ε := by linarith
  have hs1 : 1 ≤ Nat.sqrt n := Nat.sqrt_pos.mpr hn
  have hs0 : (0 : ℝ) ≤ Nat.sqrt n := Nat.cast_nonneg _
  have hsr : (Nat.sqrt n : ℝ) ≤ Real.sqrt n := Real.nat_sqrt_le_real_sqrt
  have hr1 : (1 : ℝ) ≤ Real.sqrt n := (by exact_mod_cast hs1 : (1 : ℝ) ≤ Nat.sqrt n).trans hsr
  have hpow := Real.rpow_le_rpow hs0 hsr hσ.le
  have hpow1 := Real.one_le_rpow hr1 hσ.le
  have hdiv := div_le_div_of_nonneg_right hpow hσ.le
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 (Nat.sqrt n), (d : ℝ) ^ (-ε) :=
      abs_pmShortModulusSawtooth_le_power_sum ε n (Nat.sqrt n)
    _ ≤ 1 + (Nat.sqrt n : ℝ) ^ (1 - ε) / (1 - ε) :=
      RHTower.sum_rpow_neg_head_le hε hε1 (Nat.sqrt n)
    _ ≤ (1 + 1 / (1 - ε)) * Real.sqrt n ^ (1 - ε) := by
      calc
        _ ≤ Real.sqrt n ^ (1 - ε) + Real.sqrt n ^ (1 - ε) / (1 - ε) :=
          add_le_add hpow1 hdiv
        _ = _ := by ring

/-- The exact square-root cutoff and exponent, including the zero numerator. -/
theorem abs_pmShortModulusSawtooth_sqrt_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (n : ℕ) :
    |pmShortModulusSawtooth ε n ⌊Real.sqrt (n : ℝ)⌋₊| ≤
      (1 + 1 / (1 - ε)) * (n : ℝ) ^ ((1 - ε) / 2) := by
  rw [Real.nat_floor_real_sqrt_eq_nat_sqrt]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hp : (1 - ε) / 2 ≠ 0 := ne_of_gt (by linarith)
    simp [pmShortModulusSawtooth, Real.zero_rpow hp]
  · have hh := abs_short_sqrt_le hε hε1 (Nat.succ_le_iff.mpr hn)
    have hp : Real.sqrt (n : ℝ) ^ (1 - ε) = (n : ℝ) ^ ((1 - ε) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg n)]
      congr 1
      ring
    rwa [hp] at hh

/-- The square-root head has the exact bounded pronic energy at every horizon. -/
theorem sum_pmShortModulusSawtooth_sqrt_pronic_le
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (T : ℕ) :
    (∑ n ∈ Finset.Icc 1 T,
      (pmShortModulusSawtooth ε n ⌊Real.sqrt (n : ℝ)⌋₊) ^ 2 /
        ((n : ℝ) * ((n : ℝ) + 1))) ≤
      (1 + 1 / (1 - ε)) ^ 2 * (1 + 1 / ε) := by
  simpa only [Real.nat_floor_real_sqrt_eq_nat_sqrt] using
    TransHorizonIncidenceMechanics.sum_sq_le_of_abs_le_sqrt_rpow hε
      (fun n hn => abs_short_sqrt_le hε hε1 hn) T

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
