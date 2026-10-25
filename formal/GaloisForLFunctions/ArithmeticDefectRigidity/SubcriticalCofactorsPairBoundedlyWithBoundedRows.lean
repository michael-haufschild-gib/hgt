import GaloisForLFunctions.ArithmeticDefectRigidity.TheSourcePowerSavingControlsMovingSuccessors
import GaloisForLFunctions.RHTower.CreaseBudgetPrimeMass

/-!
# Subcritical cofactors pair boundedly with bounded rows

The source power envelope makes absolute pronic cofactor mass summable,
uniformly in horizon and cofactor. A finite origin-to-energy square ratio
therefore makes all mixed bounded-row pairings vanish on escape.
-/

section

noncomputable section
set_option autoImplicit false
open Finset Filter Topology RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- Subcritical source growth bounds every cofactor's absolute pronic mass, uniformly in horizon. -/
theorem exists_uniform_abs_pronic_cofactor_bound (ε : SubcriticalDamping) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ+, ∀ T : ℕ,
      (∑ n ∈ Icc 1 T, |rowDilate j (pmPowerDampedCenteredDivisorPrefix ε) n| /
        ((n : ℝ) * ((n : ℝ) + 1))) ≤ C := by
  obtain ⟨B, hB, hA⟩ := exists_receiver_small_power_envelope ε zero_lt_one
  let a : ℝ := 1 - (ε : ℝ)
  have ha0 : 0 ≤ a := by dsimp [a]; linarith only [ε.property.2]
  have ha : a < 1 := by dsimp [a]; linarith only [ε.property.1]
  have hden : 0 < (2 - a) - 1 := by linarith only [ha]
  refine ⟨(1 + B) * (1 + 1 / ((2 - a) - 1)), by positivity, fun j T => ?_⟩
  have hcell (n : ℕ) (hn : n ∈ Icc 1 T) :
      |rowDilate j (pmPowerDampedCenteredDivisorPrefix ε) n| /
          ((n : ℝ) * ((n : ℝ) + 1)) ≤ (1 + B) * (n : ℝ) ^ (-(2 - a)) := by
    have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hpow : ((n / j : ℕ) : ℝ) ^ a ≤ (n : ℝ) ^ a :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.div_le_self n j) ha0
    have hone : 1 ≤ (n : ℝ) ^ a := Real.one_le_rpow (by exact_mod_cast hn1) ha0
    have hrow : |rowDilate j (pmPowerDampedCenteredDivisorPrefix ε) n| ≤
        (1 + B) * (n : ℝ) ^ a := by
      have hsource := hA (n / j)
      simp only [one_mul] at hsource
      change |pmPowerDampedCenteredDivisorPrefix ε (n / j)| ≤ _
      have hBpow := mul_le_mul_of_nonneg_left hone hB
      nlinarith only [hsource, hpow, hBpow]
    have hp : (n : ℝ) ^ a = (n : ℝ) ^ (-(2 - a)) * (n : ℝ) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hn0]
      congr 1
      ring
    apply (div_le_iff₀ (by positivity)).mpr
    calc
      _ ≤ (1 + B) * (n : ℝ) ^ a := hrow
      _ = (1 + B) * (n : ℝ) ^ (-(2 - a)) * (n : ℝ) ^ 2 := by rw [hp]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by nlinarith only [hn0.le] : (n : ℝ) ^ 2 ≤ (n : ℝ) * ((n : ℝ) + 1))
        (by positivity)
  calc
    _ ≤ ∑ n ∈ Icc 1 T, (1 + B) * (n : ℝ) ^ (-(2 - a)) := sum_le_sum hcell
    _ = (1 + B) * ∑ n ∈ Icc 1 T, (n : ℝ) ^ (-(2 - a)) := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_Icc_rpow_neg_le (by linarith : 1 < 2 - a) T)
      (by positivity)

/-- A bounded row pairs uniformly with every actual subcritical cofactor. -/
theorem exists_uniform_bounded_row_pairing (ε : SubcriticalDamping) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : ℕ → ℝ, ∀ D : ℝ,
      (∀ n, |g n| ≤ D) → ∀ j : ℕ+, ∀ T : ℕ,
        |pronicPairing T (rowDilate j (pmPowerDampedCenteredDivisorPrefix ε)) g| ≤ C * D := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_abs_pronic_cofactor_bound ε
  refine ⟨C, hC, fun g D hg j T => ?_⟩
  have hD : 0 ≤ D := (abs_nonneg (g 0)).trans (hg 0)
  calc
    _ ≤ ∑ n ∈ Icc 1 T,
        |rowDilate j (pmPowerDampedCenteredDivisorPrefix ε) n * g n /
          ((n : ℝ) * ((n : ℝ) + 1))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Icc 1 T,
        |rowDilate j (pmPowerDampedCenteredDivisorPrefix ε) n| /
          ((n : ℝ) * ((n : ℝ) + 1)) * D := by
      apply sum_le_sum
      intro n hn
      rw [abs_div, abs_mul,
        abs_of_nonneg (show 0 ≤ (n : ℝ) * ((n : ℝ) + 1) by positivity)]
      calc
        _ ≤ (|rowDilate j (pmPowerDampedCenteredDivisorPrefix ε) n| * D) /
            ((n : ℝ) * ((n : ℝ) + 1)) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hg n) (abs_nonneg _))
            (by positivity)
        _ = _ := by ring
    _ = (∑ n ∈ Icc 1 T,
        |rowDilate j (pmPowerDampedCenteredDivisorPrefix ε) n| /
          ((n : ℝ) * ((n : ℝ) + 1))) * D := (sum_mul _ _ _).symm
    _ ≤ C * D := mul_le_mul_of_nonneg_right (hbound j T) hD

/-- A bounded origin-trace energy ratio makes the trace divided by energy vanish. -/
theorem origin_div_energy_tendsto_zero (M E : ℕ → ℝ)
    (hE : Tendsto E atTop atTop) {c : ℝ}
    (hM : Tendsto (fun m => M m ^ 2 / E m) atTop (𝓝 c)) :
    Tendsto (fun m => M m / E m) atTop (𝓝 0) := by
  have hinv : Tendsto (fun m => 1 / E m) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop hE
  have hsq := hM.mul hinv
  rw [mul_zero] at hsq
  have habs := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  rw [Real.sqrt_zero] at habs
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  convert habs using 1
  funext m
  simp only [Function.comp_apply]
  rw [show M m ^ 2 / E m * (1 / E m) = (M m / E m) ^ 2 by ring,
    Real.sqrt_sq_eq_abs]

end GaloisForLFunctions.ArithmeticDefectRigidity

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.exists_uniform_bounded_row_pairing
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.origin_div_energy_tendsto_zero
end
end
