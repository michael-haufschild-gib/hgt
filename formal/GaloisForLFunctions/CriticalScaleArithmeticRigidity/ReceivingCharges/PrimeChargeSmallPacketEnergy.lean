import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.LogarithmFreeCriticalConductorResiduals
import GaloisForLFunctions.CompletedArithmeticForms.PrimePacketCoercivity
import GaloisForLFunctions.CompletedArithmeticForms.ConductorEnergiesHaveAUniformLogarithmicUpperBound
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeUniformCoefficients

/-!
# Complete energy of packets below the overlap scale

The full conductor residual is summed with its two exact coefficient
moments. The remaining discrepancy is the polarized harmonic Gram error.
The completed conductor energies, including conductor one, remain literal.
-/

noncomputable section

open Finset MeasureTheory
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell CompletedArithmeticForms

/-- A small packet retains its completed conductor diagonal with two explicit residual moments. -/
theorem exists_complete_packet_diagonal_error_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Q N : ℕ} {c : ℝ},
      2 ≤ Q → Q * Q ≤ N → 18 * (1 + Real.log Q) ≤ Real.log N →
      1 ≤ c → 4 * (linearNearRowRadius c + 1) ^ 2 ≤ N → c ^ 4 ≤ N →
      ∀ a : ℕ → ℝ,
      let E := completedConductorEnergy φ c
      let u := ∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N
      |completeWeilEnergy φ c N u - ∑ m ∈ Icc 1 Q, E m * a m ^ 2| ≤
        K * ((c / Real.log N) * (∑ m ∈ Icc 1 Q, |a m| * (m : ℝ) ^ 2) ^ 2 +
          (c ^ 5 * Real.log N / N) * (∑ m ∈ Icc 1 Q, |a m| * (m : ℝ) ^ 5) ^ 2) +
        9 * (1 + Real.log Q) / Real.log N *
          Real.sqrt (∑ m ∈ Icc 1 Q, (E m * a m) ^ 2) *
          Real.sqrt (∑ m ∈ Icc 1 Q, a m ^ 2) := by
  obtain ⟨K, hK, hb⟩ := exists_completeWeil_bilinear_conductor_residual_log_free hφ hsupp hM
  refine ⟨K, hK, ?_⟩
  intro Q N c hQ hQN hlog hc hrad hc4 a
  dsimp only
  let E := completedConductorEnergy φ c
  let v := fun m => normalizedRamanujanHorizonVector m N
  let u := ∑ m ∈ Icc 1 Q, a m • v m
  let d := ∑ m ∈ Icc 1 Q, (E m * a m) • v m
  let r := fun m l => ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) (v m) - E m • v m, v l⟫
  have hentry (m : ℕ) (hm : m ∈ Icc 1 Q) (l : ℕ) (hl : l ∈ Icc 1 Q) :
      |r m l| ≤ K * ((m : ℝ) ^ 2 * (l : ℝ) ^ 2 * (c / Real.log N) +
        ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N)) := by
    have hR : max 2 (max m l) ≤ Q :=
      max_le hQ (max_le (mem_Icc.mp hm).2 (mem_Icc.mp hl).2)
    have hR0 : (0 : ℝ) < (max 2 (max m l) : ℕ) := by
      exact_mod_cast (zero_lt_two.trans_le (le_max_left 2 (max m l)))
    have hlogR := Real.log_le_log hR0 (by exact_mod_cast hR)
    exact hb (mem_Icc.mp hm).1 (mem_Icc.mp hl).1
      ((Nat.mul_le_mul hR hR).trans hQN)
      ((mul_le_mul_of_nonneg_left (add_le_add_left hlogR 1) (by norm_num)).trans hlog)
      hc hrad hc4
  have herror : completeWeilEnergy φ c N u - ⟪d, u⟫ =
      ∑ m ∈ Icc 1 Q, ∑ l ∈ Icc 1 Q, a m * a l * r m l := by
    simp only [completeWeilEnergy, u, d, r, map_sum, map_smul,
      sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
      inner_sub_left, ← sum_sub_distrib]
    apply sum_congr rfl
    intro m _
    exact sum_congr rfl fun l _ => by ring
  have herr : |completeWeilEnergy φ c N u - ⟪d, u⟫| ≤
      K * ((c / Real.log N) * (∑ m ∈ Icc 1 Q, |a m| * (m : ℝ) ^ 2) ^ 2 +
        (c ^ 5 * Real.log N / N) * (∑ m ∈ Icc 1 Q, |a m| * (m : ℝ) ^ 5) ^ 2) := by
    rw [herror]
    calc
      _ ≤ ∑ m ∈ Icc 1 Q, ∑ l ∈ Icc 1 Q,
          |a m| * |a l| * (K * ((m : ℝ) ^ 2 * (l : ℝ) ^ 2 * (c / Real.log N) +
            ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N))) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m hm => ?_)
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun l hl => ?_)
        rw [abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left (hentry m hm l hl) (by positivity)
      _ = _ := by
        have he : (∑ m ∈ Icc 1 Q, ∑ l ∈ Icc 1 Q,
            |a m| * |a l| * (K * ((m : ℝ) ^ 2 * (l : ℝ) ^ 2 * (c / Real.log N) +
              ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N)))) =
            (∑ m ∈ Icc 1 Q, ∑ l ∈ Icc 1 Q,
              K * (c / Real.log N) * (|a m| * (m : ℝ) ^ 2) * (|a l| * (l : ℝ) ^ 2)) +
            (∑ m ∈ Icc 1 Q, ∑ l ∈ Icc 1 Q,
              K * (c ^ 5 * Real.log N / N) * (|a m| * (m : ℝ) ^ 5) * (|a l| * (l : ℝ) ^ 5)) := by
          rw [← sum_add_distrib]
          apply sum_congr rfl
          intro m _
          rw [← sum_add_distrib]
          exact sum_congr rfl fun l _ => by ring
        rw [he]
        simp only [← mul_sum, ← sum_mul]
        ring
  have hgram := abs_inner_sum_normalizedRamanujanHorizonVector_sub_le hQ hQN
    (fun m => E m * a m) a
  have hdiag : (∑ m ∈ Icc 1 Q, (E m * a m) * a m) =
      ∑ m ∈ Icc 1 Q, E m * a m ^ 2 := sum_congr rfl fun m _ => by ring
  rw [hdiag] at hgram
  exact (abs_sub_le _ ⟪d, u⟫ _).trans (add_le_add herr hgram)

/-- The coherent nonpolar completed diagonal is small uniformly in both overlap and horizon. -/
theorem harmonicPrimeCharge_nonpolar_completedEnergy_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 1 ≤ c) (Q N : ℕ) (t : ℝ) :
    (∑ m ∈ (Icc 1 Q).filter (fun m => m ≠ 1),
      completedConductorEnergy φ c m * harmonicPrimeChargeCoefficients Q N t m ^ 2) ≤
      (|completeWeilSelfFinitePart φ 1| + 3) * (t / primePoleScale Q) ^ 2 *
        ((∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) + primePoleScale Q) := by
  let D := |completeWeilSelfFinitePart φ 1| + 3
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hE (m : ℕ) (hm : 0 < m) : completedConductorEnergy φ c m ≤ D * (1 + Real.log m) := by
    refine (completedConductorEnergy_le_logarithmic_uniform hφ hsupp hM hc hm).trans ?_
    have h := mul_nonneg (add_nonneg (abs_nonneg (completeWeilSelfFinitePart φ 1)) zero_le_one)
      (Real.log_natCast_nonneg m)
    dsimp only [D]
    nlinarith only [h]
  calc
    _ ≤ D * (∑ m ∈ (Icc 1 Q).filter (fun m => m ≠ 1),
        (1 + Real.log m) * harmonicPrimeChargeCoefficients Q N t m ^ 2) := by
      rw [mul_sum]
      exact sum_le_sum fun m hm =>
        (mul_le_mul_of_nonneg_right (hE m (mem_Icc.mp (mem_filter.mp hm).1).1)
          (sq_nonneg _)).trans_eq (mul_assoc _ _ _)
    _ ≤ _ := (mul_le_mul_of_nonneg_left (harmonicPrimeCharge_nonpolar_log_sq_le Q N t) hD).trans_eq
      (by dsimp only [D]; ring)

#print axioms exists_complete_packet_diagonal_error_bound
#print axioms harmonicPrimeCharge_nonpolar_completedEnergy_le

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
