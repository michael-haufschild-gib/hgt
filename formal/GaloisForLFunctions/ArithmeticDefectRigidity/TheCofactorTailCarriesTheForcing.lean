import GaloisForLFunctions.ArithmeticDefectRigidity.ForcingScaleSeparation
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheDilationSelfSimilarityOfThePronicMeasure

/-!
# The forcing escapes every fixed cofactor head

For the actual source, the proper cofactor sum minus any fixed head approaches the complete
forcing in the forcing norm. The error is bounded by the receiver energy times the square of
one plus the explicit head coefficient. This also prices moving cofactor cutoffs.

The estimate retains the signed tail as a vector. It does not replace the tail by a sum of
absolute values, and it does not claim that the receiver energy is bounded.
-/

open Finset Filter Topology RHTower RHTower.Sieve
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- The sharp finite cofactor-head coefficient in the pronic metric. -/
def cofactorHeadCoefficient (ε : ℝ) (J : ℕ) : ℝ :=
  ∑ j ∈ Icc 2 J, (j : ℝ) ^ (-ε) * (1 / Real.sqrt (j : ℝ))

theorem cofactorHeadCoefficient_nonneg (ε : ℝ) (J : ℕ) :
    0 ≤ cofactorHeadCoefficient ε J :=
  sum_nonneg fun j _ => by positivity

/-- A cofactor head costs at most its number of available integer scales. -/
theorem cofactorHeadCoefficient_le (ε : SubcriticalDamping) (J : ℕ) :
    cofactorHeadCoefficient ε J ≤ (J : ℝ) := by
  unfold cofactorHeadCoefficient
  calc _ ≤ ∑ _j ∈ Icc 2 J, (1 : ℝ) := by
      refine sum_le_sum fun j hj => ?_
      have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by
        have := (mem_Icc.mp hj).1; omega)
      have hr : (j : ℝ) ^ (-(ε : ℝ)) ≤ 1 := by
        calc _ ≤ (j : ℝ) ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hj1
            (neg_nonpos.mpr ε.property.1.le)
          _ = 1 := Real.rpow_zero _
      have hs : (1 : ℝ) ≤ Real.sqrt (j : ℝ) := by
        rw [Real.le_sqrt (by norm_num) (Nat.cast_nonneg j)]
        simpa only [one_pow] using hj1
      have hi : 1 / Real.sqrt (j : ℝ) ≤ 1 :=
        (div_le_one (lt_of_lt_of_le zero_lt_one hs)).mpr hs
      simpa only [one_mul] using mul_le_mul hr hi (by positivity) zero_le_one
    _ = ((Icc 2 J).card : ℝ) := by simp
    _ ≤ (J : ℝ) := by
      exact_mod_cast (show (Icc 2 J).card ≤ J by simp only [Nat.card_Icc]; omega)

/-- The vector estimate underlying the finite-head pairing bound. -/
theorem pronicNorm_cofactorHead_le (ε : ℝ) (J T : ℕ) :
    pronicNorm T (offDiagonalUnitDilationHead ε J) ≤
      cofactorHeadCoefficient ε J * Real.sqrt (dampedMobiusEnergy ε T) := by
  have hext : ∀ n ∈ Icc 1 T, offDiagonalUnitDilationHead ε J n =
      ∑ j ∈ Icc 2 J, (j : ℝ) ^ (-ε) *
        rowDilate j (pmPowerDampedCenteredDivisorPrefix ε) n := by
    intro n _
    unfold offDiagonalUnitDilationHead
    have hsub : Icc 2 (min J n) ⊆ Icc 2 J := by
      intro j hj
      exact mem_Icc.mpr ⟨(mem_Icc.mp hj).1,
        (mem_Icc.mp hj).2.trans (min_le_left J n)⟩
    rw [← sum_subset hsub]
    · exact sum_congr rfl fun j _ => by rw [rowDilate]
    · intro j hj hjmin
      have hjn : n < j := by
        have hJ := mem_Icc.mp hj
        by_contra hn
        exact hjmin (mem_Icc.mpr ⟨hJ.1, le_min hJ.2 (by omega)⟩)
      rw [rowDilate, Nat.div_eq_of_lt hjn,
        ArithmeticContinuationAndCriticalEnergy.pmPowerDampedCenteredDivisorPrefix_zero]
      ring
  rw [pronicNorm_congr hext]
  refine (pronicNorm_sum_le T (Icc 2 J) _).trans ?_
  rw [cofactorHeadCoefficient, sum_mul]
  refine sum_le_sum fun j hj => ?_
  have hj1 : 1 ≤ j := by have := (mem_Icc.mp hj).1; omega
  have hr : 0 ≤ (j : ℝ) ^ (-ε) := Real.rpow_nonneg (Nat.cast_nonneg j) _
  rw [pronicNorm_const_mul hr, ← pronicNorm_centeredPrefix ε T, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (pronicNorm_rowDilate_le_sharp hj1 T _
      (ArithmeticContinuationAndCriticalEnergy.pmPowerDampedCenteredDivisorPrefix_zero ε)) hr

/-- The signed proper cofactor sum beyond the chosen head. -/
def cofactorTail (ε : ℝ) (J n : ℕ) : ℝ :=
  offDiagonalUnitDilation ε n - offDiagonalUnitDilationHead ε J n

/-- The squared distance from the cofactor tail to the complete forcing. -/
def cofactorTailErrorEnergy (ε : ℝ) (J T : ℕ) : ℝ :=
  pronicNorm T (fun n => cofactorTail ε J n - inversionDefect ε n) ^ 2

theorem cofactorTailErrorEnergy_nonneg (ε : ℝ) (J T : ℕ) :
    0 ≤ cofactorTailErrorEnergy ε J T := sq_nonneg _

/-- Discarding the receiver and a finite cofactor head has an exact, explicit energy budget. -/
theorem cofactorTailErrorEnergy_le (ε : ℝ) (J T : ℕ) :
    cofactorTailErrorEnergy ε J T ≤
      (1 + cofactorHeadCoefficient ε J) ^ 2 * dampedMobiusEnergy ε T := by
  have heq : pronicNorm T (fun n => cofactorTail ε J n - inversionDefect ε n) =
      pronicNorm T (fun n => pmPowerDampedCenteredDivisorPrefix ε n +
        offDiagonalUnitDilationHead ε J n) := by
    calc _ = pronicNorm T (fun n => -(pmPowerDampedCenteredDivisorPrefix ε n +
          offDiagonalUnitDilationHead ε J n)) := by
            apply pronicNorm_congr
            intro n hn
            rw [cofactorTail, inversionDefect_eq_centeredPrefix_add_offDiagonal ε
              (mem_Icc.mp hn).1]
            ring
      _ = _ := pronicNorm_neg _ _
  have hnorm : pronicNorm T (fun n => cofactorTail ε J n - inversionDefect ε n) ≤
      (1 + cofactorHeadCoefficient ε J) * Real.sqrt (dampedMobiusEnergy ε T) := by
    rw [heq]
    calc _ ≤ pronicNorm T (pmPowerDampedCenteredDivisorPrefix ε) +
          pronicNorm T (offDiagonalUnitDilationHead ε J) := pronicNorm_add_le _ _ _
      _ ≤ Real.sqrt (dampedMobiusEnergy ε T) +
          cofactorHeadCoefficient ε J * Real.sqrt (dampedMobiusEnergy ε T) := by
            rw [pronicNorm_centeredPrefix]
            exact add_le_add_left (pronicNorm_cofactorHead_le ε J T) _
      _ = _ := by ring
  have h := pow_le_pow_left₀ (pronicNorm_nonneg T _) hnorm 2
  rw [mul_pow, Real.sq_sqrt (dampedMobiusEnergy_nonneg ε T)] at h
  exact h

/-- The actual source supplies a VK saving uniformly over all cofactor cutoffs. -/
theorem exists_cofactorTailError_le_vk_mul_forcingEnergy (ε : SubcriticalDamping) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℕ in atTop, ∀ J : ℕ,
      cofactorTailErrorEnergy ε J T ≤
        C * (1 + cofactorHeadCoefficient ε J) ^ 2 *
          Real.exp (-(vkKappa * vkScale T / 270)) * forcingEnergy ε T := by
  obtain ⟨C, hC, hbound⟩ := exists_receiver_le_vk_mul_forcingEnergy ε
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with T hT
  intro J
  calc _ ≤ (1 + cofactorHeadCoefficient ε J) ^ 2 * dampedMobiusEnergy ε T :=
      cofactorTailErrorEnergy_le ε J T
    _ ≤ (1 + cofactorHeadCoefficient ε J) ^ 2 *
        (C * Real.exp (-(vkKappa * vkScale T / 270)) * forcingEnergy ε T) :=
      mul_le_mul_of_nonneg_left hT (sq_nonneg _)
    _ = _ := by ring

/-- Every fixed cofactor tail converges to the forcing in the forcing energy normalization. -/
theorem tendsto_cofactorTailError_div_forcingEnergy_zero (ε : SubcriticalDamping) (J : ℕ) :
    Tendsto (fun T => cofactorTailErrorEnergy ε J T / forcingEnergy ε T) atTop (𝓝 0) := by
  have hlim := (tendsto_receiver_div_forcingEnergy_zero ε).const_mul
    ((1 + cofactorHeadCoefficient ε J) ^ 2)
  simp only [mul_zero] at hlim
  refine squeeze_zero
    (fun T => div_nonneg (cofactorTailErrorEnergy_nonneg ε J T)
      (forcingEnergy_nonneg ε T)) (fun T => ?_) hlim
  simpa only [mul_div_assoc] using
    div_le_div_of_nonneg_right (cofactorTailErrorEnergy_le ε J T)
      (forcingEnergy_nonneg ε T)

end GaloisForLFunctions.ArithmeticDefectRigidity
