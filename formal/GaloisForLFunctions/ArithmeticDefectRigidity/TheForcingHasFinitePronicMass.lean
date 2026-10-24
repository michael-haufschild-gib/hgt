import GaloisForLFunctions.ArithmeticDefectRigidity.TheForcingSplitsIntoAPowerAndAnAdmittedRemainder

/-!
# The complete forcing has finite pronic mass

The forcing has power growth `n^(1-ε)`, so its pronic L1 mass is bounded at every positive
subcritical damping. This is compatible with its divergent L2 energy. Bounded cell errors
therefore have bounded work against the complete forcing, even though a generic L2 estimate
would introduce the much larger forcing norm.
-/

open Finset Filter Topology RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.TransHorizonIncidenceMechanics
  (subHalfZetaCoeff subHalfRemainder abs_subHalfRemainder_le floorSumRate
   dampedSignWeight unitSign weightCenteredPrefix firstPronicMoment firstPronicMoment_unitSign
   hasSum_firstPronicMoment unitSign_mem_dampedClass hasSum_vonMangoldt_rpow'
   dampedSign_sum_range_succ_eq_add_Icc)

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- The exact power expansion supplies a uniform upper envelope for the unsigned receiver. -/
theorem abs_majorantCenteredPrefix_le_power (ε : SubcriticalDamping) (n : ℕ) (hn : 1 ≤ n) :
    |majorantCenteredPrefix ε n| ≤ forcingExpansionBudget ε * (n : ℝ) ^ (1 - (ε : ℝ)) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have he : (ε : ℝ) < 1 := by linarith [ε.property.2]
  have hK : 0 ≤ floorSumRate ((1 - (ε : ℝ) : ℝ) : ℂ) := by
    have h := abs_subHalfRemainder_le ε.property.1 he 1
    simp only [Nat.cast_one, Real.sqrt_one, Real.one_rpow, mul_one] at h
    exact (abs_nonneg _).trans h
  have hs : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg n), Real.sqrt_nonneg (n : ℝ),
      Real.one_le_sqrt.mpr hn1]
  have hp := Real.rpow_le_rpow (Real.sqrt_nonneg (n : ℝ)) hs (by linarith : 0 ≤ 1 - (ε : ℝ))
  have hR := abs_subHalfRemainder_le ε.property.1 he n
  have heq : majorantCenteredPrefix ε n =
      subHalfRemainder ε n + subHalfZetaCoeff ε * (n : ℝ) ^ (1 - (ε : ℝ)) := by
    rw [majorantCenteredPrefix_eq_unitReceiver]
    unfold subHalfRemainder
    ring
  rw [heq]
  calc _ ≤ |subHalfRemainder ε n| +
        |subHalfZetaCoeff ε * (n : ℝ) ^ (1 - (ε : ℝ))| := abs_add_le _ _
    _ ≤ floorSumRate ((1 - (ε : ℝ) : ℝ) : ℂ) * (n : ℝ) ^ (1 - (ε : ℝ)) +
        |subHalfZetaCoeff ε| * (n : ℝ) ^ (1 - (ε : ℝ)) := by
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
      exact add_le_add (hR.trans (mul_le_mul_of_nonneg_left hp hK)) (le_refl _)
    _ = _ := by unfold forcingExpansionBudget; ring

/-- The positive forcing has the same upper power scale as its lower envelope. -/
theorem inversionDefect_le_power (ε : SubcriticalDamping) (n : ℕ) (hn : 1 ≤ n) :
    inversionDefect ε n ≤ (pmPowerDampedDivisorDensity (ε : ℝ)).re *
      forcingExpansionBudget ε * (n : ℝ) ^ (1 - (ε : ℝ)) := by
  have hm := (RHTower.pmPowerDampedDivisorDensity_re_pos ε.property.1).le
  rw [inversionDefect_eq_neg_density_mul_majorantCenteredPrefix ε.property.1]
  calc _ = (pmPowerDampedDivisorDensity (ε : ℝ)).re * (-majorantCenteredPrefix ε n) := by ring
    _ ≤ (pmPowerDampedDivisorDensity (ε : ℝ)).re * |majorantCenteredPrefix ε n| :=
      mul_le_mul_of_nonneg_left (neg_le_abs _) hm
    _ ≤ (pmPowerDampedDivisorDensity (ε : ℝ)).re *
        (forcingExpansionBudget ε * (n : ℝ) ^ (1 - (ε : ℝ))) :=
      mul_le_mul_of_nonneg_left (abs_majorantCenteredPrefix_le_power ε n hn) hm
    _ = _ := by ring

/-- The finite pronic L1 mass of the nonnegative complete forcing. -/
def forcingPronicMass (ε : ℝ) (T : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 T, inversionDefect ε n / ((n : ℝ) * ((n : ℝ) + 1))

theorem forcingPronicMass_nonneg (ε : SubcriticalDamping) (T : ℕ) :
    0 ≤ forcingPronicMass ε T :=
  sum_nonneg fun n _ => div_nonneg (inversionDefect_nonneg ε.property.1 n) (by positivity)

/-- The forcing's dual norm against bounded cell rows is bounded uniformly in the horizon. -/
theorem forcingPronicMass_le (ε : SubcriticalDamping) (T : ℕ) :
    forcingPronicMass ε T ≤ forcingExpansionBudget ε := by
  have hm := (RHTower.pmPowerDampedDivisorDensity_re_pos ε.property.1).le
  have hM := forcingExpansionBudget_nonneg ε
  have hcell : ∀ n ∈ Icc 1 T,
      inversionDefect ε n / ((n : ℝ) * ((n : ℝ) + 1)) ≤
        (pmPowerDampedDivisorDensity (ε : ℝ)).re * forcingExpansionBudget ε *
          (n : ℝ) ^ (-(1 + (ε : ℝ))) := by
    intro n hn
    have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hpow : (n : ℝ) ^ (1 - (ε : ℝ)) =
        (n : ℝ) ^ (-(1 + (ε : ℝ))) * (n : ℝ) * (n : ℝ) := by
      rw [← Real.rpow_add_one hn0.ne', ← Real.rpow_add_one hn0.ne']
      congr 1
      ring
    calc _ ≤ ((pmPowerDampedDivisorDensity (ε : ℝ)).re * forcingExpansionBudget ε *
          (n : ℝ) ^ (1 - (ε : ℝ))) / ((n : ℝ) * ((n : ℝ) + 1)) :=
        div_le_div_of_nonneg_right (inversionDefect_le_power ε n hn1) (by positivity)
      _ ≤ ((pmPowerDampedDivisorDensity (ε : ℝ)).re * forcingExpansionBudget ε *
          (n : ℝ) ^ (1 - (ε : ℝ))) / ((n : ℝ) * (n : ℝ)) :=
        div_le_div_of_nonneg_left
          (mul_nonneg (mul_nonneg hm hM) (Real.rpow_nonneg hn0.le _))
          (mul_pos hn0 hn0) (by nlinarith)
      _ = _ := by rw [hpow]; field_simp
  calc forcingPronicMass ε T ≤
        ∑ n ∈ Icc 1 T, (pmPowerDampedDivisorDensity (ε : ℝ)).re *
          forcingExpansionBudget ε * (n : ℝ) ^ (-(1 + (ε : ℝ))) := sum_le_sum hcell
    _ = (pmPowerDampedDivisorDensity (ε : ℝ)).re * forcingExpansionBudget ε *
        ∑ n ∈ Icc 1 T, (n : ℝ) ^ (-(1 + (ε : ℝ))) := by rw [mul_sum]
    _ ≤ (pmPowerDampedDivisorDensity (ε : ℝ)).re * forcingExpansionBudget ε *
        realZetaSeries (1 + (ε : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_Icc_rpow_le_realZetaSeries ε.property.1 T)
        (mul_nonneg hm hM)
    _ = forcingExpansionBudget ε := by
      rw [pmPowerDampedDivisorDensity_re_eq ε.property.1]
      have hZ : realZetaSeries (1 + (ε : ℝ)) ≠ 0 := (realZetaSeries_pos
        (by linarith [ε.property.1])).ne'
      field_simp

/-- The complete forcing mass is the positive prime-power logarithmic derivative. -/
def forcingMassLimit (ε : ℝ) : ℝ :=
  ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 + ε))

/-- The existing unit-row first moment identifies the forcing mass exactly. -/
theorem hasSum_forcingPronicMass (ε : SubcriticalDamping) :
    HasSum (fun n : ℕ => inversionDefect ε n / ((n : ℝ) * ((n : ℝ) + 1)))
      (forcingMassLimit ε) := by
  have hs := (hasSum_firstPronicMoment ε.property.1
    (unitSign_mem_dampedClass (ε : ℝ))).summable.hasSum
  change HasSum (fun n : ℕ => weightCenteredPrefix (dampedSignWeight unitSign ε)
    (∑' d : ℕ, dampedSignWeight unitSign ε d / d) n / ((n : ℝ) * ((n : ℝ) + 1)))
    (firstPronicMoment (dampedSignWeight unitSign ε)) at hs
  rw [firstPronicMoment_unitSign ε.property.1] at hs
  have hm := hs.mul_left (-(pmPowerDampedDivisorDensity (ε : ℝ)).re)
  have hvalue : -(pmPowerDampedDivisorDensity (ε : ℝ)).re *
      (-(∑' d : ℕ, dampedSignWeight unitSign ε d / d) * forcingMassLimit ε) =
      forcingMassLimit ε := by
    rw [unitWeightDensity_eq_realZetaSeries, pmPowerDampedDivisorDensity_re_eq ε.property.1]
    have hZ : realZetaSeries (1 + (ε : ℝ)) ≠ 0 :=
      (realZetaSeries_pos (by linarith [ε.property.1])).ne'
    field_simp
  change HasSum _ (-(pmPowerDampedDivisorDensity (ε : ℝ)).re *
    (-(∑' d : ℕ, dampedSignWeight unitSign ε d / d) * forcingMassLimit ε)) at hm
  rw [hvalue] at hm
  refine hm.congr_fun fun n => ?_
  rw [inversionDefect_eq_neg_density_mul_majorantCenteredPrefix ε.property.1,
    majorantCenteredPrefix_eq_unitReceiver]
  ring

/-- Every finite horizon is bounded by the exact prime-power mass. -/
theorem forcingPronicMass_le_limit (ε : SubcriticalDamping) (T : ℕ) :
    forcingPronicMass ε T ≤ forcingMassLimit ε := by
  have hs := hasSum_forcingPronicMass ε
  rw [← hs.tsum_eq]
  exact hs.summable.sum_le_tsum _ fun n _ =>
    div_nonneg (inversionDefect_nonneg ε.property.1 n) (by positivity)

/-- Increasing the horizon exhausts the exact forcing mass. -/
theorem tendsto_forcingPronicMass (ε : SubcriticalDamping) :
    Tendsto (forcingPronicMass ε) atTop (𝓝 (forcingMassLimit ε)) := by
  have h := (hasSum_forcingPronicMass ε).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  change Tendsto (fun T : ℕ => ∑ n ∈ range (T + 1),
    inversionDefect ε n / ((n : ℝ) * ((n : ℝ) + 1))) atTop (𝓝 (forcingMassLimit ε)) at h
  simpa only [dampedSign_sum_range_succ_eq_add_Icc, Nat.cast_zero,
    zero_mul, div_zero, zero_add, forcingPronicMass] using h

/-- The exact total mass is the least uniform bound for finite forcing masses. -/
theorem forcingMassLimit_isLUB (ε : SubcriticalDamping) :
    IsLUB (Set.range (forcingPronicMass ε)) (forcingMassLimit ε) := by
  refine ⟨?_, ?_⟩
  · rintro x ⟨T, rfl⟩
    exact forcingPronicMass_le_limit ε T
  · intro B hB
    exact le_of_tendsto' (tendsto_forcingPronicMass ε) fun T => hB (Set.mem_range_self T)

/-- The exact dual mass is bounded by the explicit power-expansion budget. -/
theorem forcingMassLimit_le_expansionBudget (ε : SubcriticalDamping) :
    forcingMassLimit ε ≤ forcingExpansionBudget ε :=
  le_of_tendsto' (tendsto_forcingPronicMass ε) (forcingPronicMass_le ε)

/-- The forcing's total pronic mass is `-ζ'(1+ε)/ζ(1+ε)`. -/
theorem forcingMassLimit_eq_logarithmicDerivative (ε : SubcriticalDamping) :
    forcingMassLimit ε =
      (-deriv riemannZeta ((1 + (ε : ℝ) : ℝ) : ℂ) /
        riemannZeta ((1 + (ε : ℝ) : ℝ) : ℂ)).re :=
  (hasSum_vonMangoldt_rpow' (by linarith [ε.property.1] : 1 < 1 + (ε : ℝ))).tsum_eq

end GaloisForLFunctions.ArithmeticDefectRigidity
