import GaloisForLFunctions.ArithmeticDefectRigidity.FixedSuccessorsDisappearFromEscapingProfiles
import GaloisForLFunctions.TransHorizonIncidenceMechanics.SubHalfDampingPartialPoleSumsAndLogarithmicMomentIndexLaws

/-!
# A paid power subtraction for the complete forcing

The smooth-power prefix expansion identifies the forcing's positive leading power explicitly.
After subtracting that power, its pronic norm is uniformly bounded. The exact inversion law
therefore becomes a homogeneous relation in receiver normalization on the escaping branch.

The subtracted cofactor expression is an affine residual of the actual source. This result
does not assert a bounded or coercive operator on arbitrary rows.
-/

open Finset Filter Topology RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticCompensationTheory
open GaloisForLFunctions.TransHorizonIncidenceMechanics
  (dampedSignWeight unitSign summable_unit_weight dampedSignWeight_div weightCenteredPrefix
   subHalfZetaCoeff subHalfZetaCoeff_neg subHalfRemainder subHalfDilationRemainder
   abs_subHalfRemainder_le pronicNorm_subHalfDilationRemainder_le floorSumRate)

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- The unit-row density in the smooth-power expansion is the real zeta series. -/
theorem unitWeightDensity_eq_realZetaSeries (ε : SubcriticalDamping) :
    (∑' d : ℕ, dampedSignWeight unitSign ε d / d) = realZetaSeries (1 + (ε : ℝ)) := by
  have hsplit := (summable_unit_weight ε.property.1).sum_add_tsum_nat_add 1
  have htail : (∑' d : ℕ, dampedSignWeight unitSign ε (d + 1) / (d + 1 : ℕ)) =
      realZetaSeries (1 + (ε : ℝ)) := by
    unfold realZetaSeries
    apply tsum_congr
    intro d
    rw [dampedSignWeight_div ε.property.1, unitSign, mul_one]
    simp only [Nat.cast_add, Nat.cast_one]
  simpa only [sum_range_one, Nat.cast_zero, div_zero, zero_add, htail] using hsplit.symm

/-- The unsigned centered prefix is exactly the existing smooth-power receiver. -/
theorem majorantCenteredPrefix_eq_unitReceiver (ε : SubcriticalDamping) (n : ℕ) :
    majorantCenteredPrefix ε n =
      weightCenteredPrefix (dampedSignWeight unitSign ε)
        (∑' d : ℕ, dampedSignWeight unitSign ε d / d) n := by
  rw [unitWeightDensity_eq_realZetaSeries]
  unfold weightCenteredPrefix
  rw [sum_Icc_sum_divisors_eq_floor]
  simp only [majorantCenteredPrefix, dampedSignWeight, unitSign, one_mul]
  ring

/-- The positive coefficient of the forcing's leading power. -/
def forcingPowerCoefficient (ε : ℝ) : ℝ :=
  -(pmPowerDampedDivisorDensity ε).re * subHalfZetaCoeff ε

theorem forcingPowerCoefficient_pos (ε : SubcriticalDamping) :
    0 < forcingPowerCoefficient ε := by
  have hm := RHTower.pmPowerDampedDivisorDensity_re_pos ε.property.1
  have hz := subHalfZetaCoeff_neg ε.property.1 (by linarith [ε.property.2])
  unfold forcingPowerCoefficient
  nlinarith

/-- The explicit power carrying the forcing's unbounded pronic energy. -/
def forcingPower (ε : ℝ) (n : ℕ) : ℝ :=
  forcingPowerCoefficient ε * (n : ℝ) ^ (1 - ε)

/-- The forcing after its explicit smooth-power boundary term has been subtracted. -/
def forcingRemainder (ε : ℝ) (n : ℕ) : ℝ :=
  inversionDefect ε n - forcingPower ε n

/-- Exact identification with the already established smooth-power remainder. -/
theorem forcingRemainder_eq (ε : SubcriticalDamping) (n : ℕ) :
    forcingRemainder ε n = -(pmPowerDampedDivisorDensity (ε : ℝ)).re *
      subHalfRemainder ε n := by
  rw [forcingRemainder, inversionDefect_eq_neg_density_mul_majorantCenteredPrefix ε.property.1,
    majorantCenteredPrefix_eq_unitReceiver]
  unfold forcingPower forcingPowerCoefficient subHalfRemainder
  ring

/-- The explicit constant controlling the power expansion and its pronic remainder. -/
def forcingExpansionBudget (ε : ℝ) : ℝ :=
  floorSumRate ((1 - ε : ℝ) : ℂ) + |subHalfZetaCoeff ε|

theorem forcingExpansionBudget_nonneg (ε : SubcriticalDamping) :
    0 ≤ forcingExpansionBudget ε := by
  have h := abs_subHalfRemainder_le ε.property.1 (by linarith [ε.property.2]) 1
  simp only [Nat.cast_one, Real.sqrt_one, Real.one_rpow, mul_one] at h
  exact add_nonneg ((abs_nonneg _).trans h) (abs_nonneg _)

/-- A uniform norm budget for the complete power-subtracted forcing. -/
def forcingRemainderBudget (ε : ℝ) : ℝ :=
  (pmPowerDampedDivisorDensity ε).re * Real.sqrt (1 + 1 / ε) * forcingExpansionBudget ε

theorem forcingRemainderBudget_nonneg (ε : SubcriticalDamping) :
    0 ≤ forcingRemainderBudget ε :=
  mul_nonneg (mul_nonneg (RHTower.pmPowerDampedDivisorDensity_re_pos ε.property.1).le
    (Real.sqrt_nonneg _)) (forcingExpansionBudget_nonneg ε)

/-- The forcing remainder is globally paid, with no admission assumption on the receiver. -/
theorem pronicNorm_forcingRemainder_le (ε : SubcriticalDamping) (T : ℕ) :
    pronicNorm T (forcingRemainder ε) ≤ forcingRemainderBudget ε := by
  have hR := pronicNorm_subHalfDilationRemainder_le ε.property.1
    (by linarith [ε.property.2]) (j := 1) (by omega) T
  simp only [Nat.cast_one, Real.one_rpow, mul_one] at hR
  have hnorm : pronicNorm T (subHalfRemainder ε) =
      GaloisForLFunctions.TransHorizonIncidenceMechanics.pronicNorm
        (fun n => if 1 ≤ n then subHalfDilationRemainder ε n 1 else 0) T := by
    change pronicNorm T (subHalfRemainder ε) = pronicNorm T _
    apply pronicNorm_congr
    intro n hn
    rw [if_pos (mem_Icc.mp hn).1]
    simp only [subHalfDilationRemainder, Nat.div_one, Nat.cast_one, Real.one_rpow,
      mul_one, sub_self, mul_zero, sub_zero]
  have hfun : forcingRemainder ε = fun n =>
      -((pmPowerDampedDivisorDensity (ε : ℝ)).re * subHalfRemainder ε n) := by
    funext n
    rw [forcingRemainder_eq]
    ring
  rw [hfun, pronicNorm_neg,
    pronicNorm_const_mul (RHTower.pmPowerDampedDivisorDensity_re_pos ε.property.1).le, hnorm]
  simpa only [forcingRemainderBudget, forcingExpansionBudget, mul_assoc] using
    mul_le_mul_of_nonneg_left hR (RHTower.pmPowerDampedDivisorDensity_re_pos ε.property.1).le

/-- A horizon-independent squared-energy budget for the complete remainder. -/
theorem forcingRemainderEnergy_le (ε : SubcriticalDamping) (T : ℕ) :
    pronicNorm T (forcingRemainder ε) ^ 2 ≤ forcingRemainderBudget ε ^ 2 :=
  pow_le_pow_left₀ (pronicNorm_nonneg T _) (pronicNorm_forcingRemainder_le ε T) 2

/-- The actual proper cofactor sum with its explicit boundary power removed. -/
def renormalizedCofactor (ε : ℝ) (n : ℕ) : ℝ :=
  offDiagonalUnitDilation ε n - forcingPower ε n

/-- The residual inversion equation retains the full finite-cell forcing remainder. -/
theorem receiver_add_renormalizedCofactor_eq (ε : SubcriticalDamping) (n : ℕ) :
    pmPowerDampedCenteredDivisorPrefix ε (n + 1) + renormalizedCofactor ε (n + 1) =
      forcingRemainder ε (n + 1) := by
  rw [forcingRemainder, renormalizedCofactor,
    inversionDefect_eq_centeredPrefix_add_offDiagonal ε (by omega)]
  ring

/-- The paid subtraction is valid in the global pronic norm, including moving cells. -/
theorem pronicNorm_receiver_add_renormalizedCofactor_le (ε : SubcriticalDamping) (T : ℕ) :
    pronicNorm T (fun n => pmPowerDampedCenteredDivisorPrefix ε n +
      renormalizedCofactor ε n) ≤ forcingRemainderBudget ε := by
  have heq : pronicNorm T (fun n => pmPowerDampedCenteredDivisorPrefix ε n +
      renormalizedCofactor ε n) = pronicNorm T (forcingRemainder ε) := by
    apply pronicNorm_congr
    intro n hn
    cases n with
    | zero => simp only [mem_Icc] at hn; omega
    | succ n => exact receiver_add_renormalizedCofactor_eq ε n
  rw [heq]
  exact pronicNorm_forcingRemainder_le ε T

/-- On escape the residual cofactor relation is homogeneous in the global receiver norm. -/
theorem admits_or_renormalized_inversion_is_homogeneous (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨
      Tendsto (fun T => pronicNorm T (fun n => pmPowerDampedCenteredDivisorPrefix ε n +
        renormalizedCofactor ε n) ^ 2 / dampedMobiusEnergy ε T) atTop (𝓝 0) := by
  rcases admits_or_tendsto_atTop (ε : ℝ) with h | hE
  · exact Or.inl h
  · refine Or.inr (squeeze_zero
      (fun T => div_nonneg (sq_nonneg _) (dampedMobiusEnergy_nonneg ε T))
      (fun T => div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (pronicNorm_nonneg T _)
          (pronicNorm_receiver_add_renormalizedCofactor_le ε T) 2)
        (dampedMobiusEnergy_nonneg ε T)) ?_)
    exact tendsto_const_nhds.div_atTop hE

end GaloisForLFunctions.ArithmeticDefectRigidity
