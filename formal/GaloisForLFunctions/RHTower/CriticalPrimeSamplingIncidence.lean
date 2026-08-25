import GaloisForLFunctions.HTGeometry.CompactAdjoint
import GaloisForLFunctions.HTGeometry.DiagonalEllTwoIndexed
import GaloisForLFunctions.RHTower.BurnolPrimeLogSummability
import GaloisForLFunctions.RHTower.TraceClassCompressionCurvature

/-!
# Critical-prime normalized sampling endpoints

Generic operator consequences shared by polynomial and rapid Fock carriers.
-/

open scoped InnerProductSpace

namespace RHTower

noncomputable section

open ContinuousLinearMap

/-- Critical prime weight used by every normalized sampling carrier. -/
def criticalPrimeSamplingWeight (p : Nat.Primes) : ℝ :=
  Real.log (p : ℝ) ^ 2 / (p : ℝ)

theorem criticalPrimeSamplingWeight_pos (p : Nat.Primes) :
    0 < criticalPrimeSamplingWeight p := by
  rw [criticalPrimeSamplingWeight]
  exact div_pos (sq_pos_of_pos (Real.log_pos (by exact_mod_cast p.2.two_le)))
    (by exact_mod_cast p.2.pos)

/-- The normalized coordinate masses have infinite Hilbert--Schmidt energy. -/
theorem criticalPrimeSamplingWeight_not_summable :
    ¬ Summable criticalPrimeSamplingWeight := by
  intro hsum
  have hc : 0 < Real.log (2 : ℝ) ^ 2 :=
    sq_pos_of_pos (Real.log_pos (by norm_num))
  have hscaled : Summable (fun p : Nat.Primes =>
      Real.log (2 : ℝ) ^ 2 * (1 / (p : ℝ))) := by
    refine Summable.of_nonneg_of_le (fun p => mul_nonneg hc.le (by positivity)) ?_ hsum
    intro p
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.two_le
    have hlog : Real.log (2 : ℝ) ≤ Real.log (p : ℝ) := Real.log_le_log (by norm_num) hp2
    have hlog2 : 0 ≤ Real.log (2 : ℝ) := (Real.log_pos (by norm_num)).le
    have hsq : Real.log (2 : ℝ) ^ 2 ≤ Real.log (p : ℝ) ^ 2 := by
      nlinarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ (p : ℝ))]
    simpa [criticalPrimeSamplingWeight, one_div, div_eq_mul_inv] using
      (mul_le_mul_of_nonneg_right hsq (show 0 ≤ ((p : ℝ)⁻¹) by positivity))
  exact burnolNotSummable_prime_one_div
    ((summable_mul_left_iff hc.ne').mp hscaled)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev CriticalPrimeEllTwo := HTGeometry.IndexedEllTwo Nat.Primes

/-- Positive Gram incidence associated with a normalized all-prime sampling map. -/
def criticalPrimeSamplingIncidence (S : H →L[ℂ] CriticalPrimeEllTwo) : H →L[ℂ] H :=
  adjoint S ∘L S

theorem criticalPrimeSamplingIncidence_isPositive
    (S : H →L[ℂ] CriticalPrimeEllTwo) :
    (criticalPrimeSamplingIncidence S).IsPositive := by
  simpa [criticalPrimeSamplingIncidence] using isPositive_adjoint_comp_self S

/-- Compact sampling gives compact positive incidence. -/
theorem criticalPrimeSamplingIncidence_isCompactOperator
    {S : H →L[ℂ] CriticalPrimeEllTwo} (hS : IsCompactOperator S) :
    IsCompactOperator (criticalPrimeSamplingIncidence S) := by
  rw [criticalPrimeSamplingIncidence]
  exact hS.clm_comp (adjoint S)

/-- A normalized sampler with the literal critical prime coordinate norms cannot be
Hilbert--Schmidt. -/
theorem not_isHilbertSchmidt_of_adjoint_coordinate_normSq_eq_criticalPrimeSamplingWeight
    (S : H →L[ℂ] CriticalPrimeEllTwo)
    (hcoord : ∀ p : Nat.Primes,
      ‖adjoint S (HTGeometry.ellTwoCoordinateBasis Nat.Primes p)‖ ^ 2 =
        criticalPrimeSamplingWeight p) :
    ¬ S.IsHilbertSchmidt := by
  intro hS
  have hAdj : (adjoint S).IsHilbertSchmidt := hS.adjoint
  have hsum : Summable (fun p : Nat.Primes =>
      ‖adjoint S (HTGeometry.ellTwoCoordinateBasis Nat.Primes p)‖ ^ 2) :=
    hAdj.summable (HTGeometry.ellTwoCoordinateBasis Nat.Primes)
  exact criticalPrimeSamplingWeight_not_summable
    (hsum.congr fun p => hcoord p)

/-- Rectangular positive-Gram converse: Schatten-one membership of `S†S` forces `S` to be
Hilbert--Schmidt. -/
theorem isHilbertSchmidt_of_adjoint_comp_self_memSchattenClass_one
    (S : H →L[ℂ] CriticalPrimeEllTwo)
    (hT : MemSchattenClass 1 (adjoint S ∘L S)) :
    S.IsHilbertSchmidt := by
  have hdiag := hT.one_summable_inner_diag
  refine isHilbertSchmidt_of_summable (hsBasis ℂ H) ?_
  rw [← RCLike.summable_ofReal (𝕜 := ℂ)]
  refine hdiag.congr fun i => ?_
  rw [ContinuousLinearMap.comp_apply, adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

/-- The critical normalized incidence is never trace class. -/
theorem criticalPrimeSamplingIncidence_not_memSchattenClass_one
    (S : H →L[ℂ] CriticalPrimeEllTwo)
    (hcoord : ∀ p : Nat.Primes,
      ‖adjoint S (HTGeometry.ellTwoCoordinateBasis Nat.Primes p)‖ ^ 2 =
        criticalPrimeSamplingWeight p) :
    ¬ MemSchattenClass 1 (criticalPrimeSamplingIncidence S) := by
  intro hT
  apply not_isHilbertSchmidt_of_adjoint_coordinate_normSq_eq_criticalPrimeSamplingWeight S hcoord
  apply isHilbertSchmidt_of_adjoint_comp_self_memSchattenClass_one S
  simpa [criticalPrimeSamplingIncidence] using hT

end

end RHTower
