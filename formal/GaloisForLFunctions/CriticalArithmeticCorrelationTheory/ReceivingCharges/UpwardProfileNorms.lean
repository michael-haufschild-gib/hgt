import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ReceivingCharges.UpwardProfileNormalization
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCompleteWeilFormIsPositiveAtEveryFixedOverlap
import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.CompleteFormMoments

/-!
# Literal upward norm in reciprocal profile coordinates

The exact offset coefficient represents the upward vector itself. Its
physical square norm is the harmonic square of that coefficient divided
by the horizon logarithm; both finite cutoffs remain inside the coefficient.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open RenormalizedArithmeticPotentialTheory ArithmeticCouplingTheory

/-- The upward arithmetic operator preserves scalar multiplication exactly. -/
theorem upwardPrimeVector_smul (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) (r : ℝ)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    upwardPrimeVector φ c N (r • x) = r • upwardPrimeVector φ c N x := by
  have hext : ∀ j ∈ Icc 1 N,
      primeHorizonExtension (r • x) j = r * primeHorizonExtension x j := by
    intro j hj
    simp only [primeHorizonExtension, dif_pos hj]
    rfl
  ext n
  change upwardPrimeRow (atomDilate φ (c / N)) N (primeHorizonExtension (r • x)) n /
      (∫ u, atomDilate φ (c / N) u ^ 2) =
    r * (upwardPrimeRow (atomDilate φ (c / N)) N (primeHorizonExtension x) n /
      (∫ u, atomDilate φ (c / N) u ^ 2))
  rw [upwardPrimeRow_congr_smul hext]
  ring

/-- The finite logarithmic offset coefficient is the exact upward packet profile. -/
theorem upwardPrimeVector_packet_eq {φ : ℝ → ℝ}
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {c : ℝ} (hc : 0 < c)
    {N : ℕ} (hwidth : c / N ≤ 1) (F : ℕ → ℝ) :
    upwardPrimeVector φ c N (packetVector F N) =
      packetVector (logarithmicUpwardProfileCoefficient φ c (linearPrimeStrip c) N F) N := by
  have hext : ∀ j ∈ Icc 1 N,
      primeHorizonExtension (packetVector F N) j = 1 * (F j / Real.sqrt j) := by
    intro j hj
    simp only [primeHorizonExtension, dif_pos hj, one_mul]
    rfl
  ext n
  have hn : (0 : ℝ) < (n : ℕ) := by exact_mod_cast (mem_Icc.mp n.property).1
  have h := sqrt_mul_upwardProfileRow_eq_logarithmicCoefficient hsupp hc n.property hwidth F
  have hrow := upwardPrimeRow_congr_smul (g := atomDilate φ (c / N)) (n := (n : ℕ)) hext
  simp only [one_mul] at hrow
  rw [← hrow] at h
  change upwardPrimeRow (atomDilate φ (c / N)) N (primeHorizonExtension (packetVector F N)) n /
      (∫ u, atomDilate φ (c / N) u ^ 2) =
    logarithmicUpwardProfileCoefficient φ c (linearPrimeStrip c) N F n / Real.sqrt (n : ℕ)
  apply (eq_div_iff (Real.sqrt_pos.mpr hn).ne').mpr
  simpa only [mul_comm] using h

/-- The literal upward square norm is the harmonic square of its finite coefficient. -/
theorem upwardPrimeVector_packet_norm_sq {φ : ℝ → ℝ}
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {c : ℝ} (hc : 0 < c)
    {N : ℕ} (hwidth : c / N ≤ 1) (F : ℕ → ℝ) :
    ‖upwardPrimeVector φ c N (packetVector F N)‖ ^ 2 =
      ∑ n ∈ Icc 1 N, logarithmicUpwardProfileCoefficient φ c (linearPrimeStrip c) N F n ^ 2 /
        (n : ℝ) := by
  rw [upwardPrimeVector_packet_eq hsupp hc hwidth, packetVector_norm_sq]

/-- Physical normalization divides the exact upward harmonic square by `log N`. -/
theorem upwardPrimeVector_physical_packet_norm_sq {φ : ℝ → ℝ}
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {c : ℝ} (hc : 0 < c)
    {N : ℕ} (hwidth : c / N ≤ 1) (F : ℕ → ℝ) :
    ‖upwardPrimeVector φ c N ((Real.sqrt (Real.log N))⁻¹ • packetVector F N)‖ ^ 2 =
      (∑ n ∈ Icc 1 N, logarithmicUpwardProfileCoefficient φ c (linearPrimeStrip c) N F n ^ 2 /
        (n : ℝ)) / Real.log N := by
  rw [upwardPrimeVector_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inv_pow, Real.sq_sqrt (Real.log_natCast_nonneg N),
    upwardPrimeVector_packet_norm_sq hsupp hc hwidth]
  ring

#print axioms upwardPrimeVector_packet_eq
#print axioms upwardPrimeVector_physical_packet_norm_sq

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
