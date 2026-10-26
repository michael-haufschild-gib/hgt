import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.LongModulusIntegrableProducer
import GaloisForLFunctions.BezoutValuationIncidence.HyperbolaCancellationWithDivisorBoundedCoefficients

/-!
# Exact integer sampling of the Möbius quadrature function

Positive integer samples count the exact hyperbola incidences. Reversing that
finite sum gives the long divisor floor sum with its entire harmonic tail.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
set_option autoImplicit false

/-- Integer sampling preserves the exact natural quotient cutoff. -/
theorem pmLongModulusFunction_natCast (ε : ℝ) (n D j : ℕ) :
    pmLongModulusFunction ε n D j =
      ∑ d ∈ Finset.Ioc D (n / j), pmLongModulusWeight ε d := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [pmLongModulusFunction]
  · have hjR : (0 : ℝ) < j := by exact_mod_cast hj
    rw [pmLongModulusFunction, if_pos hjR, Nat.floor_div_eq_div]

/-- All positive integer samples beyond the numerator vanish exactly. -/
theorem pmLongModulusFunction_natCast_eq_zero (ε : ℝ) (n D : ℕ) {j : ℕ} (hj : n < j) :
    pmLongModulusFunction ε n D j = 0 := by
  rw [pmLongModulusFunction_natCast, Nat.div_eq_of_lt hj]
  simp

/-- The complete positive-integer sample sum is the exact long-modulus floor sum. -/
theorem tsum_pmLongModulusFunction_natCast_succ (ε : ℝ) (n D : ℕ) :
    (∑' j : ℕ, pmLongModulusFunction ε n D ((j + 1 : ℕ) : ℝ)) =
      ∑ d ∈ Finset.Ioc D n, pmLongModulusWeight ε d * ((n / d : ℕ) : ℝ) := by
  rw [tsum_eq_sum (s := Finset.range n) (fun j hj =>
    pmLongModulusFunction_natCast_eq_zero ε n D (by
      simp only [Finset.mem_range] at hj
      omega))]
  have hshift : (∑ j ∈ Finset.range n, pmLongModulusFunction ε n D ((j + 1 : ℕ) : ℝ)) =
      ∑ j ∈ Finset.Icc 1 n, pmLongModulusFunction ε n D j := by
    apply Finset.sum_bij (fun j _ => j + 1)
    · intro j hj
      simp only [Finset.mem_range] at hj
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro j hj k hk h
      omega
    · intro j hj
      obtain ⟨hj1, hjn⟩ := Finset.mem_Icc.mp hj
      exact ⟨j - 1, Finset.mem_range.mpr (by omega), by omega⟩
    · intro j hj
      rfl
  rw [hshift]
  simp_rw [pmLongModulusFunction_natCast]
  exact (BezoutValuationIncidence.sum_Ioc_mul_natDiv_eq_sum_Icc_Ioc
    (pmLongModulusWeight ε) D n).symm

/-- The actual quadrature error includes the full signed harmonic tail. -/
def pmLongModulusQuadrature (ε : ℝ) (n D : ℕ) : ℝ :=
  (∑' j : ℕ, pmLongModulusFunction ε n D ((j + 1 : ℕ) : ℝ)) -
    ∫ u, pmLongModulusFunction ε n D u

/-- Exact equality for every natural cutoff, before taking any absolute values. -/
theorem pmLongModulusQuadrature_eq {ε : ℝ} (hε : 0 < ε) (n D : ℕ) :
    pmLongModulusQuadrature ε n D =
      (∑ d ∈ Finset.Ioc D n, pmLongModulusWeight ε d * ((n / d : ℕ) : ℝ)) -
        (n : ℝ) * ∑' d : ℕ, if D < d then pmLongModulusWeight ε d / d else 0 := by
  rw [pmLongModulusQuadrature, tsum_pmLongModulusFunction_natCast_succ,
    integral_pmLongModulusFunction hε]

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
