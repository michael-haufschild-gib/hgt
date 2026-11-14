import GaloisForLFunctions.HTGeometry.Thermofield.TwoCopyDynamics
import GaloisForLFunctions.HTGeometry.Thermofield.ThermalReturnPlateau
import GaloisForLFunctions.HTGeometry.PrimeLogKMSRealization

/-!
# Thermofield realizations of the prime-log carrier

The corpus vacuum-plus-prime Hamiltonian has distinct energies. Its thermal
return plateau therefore equals Gibbs purity exactly. The previously constructed
KMS-normalized prime observable has a two-copy correlation equal to the weighted
prime-log exponential sum, at every inverse temperature.

These are applications of the thermofield and discrete-spectrum mechanisms of
Maldacena, arXiv:hep-th/0106112, to the existing arithmetic response model.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry.Thermofield

open _root_.HTGeometry

noncomputable section

/-- Vacuum energy zero and the positive prime logarithms are all distinct. -/
theorem primeLog_energy_injective (P : Finset Nat.Primes) :
    Function.Injective (primeLogKMSFiniteEnergy P) := by
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some q =>
      exact False.elim ((primeLogSupport_pos q.1).ne' h.symm)
  | some p =>
    cases b with
    | none => exact False.elim ((primeLogSupport_pos p.1).ne' h)
    | some q =>
      have hpq : p = q := Subtype.ext (primeLogSupport_linearIndependent.injective h)
      exact congrArg some hpq

/-- The arithmetic model attains the exact thermal replica floor. -/
theorem primeLog_returnPlateau (P : Finset Nat.Primes) (β : ℝ) :
    returnPlateau β (primeLogKMSFiniteEnergy P) =
      finiteGibbsPartition (2 * β) (primeLogKMSFiniteEnergy P) /
        finiteGibbsPartition β (primeLogKMSFiniteEnergy P) ^ 2 := by
  rw [← finiteGibbsPurity_eq_partitionRatio]
  exact (returnPlateau_eq_purity_iff _ _).mpr (primeLog_energy_injective P)

/-- At infinite temperature the exact return mass is inverse vacuum-plus-prime dimension. -/
theorem primeLog_returnPlateau_zero (P : Finset Nat.Primes) :
    returnPlateau 0 (primeLogKMSFiniteEnergy P) = 1 / ((P.card : ℝ) + 1) := by
  rw [(returnPlateau_eq_purity_iff _ _).mpr (primeLog_energy_injective P),
    finiteGibbsPurity_zero]
  simp

/-- The actual entangled-state expectation realizes the weighted prime-log
phase sum. Temperature cancels because the observable has the corpus KMS normalization. -/
theorem primeLog_twoCopy_correlation (P : Finset Nat.Primes)
    (u : Nat.Primes → ℝ) (β : ℝ) (z w : ℂ) :
    pairExpectation (amplitude β (primeLogKMSFiniteEnergy P))
        (evolve (primeLogKMSFiniteEnergy P) z (primeLogKMSFiniteAmplitude P u β))
        (evolve (primeLogKMSFiniteEnergy P) w
          (fun a b => star (primeLogKMSFiniteAmplitude P u β a b))) =
      ∑ p : P, (primeDyadicWeight u p.1 : ℂ) *
        Complex.exp (Complex.I * (z + w) * (primeLogSupport p.1 : ℂ)) := by
  rw [expectation_evolved_conjugate]
  simp_rw [finiteKMSWightmanTransitionIntensity_primeLogKMSFiniteAmplitude]
  rw [Fintype.sum_option]
  simp_rw [Fintype.sum_option]
  simp only [primeLogKMSFiniteIntensity, primeLogKMSFiniteEnergy,
    Complex.ofReal_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, sub_zero]

/-- Opposite time translations preserve the entire prime-log carrier expectation. -/
theorem primeLog_opposite_times (P : Finset Nat.Primes)
    (u : Nat.Primes → ℝ) (β : ℝ) (z : ℂ) :
    pairExpectation (amplitude β (primeLogKMSFiniteEnergy P))
        (evolve (primeLogKMSFiniteEnergy P) z (primeLogKMSFiniteAmplitude P u β))
        (evolve (primeLogKMSFiniteEnergy P) (-z)
          (fun a b => star (primeLogKMSFiniteAmplitude P u β a b))) =
      ∑ p : P, (primeDyadicWeight u p.1 : ℂ) := by
  rw [primeLog_twoCopy_correlation]
  simp only [add_neg_cancel, mul_zero, zero_mul, Complex.exp_zero, mul_one]

end

end GaloisForLFunctions.HTGeometry.Thermofield
