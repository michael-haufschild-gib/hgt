import GaloisForLFunctions.HTGeometry.Thermofield.GibbsKMSOverlap
import GaloisForLFunctions.HTGeometry.PrimeLogKMSRealization

/-!
# Arithmetic susceptibility of the prime-log KMS model

For a prime logarithm, the single-gap susceptibility is
`(p²-1)/(log p * (p²+1))`. The vacuum-plus-prime Gibbs model therefore has
an explicit arithmetic susceptibility and inherits the sharp KMS overlap bound.
-/

noncomputable section
open MeasureTheory intervalIntegral
open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry.Thermofield
open _root_.HTGeometry

/-- Single-gap susceptibility at a prime logarithm is an elementary arithmetic ratio. -/
theorem kmsMean_primeLog (p : Nat.Primes) :
    kmsMean (primeLogSupport p) =
      ((p : ℕ)^2-1 : ℝ) / (Real.log (p : ℕ) * ((p : ℕ)^2+1)) := by
  have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.pos
  have hl : Real.log (p : ℕ) ≠ 0 := (primeLogSupport_pos p).ne'
  have hd : ((p : ℕ)^2+1 : ℝ) ≠ 0 := by positivity
  rw [kmsMean, if_neg (primeLogSupport_pos p).ne', primeLogSupport,
    Real.sinh_eq, Real.cosh_eq]
  simp only [Real.exp_neg, Real.exp_log hp]
  field_simp [hp.ne', hl, hd] <;> ring

/-- Explicit susceptibility including the vacuum contribution. -/
def primeLogKMSSusceptibility (P : Finset Nat.Primes) (β : ℝ) : ℝ :=
  (1 + ∑ p : P, Real.exp (-β * primeLogSupport p.1) *
    (((p.1 : ℕ)^2-1 : ℝ) / (Real.log (p.1 : ℕ) * ((p.1 : ℕ)^2+1)))) /
    (1 + ∑ p : P, Real.exp (-β * primeLogSupport p.1))

/-- Reading every gap of the existing multiplicative Hamiltonian gives the arithmetic ratio. -/
theorem gibbsKMSSusceptibility_primeLog (P : Finset Nat.Primes) (β : ℝ) :
    gibbsKMSSusceptibility β (primeLogKMSFiniteEnergy P) (primeLogKMSFiniteEnergy P) =
      primeLogKMSSusceptibility P β := by
  have hZ : finiteGibbsPartition β (primeLogKMSFiniteEnergy P) =
      1 + ∑ p : P, Real.exp (-β * primeLogSupport p.1) := by
    rw [finiteGibbsPartition, Fintype.sum_option]
    simp only [primeLogKMSFiniteEnergy, mul_zero, Real.exp_zero]
  unfold gibbsKMSSusceptibility finiteGibbsStateWeight
  rw [Fintype.sum_option]
  simp only [primeLogKMSFiniteEnergy, mul_zero, Real.exp_zero,
    show kmsMean 0 = 1 by simp [kmsMean], mul_one, kmsMean_primeLog]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, ← add_div, hZ]
  rfl

/-- Arithmetic form of the sharp integrated square bound for the prime-log Hamiltonian. -/
theorem primeLogKMS_overlap_bound (P : Finset Nat.Primes) (β : ℝ) :
    (∫ u in (0:ℝ)..1,
      gibbsKMSAutocorrelation β (primeLogKMSFiniteEnergy P) (primeLogKMSFiniteEnergy P) u ^ 2) ≤
      (primeLogKMSSusceptibility P β + primeLogKMSSusceptibility P β ^ 2) / 2 := by
  have h := integral_gibbsKMSAutocorrelation_sq_le β
    (primeLogKMSFiniteEnergy P) (primeLogKMSFiniteEnergy P)
  rw [gibbsKMSSusceptibility_primeLog] at h
  convert h using 1 <;> ring

end GaloisForLFunctions.HTGeometry.Thermofield
