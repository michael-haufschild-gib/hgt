import GaloisForLFunctions.HTGeometry.CPVThermalRadiation
import Mathlib

/-!
# Thermal-pair interpretation of the corpus prime occupation law

The radiation distribution in arXiv:2601.07437 becomes the literal prime
valuation distribution at inverse thermal scale `log p`. Every finite-prime
Wold occupation law is therefore a product of these one-mode radiation laws.
The bridge is an exact identity of probabilities; it assigns no gravitational
meaning to arithmetic primes.
-/
noncomputable section
namespace GaloisForLFunctions.HTGeometry.CPV
open scoped BigOperators

/-- Logarithmic thermal parameter realizing the prime ratio `1/p`. -/
def primeThermalCoordinate (p : Nat.Primes) : ℝ := Real.log (Real.log (p : ℝ))

/-- Every prime is an interior, nonvacuum thermal state. -/
theorem thermalRatio_prime (p : Nat.Primes) :
    thermalRatio (primeThermalCoordinate p) = (p : ℝ)⁻¹ := by
  have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
  have hp1 : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.one_lt
  unfold thermalRatio primeThermalCoordinate
  rw [Real.exp_log (Real.log_pos hp1), Real.exp_neg, Real.exp_log hp]

/-- Exact local prime valuation mass, in the notation used by Wold thermofields. -/
theorem radiationMass_prime (p : Nat.Primes) (n : ℕ) :
    radiationMass (primeThermalCoordinate p) n =
      (1 - (p : ℝ)⁻¹) * (p : ℝ) ^ (-(n : ℤ)) := by
  unfold radiationMass canonicalThermalMass
  rw [thermalRatio_prime]
  simp

/-- Every finite set of prime occupation factors is a product radiation state. -/
theorem finitePrimeWeight_eq_radiationProduct (S : Finset Nat.Primes) (nu : S → ℕ) :
    finitePrimeOccupationProbabilityWeight S nu =
      ∏ p : S, radiationMass (primeThermalCoordinate (p : Nat.Primes)) (nu p) := by
  unfold finitePrimeOccupationProbabilityWeight
  apply Finset.prod_congr rfl
  intro p _
  exact (radiationMass_prime (p : Nat.Primes) (nu p)).symm

/-- The existing finite-prime ratio field is precisely the assigned thermal field. -/
theorem finitePrimeRatio_eq_thermal (S : Finset Nat.Primes) (p : S) :
    finitePrimeOccupationRatio S p = thermalRatio (primeThermalCoordinate (p : Nat.Primes)) := by
  rw [thermalRatio_prime]
  rfl

/-- Prime valuation expectation is the bosonic occupation number `1/(p-1)`. -/
theorem primeRadiation_mean (p : Nat.Primes) :
    (∑' n : ℕ, (n : ℝ) * radiationMass (primeThermalCoordinate p) n) = 1 / ((p : ℝ) - 1) := by
  rw [(radiationMass_mean _).tsum_eq, thermalRatio_prime]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  field_simp

/-- Exact purity of each arithmetic radiation mode. -/
theorem primeRadiation_purity (p : Nat.Primes) :
    (∑' n, radiationMass (primeThermalCoordinate p) n ^ 2) =
      ((p : ℝ) - 1) / ((p : ℝ) + 1) := by
  rw [radiationMass_purity, thermalRatio_prime]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hp1 : (p : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- Prime radiation linear entropy is the rational quantity `2/(p+1)`. -/
theorem primeRadiation_linearEntropy (p : Nat.Primes) :
    1 - (∑' n, radiationMass (primeThermalCoordinate p) n ^ 2) = 2 / ((p : ℝ) + 1) := by
  rw [primeRadiation_purity]
  have hp1 : (p : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- Every prime mode has an entangled two-mode purification in the actual corpus Hilbert space. -/
theorem primeRadiation_entangled (p : Nat.Primes) :
    ¬ ∃ f g : ℕ → ℂ, ∀ i j, radiationPair (primeThermalCoordinate p) (i, j) = f i * g j :=
  radiationPair_not_product _

/-- The depth-shift telescoping law becomes the emitted Bose mean occupation. -/
theorem primeDepthMean_difference (p : Nat.Primes) :
    (∑' j, modeMean ((p : ℝ)⁻¹) j) - (∑' j, modeMean ((p : ℝ)⁻¹) (j + 1)) =
      ∑' n : ℕ, (n : ℝ) * radiationMass (primeThermalCoordinate p) n := by
  rw [← thermalRatio_prime p, tsum_modeMean_sub_shift
    (thermalRatio_pos _).le (thermalRatio_lt_one _), (radiationMass_mean _).tsum_eq]
  simp [modeMean]

end GaloisForLFunctions.HTGeometry.CPV
