import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheArithmeticCurvatureHasAnExactGramCompletion
import GaloisForLFunctions.BezoutValuationIncidence.SelbergSupportExactRecurrenceComplexity

/-!
# The radical of the arithmetic overlap Gram form

A finite prefix packet has zero completed energy exactly when its
polynomial is divisible by the conductor's cyclotomic polynomial.
For several conductors, the radical is the intersection of these exact
divisibility conditions. Positivity of individual prefixes therefore
does not imply coercivity on arbitrary coefficient packets.
-/

noncomputable section

open Finset Polynomial
open scoped Classical

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

/-- The polynomial whose primitive values are the weighted prefix packet. -/
def primitivePrefixPolynomial {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (k : ι → ℕ) : ℝ[X] :=
  ∑ i ∈ s, C (a i) * ∑ j ∈ range (k i), X ^ j

theorem aeval_primitivePrefixPolynomial {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (k : ι → ℕ) (ζ : ℂ) :
    aeval ζ (primitivePrefixPolynomial s a k) =
      ∑ i ∈ s, a i • primitivePrefixValue ζ (k i) := by
  simp only [primitivePrefixPolynomial, map_sum, map_mul, map_pow, aeval_C,
    aeval_X, primitivePrefixValue, Algebra.smul_def]

/-- All primitive values, rather than their separate magnitudes, determine
the radical of the full mixed form. -/
theorem primitivePrefixGram_quadratic_eq_zero_iff {ι : Type*} (s : Finset ι)
    {m : ℕ} (hm : 0 < m) (a : ι → ℝ) (k : ι → ℕ) :
    (∑ i ∈ s, ∑ j ∈ s, a i * a j * primitivePrefixGram m (k i) (k j)) = 0 ↔
      ∀ ζ : ℂ, IsPrimitiveRoot ζ m →
        ∑ i ∈ s, a i • primitivePrefixValue ζ (k i) = 0 := by
  rw [primitivePrefixGram_quadratic_eq s hm]
  constructor
  · intro h ζ hζ
    have hb := single_le_sum
      (fun ξ (_ : ξ ∈ primitiveRoots m ℂ) =>
        sq_nonneg ‖∑ i ∈ s, a i • primitivePrefixValue ξ (k i)‖)
      ((mem_primitiveRoots hm).mpr hζ)
    rw [h] at hb
    have hz : ‖∑ i ∈ s, a i • primitivePrefixValue ζ (k i)‖ ^ 2 = 0 :=
      le_antisymm hb (sq_nonneg _)
    simpa only [sq_eq_zero_iff, norm_eq_zero] using hz
  · intro h
    exact sum_eq_zero fun ζ hζ => by
      rw [h ζ ((mem_primitiveRoots hm).mp hζ), norm_zero, zero_pow two_ne_zero]

/-- The exact algebraic radical: the packet vanishes precisely in the
cyclotomic ideal of its conductor. -/
theorem primitivePrefixGram_quadratic_eq_zero_iff_cyclotomic_dvd {ι : Type*}
    (s : Finset ι) {m : ℕ} (hm : 0 < m) (a : ι → ℝ) (k : ι → ℕ) :
    (∑ i ∈ s, ∑ j ∈ s, a i * a j * primitivePrefixGram m (k i) (k j)) = 0 ↔
      cyclotomic m ℝ ∣ primitivePrefixPolynomial s a k := by
  rw [primitivePrefixGram_quadratic_eq_zero_iff s hm]
  constructor
  · intro h
    apply BezoutValuationIncidence.cyclotomic_dvd_of_aeval_primitiveRoots hm
    intro ζ hζ
    rw [aeval_primitivePrefixPolynomial]
    exact h ζ hζ
  · rintro ⟨P, hP⟩ ζ hζ
    rw [← aeval_primitivePrefixPolynomial, hP, map_mul,
      BezoutValuationIncidence.aeval_cyclotomic_primitiveRoot hm hζ, zero_mul]

/-- Combining conductors removes exactly the intersection of their
cyclotomic radicals; no mixed coefficient is discarded. -/
theorem primitivePrefixGram_family_eq_zero_iff {ι : Type*} (s : Finset ι)
    (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m) (a : ι → ℝ) (k : ι → ℕ) :
    (∑ m ∈ S, ∑ i ∈ s, ∑ j ∈ s,
      a i * a j * primitivePrefixGram m (k i) (k j)) = 0 ↔
      ∀ m ∈ S, cyclotomic m ℝ ∣ primitivePrefixPolynomial s a k := by
  constructor
  · intro h m hm
    have hb := single_le_sum
      (fun n hn => primitivePrefixGram_quadratic_nonneg s (hS n hn) a k) hm
    rw [h] at hb
    exact (primitivePrefixGram_quadratic_eq_zero_iff_cyclotomic_dvd s (hS m hm) a k).mp
      (le_antisymm hb (primitivePrefixGram_quadratic_nonneg s (hS m hm) a k))
  · intro h
    exact sum_eq_zero fun m hm =>
      (primitivePrefixGram_quadratic_eq_zero_iff_cyclotomic_dvd s (hS m hm) a k).mpr (h m hm)

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.primitivePrefixGram_quadratic_eq_zero_iff_cyclotomic_dvd
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.primitivePrefixGram_family_eq_zero_iff
