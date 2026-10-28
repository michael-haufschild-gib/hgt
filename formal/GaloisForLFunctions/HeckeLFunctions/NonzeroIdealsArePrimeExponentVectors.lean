import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Nonzero ideals are prime exponent vectors

Unique ideal factorization identifies nonzero integral ideals with finitely supported natural
exponents on the nonzero prime ideals. Fractional-ideal valuations read back each exponent.
This identifies sums over ideals with sums over prime exponent vectors.
-/

noncomputable section

open NumberField IsDedekindDomain FractionalIdeal
open scoped Classical nonZeroDivisors

namespace GaloisForLFunctions.HeckeLFunctions

variable {K : Type*} [Field K] [NumberField K]

/-- The integral ideal with the prescribed prime exponents. -/
def idealOfPrimeExponents (ν : HeightOneSpectrum (𝓞 K) →₀ ℕ) : (Ideal (𝓞 K))⁰ :=
  ⟨ν.prod (fun v n => v.asIdeal ^ n), mem_nonZeroDivisors_of_ne_zero (by
    rw [Finsupp.prod]
    exact Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ v.ne_bot)⟩

/-- The exponents in the unique prime factorization of a nonzero integral ideal. -/
def idealPrimeExponents (I : (Ideal (𝓞 K))⁰) : HeightOneSpectrum (𝓞 K) →₀ ℕ :=
  Finsupp.onFinset (Ideal.finite_factors (nonZeroDivisors.ne_zero I.2)).toFinset
    (fun v => (Associates.mk v.asIdeal).count (Associates.mk (I : Ideal (𝓞 K))).factors)
    (fun v hv => by
      rw [Set.Finite.mem_toFinset]
      exact (Associates.count_ne_zero_iff_dvd (nonZeroDivisors.ne_zero I.2) v.irreducible).mp hv)

theorem idealPrimeExponents_apply (I : (Ideal (𝓞 K))⁰) (v : HeightOneSpectrum (𝓞 K)) :
    (idealPrimeExponents I v : ℤ) = count K v (I : Ideal (𝓞 K)) := by
  rw [count_coe K v (nonZeroDivisors.ne_zero I.2)]
  rfl

/-- A prime valuation reads the corresponding exponent in a finite ideal product. -/
theorem count_idealOfPrimeExponents (ν : HeightOneSpectrum (𝓞 K) →₀ ℕ)
    (v : HeightOneSpectrum (𝓞 K)) :
    count K v ((idealOfPrimeExponents ν : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = ν v := by
  change count K v ((ν.prod (fun w n => w.asIdeal ^ n) : Ideal (𝓞 K)) :
    FractionalIdeal (𝓞 K)⁰ K) = _
  rw [Finsupp.prod]
  change count K v (coeIdealHom (𝓞 K)⁰ K (∏ w ∈ ν.support, w.asIdeal ^ ν w)) = _
  rw [map_prod, count_prod]
  · change (∑ w ∈ ν.support, count K v
      ((w.asIdeal ^ ν w : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) = _
    simp only [coeIdeal_pow, count_pow, count_maximal, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finsupp.mem_support_iff, ne_eq, ite_not]
    split_ifs with h
    · simp [h]
    · rfl
  · intro w _
    exact coeIdeal_ne_zero.mpr (pow_ne_zero _ w.ne_bot)

theorem idealPrimeExponents_idealOfPrimeExponents (ν : HeightOneSpectrum (𝓞 K) →₀ ℕ) :
    idealPrimeExponents (idealOfPrimeExponents ν) = ν := by
  ext v
  exact_mod_cast (idealPrimeExponents_apply _ v).trans (count_idealOfPrimeExponents ν v)

theorem idealOfPrimeExponents_idealPrimeExponents (I : (Ideal (𝓞 K))⁰) :
    idealOfPrimeExponents (idealPrimeExponents I) = I := by
  apply Subtype.ext
  change (idealPrimeExponents I).prod (fun v n => v.asIdeal ^ n) = (I : Ideal (𝓞 K))
  rw [Finsupp.prod, ← Ideal.finprod_heightOneSpectrum_factorization
    (nonZeroDivisors.ne_zero I.2)]
  symm
  apply finprod_eq_finsetProd_of_mulSupport_subset
  intro v hv
  rw [Finset.mem_coe, Finsupp.mem_support_iff]
  intro h
  apply hv
  change v.asIdeal ^ idealPrimeExponents I v = 1
  rw [h, pow_zero]

/-- Unique factorization, with prime ideals as the indices rather than their associates. -/
def primeExponentsIdealEquiv :
    (HeightOneSpectrum (𝓞 K) →₀ ℕ) ≃ (Ideal (𝓞 K))⁰ where
  toFun := idealOfPrimeExponents
  invFun := idealPrimeExponents
  left_inv := idealPrimeExponents_idealOfPrimeExponents
  right_inv := idealOfPrimeExponents_idealPrimeExponents

end GaloisForLFunctions.HeckeLFunctions
