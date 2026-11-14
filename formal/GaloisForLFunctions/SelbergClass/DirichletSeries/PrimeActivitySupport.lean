import GaloisForLFunctions.SelbergClass.DirichletSeries.PrimeFilterCoefficientField
import GaloisForLFunctions.SelbergClass.DirichletSeries.PrimeRestriction

/-!
# Prime support and differential coefficient fields

A prime derivative detects an arithmetic function precisely when that prime divides an integer
with nonzero coefficient. Consequently, the differential definition of a coefficient field
recovers the usual support condition, including arbitrary exceptional prime sets.
-/

namespace GaloisForLFunctions.SelbergClass.DirichletSeries

open ArithmeticFunction HTGeometry Filter
open scoped Classical

noncomputable section

/-- Primes dividing at least one index with nonzero Dirichlet coefficient. -/
def arithmeticPrimeSupport (f : ArithmeticFunction ℂ) : Set Nat.Primes :=
  {p | ∃ n, f n ≠ 0 ∧ p.1 ∣ n}

/-- Differentiation in a prime direction detects exactly the coefficients divisible by that prime. -/
theorem primeDeriv_ne_zero_iff (p : Nat.Primes) (f : ArithmeticFunction ℂ) :
    primeDeriv p.1 f ≠ 0 ↔ p ∈ arithmeticPrimeSupport f := by
  constructor
  · intro h
    by_contra hs
    apply h
    apply primeDeriv_eq_zero_of_not_dvd_support
    intro n hn hp
    exact hs ⟨n, hn, hp⟩
  · rintro ⟨n, hn, hpn⟩ hzero
    have hn0 : n ≠ 0 := by
      intro h
      subst n
      exact hn f.map_zero
    have hfac : (n.factorization p.1 : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (p.2.factorization_pos_of_dvd hn0 hpn))
    have heval := congrArg (fun g : ArithmeticFunction ℂ => g (n / p.1)) hzero
    rw [primeDeriv_apply, Nat.div_mul_cancel hpn, ArithmeticFunction.zero_apply] at heval
    exact (mul_ne_zero hfac hn) heval

/-- The fraction-field activity set is exactly the prime support of an arithmetic function. -/
theorem finitePrimeActivity_eq_arithmeticPrimeSupport (f : ArithmeticFunction ℂ) :
    finitePrimeActivity
        (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField f) =
      arithmeticPrimeSupport f := by
  ext p
  change primeFractionDerivation p
      (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField f) ≠ 0 ↔ _
  rw [primeFractionDerivation_algebraMap]
  have hinj := FaithfulSMul.algebraMap_injective
    (ArithmeticFunction ℂ) arithmeticFunctionFractionField
  constructor
  · intro h
    apply (primeDeriv_ne_zero_iff p f).mp
    intro hz
    exact h (by rw [hz, _root_.map_zero])
  · intro h hz
    apply (primeDeriv_ne_zero_iff p f).mpr h
    apply hinj
    simpa only [_root_.map_zero] using hz

/-- Membership in any filter coefficient field is precisely eventual avoidance of prime support. -/
theorem arithmetic_mem_primeFilterCoefficientField_iff
    (F : Filter Nat.Primes) (f : ArithmeticFunction ℂ) :
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField f ∈
        primeFilterCoefficientField F ↔
      ∀ᶠ p in F, p ∉ arithmeticPrimeSupport f := by
  change (∀ᶠ p in F, primeFractionDerivation p
      (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField f) = 0) ↔ _
  have hs := finitePrimeActivity_eq_arithmeticPrimeSupport f
  simp only [← hs, finitePrimeActivity, Set.mem_setOf_eq, not_not]

/-- The intrinsic finite-prime field recovers finite support in the usual Euler-prime sense. -/
theorem arithmetic_mem_finitePrimeCoefficientField_iff (f : ArithmeticFunction ℂ) :
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField f ∈
        finitePrimeCoefficientField ↔ (arithmeticPrimeSupport f).Finite := by
  rw [mem_finitePrimeCoefficientField_iff, finitePrimeActivity_eq_arithmeticPrimeSupport]

/-- Restriction to a prime set has no active prime outside that set. -/
theorem arithmeticPrimeSupport_primeRestrict_subset
    (S : Set ℕ) (f : ArithmeticFunction ℂ) :
    arithmeticPrimeSupport (primeRestrict S f) ⊆ {p : Nat.Primes | p.1 ∈ S} := by
  rintro p ⟨n, hn, hpn⟩
  have hn0 : n ≠ 0 := by
    intro h
    subst n
    exact hn (primeRestrict S f).map_zero
  have hs : (↑n.primeFactors : Set ℕ) ⊆ S := by
    by_contra hs
    exact hn (if_neg hs)
  exact hs (Nat.mem_primeFactors.mpr ⟨p.2, hpn, hn0⟩)

/-- An Euler restriction is a coefficient for every filter which eventually avoids its primes. -/
theorem primeRestrict_mem_filterField
    (F : Filter Nat.Primes) (S : Set ℕ) (f : ArithmeticFunction ℂ)
    (hS : ∀ᶠ p in F, p.1 ∉ S) :
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField (primeRestrict S f) ∈
      primeFilterCoefficientField F := by
  rw [arithmetic_mem_primeFilterCoefficientField_iff]
  filter_upwards [hS] with p hp hmem
  exact hp (arithmeticPrimeSupport_primeRestrict_subset S f hmem)

#print axioms finitePrimeActivity_eq_arithmeticPrimeSupport
#print axioms primeRestrict_mem_filterField

end
end GaloisForLFunctions.SelbergClass.DirichletSeries
