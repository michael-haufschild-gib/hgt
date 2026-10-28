import GaloisForLFunctions.Core
import GaloisForLFunctions.ArithmeticIntersectionTheory.TheDifferentOfATorsionOrbit

/-!
# Prime excitation energies separate valuation labels

The positive excitation weight adds the tame different to logarithmic degree.
Rational independence of prime logarithms makes all finite-prime energies simple.
-/

noncomputable section

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticIntersectionTheory

/-- Rational local weight: the valuation plus its nonzero tame correction. -/
def primeExcitationWeight (p : Nat.Primes) (k : ℕ) : ℚ :=
  (k : ℚ) + if k = 0 then 0 else ((p : ℕ) - (1 : ℚ))⁻¹

theorem primeExcitationWeight_zero (p : Nat.Primes) : primeExcitationWeight p 0 = 0 := by
  simp [primeExcitationWeight]

/-- Each local excitation weight strictly increases with its valuation. -/
theorem primeExcitationWeight_strictMono (p : Nat.Primes) :
    StrictMono (primeExcitationWeight p) := by
  intro a b hab
  have hp : (1 : ℚ) < (p : ℕ) := by exact_mod_cast p.property.one_lt
  have hb : b ≠ 0 := by omega
  by_cases ha : a = 0
  · subst a
    rw [primeExcitationWeight_zero, primeExcitationWeight, if_neg hb]
    exact add_pos_of_pos_of_nonneg (by exact_mod_cast hab)
      (inv_nonneg.mpr (sub_nonneg.mpr hp.le))
  · rw [primeExcitationWeight, primeExcitationWeight, if_neg ha, if_neg hb]
    have habQ : (a : ℚ) < (b : ℚ) := by exact_mod_cast hab
    linarith only [habQ]

/-- The finite-prime excitation energy on valuation coordinates. -/
def finitePrimeExcitationEnergy (Q : Finset Nat.Primes) (e : Q → ℕ) : ℝ :=
  ∑ p : Q, (primeExcitationWeight p (e p) : ℝ) * Real.log ((p : Nat.Primes) : ℕ)

/-- Distinct valuation labels give distinct arithmetic excitation energies. -/
theorem finitePrimeExcitationEnergy_injective (Q : Finset Nat.Primes) :
    Function.Injective (finitePrimeExcitationEnergy Q) := by
  intro e f h
  have hi : LinearIndependent ℚ (fun p : Q => Real.log ((p : Nat.Primes) : ℕ)) :=
    linearIndependent_log_primes.comp (fun p : Q => (p : Nat.Primes)) Subtype.val_injective
  have hc : (fun p : Q => primeExcitationWeight p (e p)) =
      fun p : Q => primeExcitationWeight p (f p) := by
    apply hi.fintypeLinearCombination_injective
    change (∑ p : Q, primeExcitationWeight p (e p) • Real.log ((p : Nat.Primes) : ℕ)) =
      ∑ p : Q, primeExcitationWeight p (f p) • Real.log ((p : Nat.Primes) : ℕ)
    simpa only [finitePrimeExcitationEnergy, Rat.smul_def] using h
  funext p
  exact (primeExcitationWeight_strictMono p).injective (congrFun hc p)

/-- The tame different is nonnegative at every integer. -/
theorem tameDifferent_nonneg (n : ℕ) : 0 ≤ tameDifferent n := by
  apply Finset.sum_nonneg
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
  exact div_nonneg (Real.log_nonneg hp1.le) (sub_nonneg.mpr hp1.le)

/-- Torsion adjunction bounds the tame different by logarithmic degree. -/
theorem tameDifferent_le_log {n : ℕ} (hn : 0 < n) : tameDifferent n ≤ Real.log n := by
  have h := selfIntersection_nonneg hn
  rw [selfIntersection_eq hn] at h
  exact sub_nonneg.mp h

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
