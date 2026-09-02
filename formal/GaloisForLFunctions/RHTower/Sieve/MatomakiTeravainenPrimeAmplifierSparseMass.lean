import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPrimeAmplifierSupport
import GaloisForLFunctions.RHTower.Sieve.PrimeWindowBrunTitchmarsh

/-!
# Sparse mass of the Matomäki--Teräväinen prime amplifier

The relevant Heath--Brown quantity is coefficient size times support cardinality.  Unique
factorization supplies the factorial/stars-and-bars part, while Brun--Titchmarsh supplies the
logarithmic saving in the underlying prime block.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The prime-amplifier support injects into the literal prime set `(P,2P]`. -/
theorem card_mtTypeIPrimeCoeffSupport_le_prime_Ioc (P : ℕ) :
    (mtTypeIPrimeCoeffSupport P).card ≤
      #{p ∈ Finset.Ioc P (2 * P) | p.Prime} := by
  let f : ↑(mtTypeIPrimeCoeffSupport P) →
      ↑({p ∈ Finset.Ioc P (2 * P) | p.Prime}) := fun j =>
    ⟨(j.1 : ℕ) + 1, by
      rw [Finset.mem_filter]
      have hj := mem_mtTypeIPrimeCoeffSupport.mp j.property
      exact ⟨Finset.mem_Ioc.mpr (mtTypeIPrimeCoeff_support j.1 hj),
        mtTypeIPrimeCoeff_prime_support P j.1 hj⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply Fin.ext
    have hval := congrArg (fun q : ↑({p ∈ Finset.Ioc P (2 * P) | p.Prime}) =>
      (q : ℕ)) hij
    dsimp only [f] at hval
    exact Nat.add_right_cancel hval
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

/-- Brun--Titchmarsh bound for the literal unraised prime-amplifier support. -/
theorem card_mtTypeIPrimeCoeffSupport_le_bt
    (P : ℕ) {z : ℝ} (hz : 1 < z) :
    ((mtTypeIPrimeCoeffSupport P).card : ℝ) ≤
      2 * (P : ℝ) / Real.log z + 6 * z * (1 + Real.log z) ^ 3 + 1 := by
  have hcard := card_mtTypeIPrimeCoeffSupport_le_prime_Ioc P
  have hcast : ((mtTypeIPrimeCoeffSupport P).card : ℝ) ≤
      (#{p ∈ Finset.Ioc P (2 * P) | p.Prime} : ℝ) := by
    exact_mod_cast hcard
  have hbt := card_prime_Ioc_le_bt (A := P) (B := 2 * P) (by omega) hz
  calc
    ((mtTypeIPrimeCoeffSupport P).card : ℝ) ≤
        (#{p ∈ Finset.Ioc P (2 * P) | p.Prime} : ℝ) := hcast
    _ ≤ 2 * (((2 * P : ℕ) : ℝ) - (P : ℝ)) / Real.log z +
        6 * z * (1 + Real.log z) ^ 3 + 1 := hbt
    _ = 2 * (P : ℝ) / Real.log z + 6 * z * (1 + Real.log z) ^ 3 + 1 := by
      push_cast
      ring

/-- Factorial coefficient loss times raised support is at most one power of the enlarged prime
alphabet per convolution coordinate. -/
theorem factorial_mul_card_mtTypeIPrimeRaisedSupport_le
    (P ell : ℕ) :
    ell.factorial * (mtTypeIPrimeRaisedSupport P ell).card ≤
      ((mtTypeIPrimeCoeffSupport P).card + ell) ^ ell := by
  let d := (mtTypeIPrimeCoeffSupport P).card + ell - 1
  have hsupport := card_mtTypeIPrimeRaisedSupport_le_choose P ell
  have hfactorial : ell.factorial * d.choose ell ≤ d ^ ell := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow d ell
  have hd : d ≤ (mtTypeIPrimeCoeffSupport P).card + ell := by
    dsimp only [d]
    omega
  calc
    ell.factorial * (mtTypeIPrimeRaisedSupport P ell).card ≤
        ell.factorial * d.choose ell := Nat.mul_le_mul_left _ hsupport
    _ ≤ d ^ ell := hfactorial
    _ ≤ ((mtTypeIPrimeCoeffSupport P).card + ell) ^ ell :=
      Nat.pow_le_pow_left hd ell

/-- Closed Brun--Titchmarsh envelope for factorial-weighted raised support. -/
theorem factorial_mul_card_mtTypeIPrimeRaisedSupport_le_bt
    (P ell : ℕ) {z : ℝ} (hz : 1 < z) :
    ((ell.factorial * (mtTypeIPrimeRaisedSupport P ell).card : ℕ) : ℝ) ≤
      (2 * (P : ℝ) / Real.log z + 6 * z * (1 + Real.log z) ^ 3 + 1 + ell) ^ ell := by
  let Q : ℝ := 2 * (P : ℝ) / Real.log z + 6 * z * (1 + Real.log z) ^ 3 + 1
  have hnat := factorial_mul_card_mtTypeIPrimeRaisedSupport_le P ell
  have hcast : ((ell.factorial * (mtTypeIPrimeRaisedSupport P ell).card : ℕ) : ℝ) ≤
      (((mtTypeIPrimeCoeffSupport P).card + ell : ℕ) : ℝ) ^ ell := by
    exact_mod_cast hnat
  have hprime := card_mtTypeIPrimeCoeffSupport_le_bt P hz
  have hbase :
      (((mtTypeIPrimeCoeffSupport P).card + ell : ℕ) : ℝ) ≤ Q + ell := by
    dsimp only [Q]
    push_cast
    linarith
  have hnonneg : 0 ≤ (((mtTypeIPrimeCoeffSupport P).card + ell : ℕ) : ℝ) := by
    positivity
  exact hcast.trans (by
    simpa only [Q] using pow_le_pow_left₀ hnonneg hbase ell)

end

end RHTower.Sieve
