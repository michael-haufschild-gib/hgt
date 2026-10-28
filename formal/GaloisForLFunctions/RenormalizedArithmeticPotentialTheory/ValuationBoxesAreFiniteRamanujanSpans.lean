import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheSieveClassesAreValuationCoordinates
import GaloisForLFunctions.RHTower.SteinhausSmoothRoughSplit
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.GcdProfilesHaveFiniteRamanujanExpansions

/-!
# Valuation boxes lie in finite Ramanujan spans

The modulus with exponent `L` at each prime below `P` records all valuations
below `L` exactly. Cutting a smooth-part profile off outside that box makes it
a function of the gcd with this modulus, hence a finite Ramanujan expansion.
-/

noncomputable section

open Finset
open scoped Classical

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open HTGeometry

/-- Bundled primes strictly below a threshold. -/
def primeThresholdPrimes (P : ℕ) : Finset Nat.Primes := by
  classical
  exact (Nat.primesBelow P).attach.image
    (fun p => (⟨p.val, (Nat.mem_primesBelow.mp p.property).2⟩ : Nat.Primes))

theorem mem_primeThresholdPrimes (P : ℕ) (p : Nat.Primes) :
    p ∈ primeThresholdPrimes P ↔ (p : ℕ) < P := by
  classical
  rw [primeThresholdPrimes, mem_image]
  constructor
  · rintro ⟨q, _, hq⟩
    have hval : q.val = (p : ℕ) := congrArg Subtype.val hq
    exact hval ▸ (Nat.mem_primesBelow.mp q.property).1
  · intro hp
    let q : ↥(Nat.primesBelow P) := ⟨p.val, Nat.mem_primesBelow.mpr ⟨hp, p.property⟩⟩
    exact ⟨q, mem_attach _ q, Subtype.ext rfl⟩

/-- The positive modulus with exponent `L` at every prime below `P`. -/
def primeValuationBoxModulus (P L : ℕ) : ℕ :=
  primeProduct (sieveExponentVector (primeThresholdPrimes P) (fun _ => L))

theorem primeValuationBoxModulus_pos (P L : ℕ) : 0 < primeValuationBoxModulus P L :=
  primeProduct_pos _

theorem factorization_primeValuationBoxModulus (P L p : ℕ) :
    (primeValuationBoxModulus P L).factorization p =
      if p ∈ Nat.primesBelow P then L else 0 := by
  classical
  by_cases hp : p.Prime
  · let q : Nat.Primes := ⟨p, hp⟩
    change (primeProduct (sieveExponentVector (primeThresholdPrimes P) (fun _ => L))).factorization
      (q : ℕ) = _
    rw [primeProduct_factorization, sieveExponentVector_apply]
    by_cases hP : p < P
    · rw [dif_pos ((mem_primeThresholdPrimes P q).mpr hP),
        if_pos (Nat.mem_primesBelow.mpr ⟨hP, hp⟩)]
    · have hq : q ∉ primeThresholdPrimes P := fun h => hP ((mem_primeThresholdPrimes P q).mp h)
      have hnot : p ∉ Nat.primesBelow P := fun h => hP (Nat.mem_primesBelow.mp h).1
      rw [dif_neg hq, if_neg hnot]
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp,
      if_neg (fun h => hp (Nat.mem_primesBelow.mp h).2)]

/-- Every retained small-prime valuation is strictly below `L`. -/
def primeValuationBox (P L n : ℕ) : Prop :=
  ∀ p ∈ Nat.primesBelow P, n.factorization p < L

theorem factorization_gcd_primeValuationBoxModulus {n : ℕ} (hn : n ≠ 0)
    (P L p : ℕ) :
    (n.gcd (primeValuationBoxModulus P L)).factorization p =
      min (n.factorization p) (if p ∈ Nat.primesBelow P then L else 0) := by
  have h := congrArg (fun f : ℕ →₀ ℕ => f p)
    (Nat.factorization_gcd hn (primeValuationBoxModulus_pos P L).ne')
  change (n.gcd (primeValuationBoxModulus P L)).factorization p =
    min (n.factorization p) ((primeValuationBoxModulus P L).factorization p) at h
  rwa [factorization_primeValuationBoxModulus] at h

/-- Taking the gcd preserves precisely whether a valuation lies inside the box. -/
theorem primeValuationBox_gcd_iff {n : ℕ} (hn : n ≠ 0) (P L : ℕ) :
    primeValuationBox P L (n.gcd (primeValuationBoxModulus P L)) ↔
      primeValuationBox P L n := by
  constructor
  · intro h p hp
    have hmin := h p hp
    rw [factorization_gcd_primeValuationBoxModulus hn, if_pos hp] at hmin
    exact (min_lt_iff.mp hmin).resolve_right (lt_irrefl L)
  · intro h p hp
    rw [factorization_gcd_primeValuationBoxModulus hn, if_pos hp]
    exact min_lt_iff.mpr (Or.inl (h p hp))

/-- Inside the valuation box the gcd is the entire smooth part. -/
theorem gcd_primeValuationBoxModulus_eq_smoothPart {n : ℕ} (hn : n ≠ 0)
    {P L : ℕ} (hbox : primeValuationBox P L n) :
    n.gcd (primeValuationBoxModulus P L) = RHTower.Sieve.smoothPart (P - 1) n := by
  apply Nat.factorization_inj (Nat.gcd_ne_zero_left hn) (RHTower.Sieve.smoothPart_pos _ _).ne'
  rw [RHTower.factorization_sieveSmoothPart]
  ext p
  rw [factorization_gcd_primeValuationBoxModulus hn, Finsupp.filter_apply]
  by_cases hp : p ∈ Nat.primesBelow P
  · rw [if_pos hp, if_pos hp, min_eq_left (hbox p hp).le]
  · rw [if_neg hp, if_neg hp, _root_.min_zero]

/-- A smooth-part profile cut off outside a finite valuation box is a gcd profile. -/
theorem truncated_smoothProfile_eq_gcdProfile {n : ℕ} (hn : n ≠ 0)
    (P L : ℕ) (F : ℕ → ℝ) :
    (if primeValuationBox P L n then F (RHTower.Sieve.smoothPart (P - 1) n) else 0) =
      if primeValuationBox P L (n.gcd (primeValuationBoxModulus P L)) then
        F (n.gcd (primeValuationBoxModulus P L)) else 0 := by
  classical
  rw [primeValuationBox_gcd_iff hn]
  by_cases hbox : primeValuationBox P L n
  · rw [if_pos hbox, if_pos hbox, gcd_primeValuationBoxModulus_eq_smoothPart hn hbox]
  · rw [if_neg hbox, if_neg hbox]

/-- The conductor set is fixed by the valuation box, independent of the profile. -/
theorem exists_truncated_smoothProfile_normalizedRamanujan_expansion
    (P L : ℕ) (F : ℕ → ℝ) :
    ∃ a : ℕ → ℝ, ∀ n : ℕ, 0 < n →
      (if primeValuationBox P L n then F (RHTower.Sieve.smoothPart (P - 1) n) else 0) =
        ∑ q ∈ (primeValuationBoxModulus P L).divisors, a q * normalizedRamanujanMode q n := by
  classical
  obtain ⟨a, ha⟩ := exists_gcdProfile_normalizedRamanujan_expansion
    (fun d => if primeValuationBox P L d then F d else 0) (primeValuationBoxModulus_pos P L)
  refine ⟨a, fun n hn => ?_⟩
  rw [truncated_smoothProfile_eq_gcdProfile hn.ne']
  exact ha n hn

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

