import GaloisForLFunctions.ArithmeticCountingPositivity.EveryPrimePatternInheritsFiniteCutoffUpperBounds
import GaloisForLFunctions.RenormalizedIntersectionTheory.TheAtomicHodgeIndexSeparatesExactlyTheSubmaximalMargins

/-!
# The two-adic probe separates every nontrivial prime pattern

Finite-cutoff upper bounds transfer the strict finite-flip comparison to
arbitrary prime sets. If two is flipped, the ordinary atomic Hodge index
separates the pattern. Otherwise the two-adic probe does. Neither branch
requires a density, summability, or harmonic cancellation assumption.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

open GaloisForLFunctions.ArithmeticCountingPositivity
  GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

open private primeSetFlip_mul_self from
  GaloisForLFunctions.ArithmeticCountingPositivity.DivisibilityCountsControlInfinitePrimeFlips

/-- Every prime pattern flipping two has a strictly submaximal atomic margin. -/
theorem hodgeSeparates_primeSetFlip_of_two_mem {P : Set ℕ} (h2 : 2 ∈ P) :
    HodgeSeparates (primeSetFlip P) := by
  classical
  rw [hodgeSeparates_primeSetFlip_iff]
  have hsub : ({2} : Finset ℕ) ⊆ primeSetCutoff P 2 := by
    intro q hq
    rw [mem_singleton] at hq
    subst q
    simp only [primeSetCutoff, mem_filter, Nat.mem_primesLE]
    exact ⟨⟨le_rfl, Nat.prime_two⟩, h2⟩
  exact ((primeSetGreatestGap_le_every_cutoff P 2).trans
    (finiteFlipGreatestGap_antitone hsub (primeSetCutoff_primes P 2))).trans_lt
      finiteFlipGreatestGap_two_lt

/-- Adding the two-adic probe strictly separates every nontrivial prime pattern
that leaves two unflipped, including patterns of zero Euler density. -/
theorem not_hasHyperplaneGap_probe_without_density {P : Set ℕ} (h2 : 2 ∉ P)
    {p : ℕ} (hp : p.Prime) (hpP : p ∈ P) :
    ¬ HasHyperplaneGap (fun n => finiteFlip {2} n * primeSetFlip P n)
      (finiteFlipGreatestGap {2}) := by
  classical
  have he : (fun n => finiteFlip {2} n * primeSetFlip P n) = primeSetFlip (insert 2 P) :=
    funext (probe_primeSetFlip h2)
  rw [he, primeSetFlip_hasHyperplaneGap_iff_le_greatestGap, not_le]
  let Q := max p 2
  let G := primeSetCutoff (insert 2 P) Q
  have hG : ∀ q ∈ G, q.Prime := primeSetCutoff_primes _ _
  have hsub : ({2} : Finset ℕ) ⊆ G := by
    intro q hq
    rw [mem_singleton] at hq
    subst q
    simp only [G, primeSetCutoff, mem_filter, Nat.mem_primesLE, Set.mem_insert_iff]
    exact ⟨⟨le_max_right _ _, Nat.prime_two⟩, Or.inl rfl⟩
  have hstrict : ({2} : Finset ℕ) ⊂ G := by
    rw [ssubset_iff_of_subset hsub]
    refine ⟨p, ?_, ?_⟩
    · simp only [G, primeSetCutoff, mem_filter, Nat.mem_primesLE, Set.mem_insert_iff]
      exact ⟨⟨le_max_left _ _, hp⟩, Or.inr hpP⟩
    · simp only [mem_singleton]
      rintro rfl
      exact h2 hpP
  have hlt : finiteFlipGreatestGap G < finiteFlipGreatestGap {2} :=
    (finiteFlipGreatestGap_lt_iff_of_ssubset hstrict hG).mpr
      ((finiteFlipGreatestGap_antitone hsub hG).trans_lt finiteFlipGreatestGap_two_lt)
  exact (primeSetGreatestGap_le_every_cutoff (insert 2 P) Q).trans_lt hlt

/-- The ordinary atomic Hodge index or its two-adic probe separates every
nontrivial prime-set flip, with no restriction on the distribution of primes. -/
theorem hodgeSeparates_or_probe_every_primeSetFlip (P : Set ℕ)
    (hP : ∃ p ∈ P, Nat.Prime p) :
    HodgeSeparates (primeSetFlip P) ∨
      HodgeSeparatesFrom (finiteFlip {2}) (finiteFlipGreatestGap {2})
        (fun n => finiteFlip {2} n * primeSetFlip P n) := by
  obtain ⟨p, hpP, hp⟩ := hP
  by_cases h2 : 2 ∈ P
  · exact Or.inl (hodgeSeparates_primeSetFlip_of_two_mem h2)
  · right
    have hF : ∀ p ∈ ({2} : Finset ℕ), p.Prime := by simp [Nat.prime_two]
    rw [hodgeSeparatesFrom_iff (fun n _ => finiteFlip_mul_self {2} n)
      (fun n _ => by rw [mul_mul_mul_comm, finiteFlip_mul_self, primeSetFlip_mul_self, one_mul])
      ((finiteFlip_hasHyperplaneGap_iff_le_greatestGap {2} hF _).mpr le_rfl)]
    exact not_hasHyperplaneGap_probe_without_density h2 hp hpP

/-- Every prime pattern is trivial or is separated by one of the two fixed
atomic Hodge measurements. -/
theorem primeSetFlip_trivial_or_hodgeSeparates_or_probe (P : Set ℕ) :
    (∀ n, primeSetFlip P n = 1) ∨ HodgeSeparates (primeSetFlip P) ∨
      HodgeSeparatesFrom (finiteFlip {2}) (finiteFlipGreatestGap {2})
        (fun n => finiteFlip {2} n * primeSetFlip P n) := by
  classical
  by_cases hP : ∃ p ∈ P, Nat.Prime p
  · exact Or.inr (hodgeSeparates_or_probe_every_primeSetFlip P hP)
  · left
    intro n
    have he : primeSetCutoff P n = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      have h := mem_filter.mp hp
      exact hP ⟨p, h.2, Nat.prime_of_mem_primesLE h.1⟩
    rw [primeSetFlip_eq_finiteFlip_of_le P le_rfl, he]
    simp only [finiteFlip, prod_empty]

/-- The two fixed margin tests characterize the trivial prime pattern exactly. -/
theorem primeSetFlip_two_margins_iff_trivial (P : Set ℕ) :
    (HasHyperplaneGap (primeSetFlip P) (2 * Real.log 2) ∧
      HasHyperplaneGap (fun n => finiteFlip {2} n * primeSetFlip P n)
        (finiteFlipGreatestGap {2})) ↔ (∀ n, primeSetFlip P n = 1) := by
  have hF : ∀ p ∈ ({2} : Finset ℕ), p.Prime := by simp [Nat.prime_two]
  have hbase := (finiteFlip_hasHyperplaneGap_iff_le_greatestGap {2} hF _).mpr le_rfl
  constructor
  · rintro ⟨hplain, hprobe⟩
    rcases primeSetFlip_trivial_or_hodgeSeparates_or_probe P with h | h | h
    · exact h
    · exact False.elim ((hodgeSeparates_iff_not_hasHyperplaneGap (primeSetFlip_mul_self P)).mp h hplain)
    · have hnot := (hodgeSeparatesFrom_iff (fun n _ => finiteFlip_mul_self {2} n)
        (fun n _ => by rw [mul_mul_mul_comm, finiteFlip_mul_self, primeSetFlip_mul_self, one_mul])
        hbase).mp h
      exact False.elim (hnot hprobe)
  · intro h
    have he : primeSetFlip P = fun _ => 1 := funext h
    rw [he]
    simp only [mul_one]
    exact ⟨zeta_hasHyperplaneGap_two_mul_log_two, hbase⟩

end GaloisForLFunctions.RenormalizedIntersectionTheory
