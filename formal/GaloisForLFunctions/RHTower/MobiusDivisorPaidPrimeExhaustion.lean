import GaloisForLFunctions.RHTower.MobiusDivisorPaidExhaustionStep

/-!
# Unconditional paid prime exhaustion

One inherited history processes every prime. At one fixed proportional clock,
each block, including its mandatory prime and all helpers, has every prefix
paid in both raw and complete logarithmic energy. The comparison starts before
the block. Cutoff drift between consecutive clocks is a separate question.
-/

noncomputable section
open Finset
namespace RHTower.PaidExhaustion

private def scan (w : PrimeCapacity) (k : ℕ) : ℕ := Nat.nth Nat.Prime (w.threshold+k)

private lemma scan_prime (w : PrimeCapacity) (k : ℕ) : (scan w k).Prime :=
  Nat.prime_nth_prime _

private lemma scan_large (w : PrimeCapacity) (k : ℕ) : w.threshold+k+2 ≤ scan w k :=
  Nat.add_two_le_nth_prime _

private lemma scan_count (w : PrimeCapacity) (k : ℕ) :
    Nat.primeCounting (scan w k) = w.threshold+k+1 :=
  Nat.count_nth_succ_of_infinite Nat.infinite_setOf_prime _

private structure State (w : PrimeCapacity) (k : ℕ) where
  core : Finset ℕ
  primes : ∀ p ∈ core, p.Prime
  prior : ∀ p : ℕ, p.Prime → p < scan w k → p ∈ core
  size : core.card ≤ 2*w.budget*Nat.primeCounting (scan w k)

private def initial (w : PrimeCapacity) : State w 0 where
  core := mobiusDivisorSelectionPrimes (scan w 0)
  primes := fun _ hp => (mem_filter.mp hp).2
  prior := fun _ hp hlt => mem_filter.mpr ⟨mem_range.mpr hlt,hp⟩
  size := by
    have hcard : (mobiusDivisorSelectionPrimes (scan w 0)).card = w.threshold := by
      rw [mobiusDivisorSelectionPrimes, ← Nat.count_eq_card_filter_range]
      simpa only [scan,Nat.add_zero] using Nat.count_nth_of_infinite Nat.infinite_setOf_prime w.threshold
    rw [hcard,scan_count]
    have := w.budget_pos
    nlinarith

private def block (w : PrimeCapacity) (k : ℕ) (s : State w k) : List ℕ :=
  Classical.choose (paid_extension w (scan w k) s.core (scan_prime w k)
    (by have := scan_large w k; omega) s.prior s.size)

private lemma block_spec (w : PrimeCapacity) (k : ℕ) (s : State w k) :
    (block w k s).Nodup ∧ (block w k s).length ≤ 2*w.budget ∧
      (∀ q ∈ block w k s, q.Prime ∧ scan w k ≤ q ∧ q < w.factor*scan w k ∧ q ∉ s.core) ∧
      scan w k ∈ s.core ∪ (block w k s).toFinset ∧
      ∀ j : ℕ, mobiusDivisorSelectionEnergy (w.factor*scan w k)
          (s.core ∪ ((block w k s).take j).toFinset) ≤
        mobiusDivisorSelectionEnergy (w.factor*scan w k) s.core ∧
        mobiusDivisorFiniteClockEnergy 1 (w.factor*scan w k)
          (s.core ∪ ((block w k s).take j).toFinset) ≤
          mobiusDivisorFiniteClockEnergy 1 (w.factor*scan w k) s.core :=
  Classical.choose_spec (paid_extension w (scan w k) s.core (scan_prime w k)
    (by have := scan_large w k; omega) s.prior s.size)

private def advance (w : PrimeCapacity) (k : ℕ) (s : State w k) : State w (k+1) where
  core := s.core ∪ (block w k s).toFinset
  primes := by
    intro p hp
    rcases mem_union.mp hp with hp | hp
    · exact s.primes p hp
    · exact ((block_spec w k s).2.2.1 p (List.mem_toFinset.mp hp)).1
  prior := by
    intro p hp hlt
    have hpold : p ≤ scan w k := Nat.le_nth_of_lt_nth_succ
      (by simpa only [scan,Nat.add_assoc] using hlt) hp
    rcases hpold.eq_or_lt with rfl | hlt
    · exact (block_spec w k s).2.2.2.1
    · exact mem_union_left _ (s.prior p hp hlt)
  size := by
    have hs := s.size
    rw [scan_count] at hs ⊢
    have hl := (block_spec w k s).2.1
    have hc := card_union_le s.core (block w k s).toFinset
    rw [List.toFinset_card_of_nodup (block_spec w k s).1] at hc
    nlinarith

private def states (w : PrimeCapacity) : (k : ℕ) → State w k
  | 0 => initial w
  | k+1 => advance w k (states w k)

end RHTower.PaidExhaustion

namespace RHTower
open PaidExhaustion

/-- A closed arithmetic construction: all primes enter one inherited history,
with a uniform finite block size and strictly increasing proportional integer
clocks. Every insertion prefix, including all helpers, is paid against the
state before its block in both raw energy and the complete logarithmic clock.
No energy bound or sign premise is assumed. -/
theorem exists_mobiusDivisorPaidPrimeExhaustion :
    ∃ A D : ℕ, 2 ≤ A ∧ 1 ≤ D ∧
    ∃ r : ℕ → ℕ, ∃ P : ℕ → Finset ℕ, ∃ l : ℕ → List ℕ,
      StrictMono r ∧ StrictMono (fun k => A*r k) ∧
      (∀ k, (r k).Prime) ∧
      (∀ k p, p ∈ P k → p.Prime) ∧
      (∀ p : ℕ, p.Prime → ∃ k, p ∈ P k) ∧
      (∀ k, P (k+1) = P k ∪ (l k).toFinset) ∧
      (∀ k, (l k).Nodup ∧ (l k).length ≤ D ∧
        (∀ q ∈ l k, q.Prime ∧ r k ≤ q ∧ q < A*r k ∧ q ∉ P k) ∧
        r k ∈ P (k+1)) ∧
      (∀ k j, mobiusDivisorSelectionEnergy (A*r k) (P k ∪ ((l k).take j).toFinset) ≤
          mobiusDivisorSelectionEnergy (A*r k) (P k) ∧
        mobiusDivisorFiniteClockEnergy 1 (A*r k) (P k ∪ ((l k).take j).toFinset) ≤
          mobiusDivisorFiniteClockEnergy 1 (A*r k) (P k)) := by
  obtain ⟨w⟩ := exists_primeCapacity
  let P (k : ℕ) := (states w k).core
  let l (k : ℕ) := block w k (states w k)
  have hmono : StrictMono (scan w) := by
    intro i j hij
    exact Nat.nth_strictMono Nat.infinite_setOf_prime (Nat.add_lt_add_left hij w.threshold)
  have hupdate (k : ℕ) : P (k+1) = P k ∪ (l k).toFinset := rfl
  refine ⟨w.factor,2*w.budget,w.factor_large,by have := w.budget_pos; omega,
    scan w,P,l,hmono,?_,scan_prime w,?_,?_,hupdate,?_,?_⟩
  · intro i j hij
    exact Nat.mul_lt_mul_of_pos_left (hmono hij) (by have := w.factor_large; omega)
  · intro k p hp
    exact (states w k).primes p hp
  · intro p hp
    refine ⟨p, (states w p).prior p hp ?_⟩
    have := scan_large w p
    omega
  · intro k
    have h := block_spec w k (states w k)
    exact ⟨h.1,h.2.1,h.2.2.1,(hupdate k).symm ▸ h.2.2.2.1⟩
  · intro k j
    exact (block_spec w k (states w k)).2.2.2.2 j

end RHTower
