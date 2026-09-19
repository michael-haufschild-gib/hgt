import GaloisForLFunctions.RHTower.MobiusDivisorLateBlockSuccessorEnvelope
import GaloisForLFunctions.RHTower.MobiusDivisorLocalizedInteractions
import GaloisForLFunctions.RHTower.MobiusDivisorOrientedPrimeExtension

/-!
# Late-block transport of mixed selection-energy differences

For an actual late prime block, this file keeps the complete signed block
mass.  It proves its exact effect on a remaining two-prime interaction.  The
one-prime steering law already lives in `MobiusDivisorNonemptyEnergy`.
-/

noncomputable section
set_option autoImplicit false
open Finset
namespace RHTower

/-- Mixed second difference of selection energy under two prospective primes. -/
def mobiusDivisorSecondEnergyDifference (M : ℕ) (P : Finset ℕ) (p q : ℕ) : ℝ :=
  mobiusDivisorSelectionEnergy M (insert q (insert p P)) -
    mobiusDivisorSelectionEnergy M (insert p P) -
    mobiusDivisorSelectionEnergy M (insert q P) +
      mobiusDivisorSelectionEnergy M P

private theorem mobiusDivisorSelectionHead_second_difference
    (M : ℕ) (P : Finset ℕ) {p q : ℕ} (hpq : p ≠ q) :
    mobiusDivisorSelectionFibre M (insert q (insert p P)) ∅ -
        mobiusDivisorSelectionFibre M (insert p P) ∅ -
        mobiusDivisorSelectionFibre M (insert q P) ∅ +
          mobiusDivisorSelectionFibre M P ∅ =
      mobiusDivisorSelectionFibre M P (insert p {q}) := by
  simp only [mobiusDivisorSelectionFibre_insert, notMem_empty, if_false,
    insert_empty_eq, mem_singleton, hpq]
  ring

/-- A late block transports every residual two-prime interaction by its exact
signed dilation mass times the pre-block double fibre. -/
theorem mobiusDivisorSecondEnergyDifference_union_late_primes
    (M : ℕ) (P L : Finset ℕ)
    (hL : ∀ s ∈ L, s.Prime ∧ s < M ∧ M ≤ 2 * s) (hfree : ∀ s ∈ L, s ∉ P)
    {p q : ℕ} (hpL : p ∉ L) (hqL : q ∉ L)
    (hpq : p ≠ q) :
    mobiusDivisorSecondEnergyDifference M (P ∪ L) p q =
      mobiusDivisorSecondEnergyDifference M P p q +
        2 * (∑ s ∈ L, mobiusDivisorDilationChannel M s) *
          mobiusDivisorSelectionFibre M P (insert p {q}) := by
  let A := insert q (insert p P)
  have hLA : ∀ s ∈ L, s ∉ A := by
    intro s hs
    simp only [A, mem_insert, not_or]
    exact ⟨fun h => hqL (h ▸ hs), fun h => hpL (h ▸ hs), hfree s hs⟩
  have htransport (C : Finset ℕ) (hC : C ⊆ A) :=
    mobiusDivisorSelectionEnergy_union_late_primes M C L hL
      (fun s hs h => hLA s hs (hC h))
  have hA : insert q (insert p P) ⊆ A := Subset.rfl
  have hpA : insert p P ⊆ A := subset_insert _ _
  have hqA : insert q P ⊆ A := by
    intro s hs
    simp only [A, mem_insert] at hs ⊢
    tauto
  have hPA : P ⊆ A := by
    intro s hs
    exact mem_insert_of_mem (mem_insert_of_mem hs)
  unfold mobiusDivisorSecondEnergyDifference
  simp only [← insert_union]
  rw [htransport _ hA, htransport _ hpA, htransport _ hqA, htransport _ hPA]
  have hhead := mobiusDivisorSelectionHead_second_difference M P hpq
  linear_combination 2 * (∑ s ∈ L, mobiusDivisorDilationChannel M s) * hhead

/-- At the empty core, a late block weakly lowers every residual two-prime
interaction. -/
theorem mobiusDivisorSecondEnergyDifference_empty_union_late_primes_le
    (M : ℕ) (L : Finset ℕ)
    (hL : ∀ s ∈ L, s.Prime ∧ s < M ∧ M ≤ 2 * s)
    {p q : ℕ}
    (hpL : p ∉ L) (hqL : q ∉ L) (hpq : p ≠ q) :
    mobiusDivisorSecondEnergyDifference M L p q ≤
      mobiusDivisorSecondEnergyDifference M ∅ p q := by
  rw [show L = ∅ ∪ L by simp,
    mobiusDivisorSecondEnergyDifference_union_late_primes M ∅ L hL (by simp)
      hpL hqL hpq]
  have hsum : (∑ s ∈ L, mobiusDivisorDilationChannel M s) ≤ 0 :=
    sum_nonpos fun s hs => mobiusDivisorDilationChannel_late_prime_nonpos (hL s hs).1 M
  have hfibre : 0 ≤ mobiusDivisorSelectionFibre M ∅ (insert p {q}) := by
    have h := mobiusDivisorSelectionFibre_empty_parity_nonneg M (insert p {q})
    have hcard : (insert p ({q} : Finset ℕ)).card = 2 := by simp [hpq]
    rw [hcard] at h
    norm_num at h
    exact h
  have hprod : (∑ s ∈ L, mobiusDivisorDilationChannel M s) *
      mobiusDivisorSelectionFibre M ∅ (insert p {q}) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hsum hfibre
  linarith

end RHTower
