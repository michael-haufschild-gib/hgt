import GaloisForLFunctions.RHTower.MobiusMertensPrimeRemovalTentLaw
import GaloisForLFunctions.RHTower.MobiusMertensReversalEnergyCriterion
import Mathlib.Data.Finset.NatAntidiagonal

open scoped BigOperators

namespace RHTower

noncomputable section

/-! Exact one-prime localization of the positive palindromic Mertens reversal energy. -/

/-- Positive palindromic reversal energy expressed entirely through one prime-free Mertens
window. -/
def mobiusPrimeWindowPalindromicEnergy (p : Nat.Primes) (N : ℕ) : ℝ :=
  (1 / 4 : ℝ) *
    ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) N,
    ((mobiusPrimeWindowPartialSum p ab.1).re +
      (mobiusPrimeWindowPartialSum p ab.2).re) ^ (2 : ℕ)

/-- Removing any one prime preserves the palindromic Mertens energy exactly. -/
theorem mobiusPrimeWindowPalindromicEnergy_eq_mertens
    (p : Nat.Primes) (N : ℕ) :
    mobiusPrimeWindowPalindromicEnergy p N =
      mobiusMertensPalindromicEnergy N := by
  rw [mobiusPrimeWindowPalindromicEnergy, mobiusMertensPalindromicEnergy]
  apply congrArg ((1 / 4 : ℝ) * ·)
  apply Finset.sum_congr rfl
  intro ab _hab
  rw [mobiusMertensPartialSum_eq_primeWindow p.prop,
    mobiusMertensPartialSum_eq_primeWindow p.prop]

/-- All-subpower upper control of one prime-window palindromic energy. -/
def MobiusPrimeWindowPalindromicEnergySubpowerUpperBound (p : Nat.Primes) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
    mobiusPrimeWindowPalindromicEnergy p N ≤ C * ((N : ℝ) + 1) ^ (2 + ε)

/-- A single arbitrary prime-free window carries exactly the global reversal-energy criterion. -/
theorem mobiusPrimeWindowPalindromicEnergySubpowerUpperBound_iff
    (p : Nat.Primes) :
    MobiusPrimeWindowPalindromicEnergySubpowerUpperBound p ↔
      MobiusMertensPalindromicEnergySubpowerUpperBound := by
  constructor
  · intro h ε hε
    obtain ⟨C, hC, hbound⟩ := h ε hε
    exact ⟨C, hC, fun N => by
      rw [← mobiusPrimeWindowPalindromicEnergy_eq_mertens p N]
      exact hbound N⟩
  · intro h ε hε
    obtain ⟨C, hC, hbound⟩ := h ε hε
    exact ⟨C, hC, fun N => by
      rw [mobiusPrimeWindowPalindromicEnergy_eq_mertens p N]
      exact hbound N⟩

/-- **Prime-removal reversal-energy universality.** Every prime-free Mertens window realizes the
same positive palindromic energy, the same subpower criterion, and hence the same RH implication. -/
theorem mobiusMertens_primeWindowReversalEnergyUniversality
    (p q : Nat.Primes) :
    (∀ N, mobiusPrimeWindowPalindromicEnergy p N =
      mobiusPrimeWindowPalindromicEnergy q N) ∧
    (MobiusPrimeWindowPalindromicEnergySubpowerUpperBound p ↔
      MobiusMertensPalindromicEnergySubpowerUpperBound) ∧
    (MobiusPrimeWindowPalindromicEnergySubpowerUpperBound p → RiemannHypothesis) := by
  refine ⟨fun N => ?_, mobiusPrimeWindowPalindromicEnergySubpowerUpperBound_iff p, ?_⟩
  · rw [mobiusPrimeWindowPalindromicEnergy_eq_mertens,
      mobiusPrimeWindowPalindromicEnergy_eq_mertens]
  · intro h
    exact mobiusMertensPalindromicEnergySubpowerUpperBound_implies_riemannHypothesis
      ((mobiusPrimeWindowPalindromicEnergySubpowerUpperBound_iff p).mp h)

end

end RHTower
