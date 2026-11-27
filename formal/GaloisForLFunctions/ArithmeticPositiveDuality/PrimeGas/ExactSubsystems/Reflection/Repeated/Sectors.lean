import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Readings
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Outgoing

/-! # Finite tests for critical-line symmetry after repeating a prime sector -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated

open Finset _root_.HTGeometry
open FixedCount (State capacity pairCount level outgoingShare)
open scoped ComplexConjugate

variable {S : Finset Nat.Primes} (c : S → ℕ) (m : ℕ)

def sectorEnergy (x : State c m) := energy (level x)

def share (s : ℂ) (x : State c m) := outgoingShare s x

/-- Empty sectors have the empty pairing. On feasible sectors the occupation intervals
decide reflection without enumerating the many-particle spectrum. -/
theorem sector_reflection_iff :
    Reflects (sectorEnergy c m) ↔ capacity c < m ∨ (∑ i, pairCount c m i)=2*m := by
  by_cases h : m ≤ capacity c
  · have hn := (FixedCount.feasible_iff c m).mpr h
    have eq := FixedCount.reflection_iff S c m
    change Nonempty (State c m) ∧ Reflects (sectorEnergy c m) ↔ _ at eq
    rw [and_iff_right hn,and_iff_right h] at eq
    rw [or_iff_right (not_lt.mpr h),eq]
  · have absent : ¬Nonempty (State c m) := fun he => h ((FixedCount.feasible_iff c m).mp he)
    exact ⟨fun _ => Or.inl (lt_of_not_ge h),fun _ => ⟨0,Equiv.refl _,fun x => (absent ⟨x⟩).elim⟩⟩

theorem repeated_sector_reflection (k : ℕ) :
    Reflects (copyEnergy (sectorEnergy c m) k) ↔ k=0 ∨ capacity c < m ∨ (∑ i, pairCount c m i)=2*m := by
  rw [reflects_copies_iff,sector_reflection_iff]

theorem share_pos (s : ℂ) (x : State c m) : 0 < share c m s x := by
  letI : Nonempty (State c m) := ⟨x⟩
  rw [share,FixedCount.outgoing_gibbs]
  exact finiteGibbsStateWeight_pos _ _ _

private theorem share_matches (s : ℂ) :
    Matches (share c m s) (share c m (1-conj s)) ↔ s.re=1/2 ∨ Reflects (sectorEnergy c m) := by
  constructor
  · rintro ⟨R,h⟩
    rcases (FixedCount.fixed_permutation_iff s R).mp h with he | ⟨L,he⟩
    · exact Or.inl he
    · exact Or.inr ⟨L,R,he⟩
  · rintro (hs | ⟨L,R,h⟩)
    · exact ⟨Equiv.refl _,(FixedCount.fixed_permutation_iff s _).mpr (Or.inl hs)⟩
    · exact ⟨R,(FixedCount.fixed_permutation_iff s R).mpr (Or.inr ⟨L,h⟩)⟩

private theorem initial_moments (s w : ℂ) (j : ℕ) (small : j < 2) :
    moment (share c m s) j = moment (share c m w) j := by
  rcases (show j=0 ∨ j=1 by omega) with rfl | rfl
  · simp only [moment,pow_zero]
  · rcases isEmpty_or_nonempty (State c m) with he | hn
    · letI := he
      simp only [moment,univ_eq_empty,sum_empty]
    · letI := hn
      simp only [moment,pow_one,share,FixedCount.outgoing_gibbs,sum_finiteGibbsStateWeight_eq_one]

variable {Z : Type*} [Fintype Z]

/-- Compare only orders two through the dimension of one copy, regardless of total
dimension after replication and attachment of the common bath. -/
theorem finite_probe_iff (s : ℂ) (k : ℕ) (B : Z → ℝ) (b : ℝ) :
    (∀ j, 2 ≤ j → j ≤ Fintype.card (State c m) →
      moment (observed (share c m s) k B b) j = moment (observed (share c m (1-conj s)) k B b) j) ↔
      k=0 ∨ IsEmpty Z ∨ (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x) ∨
        capacity c < m ∨ (∑ i, pairCount c m i)=2*m := by
  rw [split_isometric_iff,← sector_reflection_iff,← share_matches, matches_iff_moments]
  have instant := fun j => observed_eq_iff (fun x => (share_pos c m s x).le)
    (fun x => (share_pos c m (1-conj s) x).le) k j B b
  constructor
  · intro h
    by_cases hk : k=0
    · exact Or.inl hk
    by_cases hz : IsEmpty Z
    · exact Or.inr (Or.inl hz)
    refine Or.inr (Or.inr (fun j hj => ?_))
    by_cases enough : 2 ≤ j
    · exact (((instant j).mp (h j enough hj)).resolve_left hk).resolve_left hz
    · exact initial_moments c m s _ j (lt_of_not_ge enough)
  · intro h j _ hj
    exact (instant j).mpr (h.imp_right (Or.imp_right (fun he => he j hj)))

#print axioms sector_reflection_iff
#print axioms repeated_sector_reflection
#print axioms finite_probe_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated
