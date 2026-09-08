import GaloisForLFunctions.RHTower.MobiusDivisorNonemptyEnergy
import Mathlib.Data.Finset.Max
/-!
# A prime separating the signs remains contracting

All mergers at other labels preserve the two sign classes distinguished by
membership of one prime. Their full paired overlaps remain nonpositive even
after arbitrary other subsets, retaining every overlapping source coordinate.
Actual source occurrence is certified separately; a separator is not assumed
to exist at every state.
-/
noncomputable section
open Finset
namespace RHTower
/-- A retained prime separates nonpositive free fibres from nonnegative containing fibres. -/
def MobiusDivisorPrimeSeparated (M : ℕ) (P : Finset ℕ) (p : ℕ) : Prop :=
  ∀ R : Finset ℕ, (p∉R → mobiusDivisorSelectionFibre M P R≤0) ∧
    (p∈R → 0≤ mobiusDivisorSelectionFibre M P R)

/-- Processing another label preserves the entire prime-separated sign field. -/
theorem mobiusDivisorPrimeSeparated_insert {M p q : ℕ} {P : Finset ℕ}
    (hpq : p≠q) (h : MobiusDivisorPrimeSeparated M P p) :
    MobiusDivisorPrimeSeparated M (insert q P) p := by
  intro R
  rw [mobiusDivisorSelectionFibre_insert]
  by_cases hqR : q∈R
  · simp [hqR]
  simp only [hqR,if_false]
  constructor
  · intro hpR
    exact add_nonpos ((h R).1 hpR) ((h (insert q R)).1 (by simp [hpq,hpR]))
  · intro hpR
    exact add_nonneg ((h R).2 hpR) ((h (insert q R)).2 (by simp [hpR]))

/-- Prime separation is hereditary under every finite set of other mergers. -/
theorem mobiusDivisorPrimeSeparated_union {M p : ℕ} {P : Finset ℕ}
    (h : MobiusDivisorPrimeSeparated M P p) (T : Finset ℕ) (hpT : p∉T) :
    MobiusDivisorPrimeSeparated M (P∪T) p := by
  induction T using Finset.induction_on with
  | empty => simpa using h
  | @insert q T hqT ih =>
    simp only [mem_insert,not_or] at hpT
    simpa only [union_insert] using mobiusDivisorPrimeSeparated_insert hpT.1 (ih hpT.2)

/-- A separated prime contracts complete energy after every choice of other
processed labels; arbitrary overlap and sign defects remain in the field. -/
theorem mobiusDivisorSelectionEnergy_insert_le_of_separated {M p : ℕ} {P : Finset ℕ}
    (hp : p.Prime) (hpM : p<M) (hpP : p∉P)
    (h : MobiusDivisorPrimeSeparated M P p) (T : Finset ℕ) (hpT : p∉T) :
    mobiusDivisorSelectionEnergy M (insert p (P∪T)) ≤ mobiusDivisorSelectionEnergy M (P∪T) := by
  have hs := mobiusDivisorPrimeSeparated_union h T hpT
  have he := mobiusDivisorSelectionEnergy_insert_cross hp M (P∪T) hpM (by simp [hpP,hpT])
  have hsum : (∑ R∈((mobiusDivisorSelectionPrimes M).erase p).powerset,
      mobiusDivisorSelectionFibre M (P∪T) R*
        mobiusDivisorSelectionFibre M (P∪T) (insert p R)) ≤ 0 := by
    apply sum_nonpos
    intro R hR
    have hpR : p∉R := fun hpR => (mem_erase.mp (mem_powerset.mp hR hpR)).1 rfl
    exact mul_nonpos_of_nonpos_of_nonneg ((hs R).1 hpR) ((hs (insert p R)).2 (by simp))
  linarith only [he,hsum]
end RHTower
