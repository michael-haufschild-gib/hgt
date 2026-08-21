import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.PollardStepOneMain

/-!
# STEP 2 of Grynkiewicz's proof: deleting an expensive point

If removing a single point of `A` or of `B` decreases `repSum A B t` by at least `t`, then the
weak Pollard bound for the smaller pair implies it for the original pair
(`pollardWeak_of_erase_left`, `pollardWeak_of_erase_right`), because the loss of `t` in `repSum` is
exactly matched by the loss of `t` in `t·#A + t·#B`.

`repSum_erase_le_left` and `repSum_erase_le_right` record that deletion never increases `repSum`,
which is what makes the induction measure decrease.
-/

open scoped Pointwise
open Finset

namespace GaloisForLFunctions.HTGeometry.AddComb

variable {G : Type*} [CommGroup G] [DecidableEq G] [Fintype G]

/-- **STEP 2, weak branch (second factor).**  If deleting a point of `B` costs at least `t` in
`repSum`, the weak Pollard bound transfers from the smaller pair. -/
theorem pollardWeak_of_erase_right (A B : Finset G) (t : ℕ) {y : G} (hy : y ∈ B)
    (hdrop : repSum A (B.erase y) t + t ≤ repSum A B t)
    (hIH : PollardWeak A (B.erase y) t) : PollardWeak A B t := by
  rw [PollardWeak] at hIH ⊢
  have hpos : 1 ≤ B.card := Finset.card_pos.2 ⟨y, hy⟩
  have hcard : B.card = (B.erase y).card + 1 := by
    rw [Finset.card_erase_of_mem hy]
    omega
  have hexp : t * ((B.erase y).card + 1) = t * (B.erase y).card + t := by ring
  rw [hcard]
  omega

/-- **STEP 2, weak branch (first factor).** -/
theorem pollardWeak_of_erase_left (A B : Finset G) (t : ℕ) {x : G} (hx : x ∈ A)
    (hdrop : repSum (A.erase x) B t + t ≤ repSum A B t)
    (hIH : PollardWeak (A.erase x) B t) : PollardWeak A B t := by
  rw [PollardWeak] at hIH ⊢
  have hpos : 1 ≤ A.card := Finset.card_pos.2 ⟨x, hx⟩
  have hcard : A.card = (A.erase x).card + 1 := by
    rw [Finset.card_erase_of_mem hx]
    omega
  have hexp : t * ((A.erase x).card + 1) = t * (A.erase x).card + t := by ring
  rw [hcard]
  omega

/-- Deleting a point never increases `repSum`. -/
theorem repSum_erase_le_right (A B : Finset G) (t : ℕ) (y : G) :
    repSum A (B.erase y) t ≤ repSum A B t :=
  repSum_mono Subset.rfl (Finset.erase_subset y B) t

theorem repSum_erase_le_left (A B : Finset G) (t : ℕ) (x : G) :
    repSum (A.erase x) B t ≤ repSum A B t :=
  repSum_mono (Finset.erase_subset x A) Subset.rfl t

end GaloisForLFunctions.HTGeometry.AddComb
