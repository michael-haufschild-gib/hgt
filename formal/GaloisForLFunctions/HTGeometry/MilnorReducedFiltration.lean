import GaloisForLFunctions.HTGeometry.MilnorDegreeReduction
import GaloisForLFunctions.HTGeometry.MilnorSlotPermutation

/-!
# The reduced form of Milnor's degree filtration

A class of `L_d` is *reduced* when it is a combination of symbols whose first entry has degree at
most `d` and all of whose remaining entries have degree below `d`.  Milnor's degree induction shows
that `L_d` consists exactly of the reduced classes: entries of degree `d` beyond the first are
removed by the division move `twoSlot_polyUnit_reduce`, which strictly lowers the sum of the degrees
of the entries.

* `reducedFiltration` : the group of reduced classes.
* `mem_reducedFiltration_of_forall_lt` : a symbol all of whose entries have degree below `d`.
* `mem_reducedFiltration_of_move` : one distinguished entry may sit anywhere — move it to the front.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {F : Type*} [Field F] {n : ℕ}

/-- Classes of symbols whose first entry has degree at most `d` and whose remaining entries have
degree below `d`. -/
noncomputable def reducedFiltration (d n : ℕ) : AddSubgroup (MilnorKDeg (RatFunc F) n) :=
  AddSubgroup.closure {x | ∃ (b : (RatFunc F)ˣ) (l : List (RatFunc F)ˣ) (h : (b :: l).length = n),
      polyDegLe (F := F) d b ∧ (∀ a ∈ l, polyDegLt (F := F) d a)
        ∧ x = milnorClassDeg (RatFunc F) n ⟨b :: l, h⟩}

theorem mem_reducedFiltration {d : ℕ} {b : (RatFunc F)ˣ} {l : List (RatFunc F)ˣ}
    (h : (b :: l).length = n) (hb : polyDegLe (F := F) d b)
    (hl : ∀ a ∈ l, polyDegLt (F := F) d a) :
    milnorClassDeg (RatFunc F) n ⟨b :: l, h⟩ ∈ reducedFiltration (F := F) d n :=
  AddSubgroup.subset_closure ⟨b, l, h, hb, hl, rfl⟩

/-- A symbol all of whose entries have degree below `d` is reduced. -/
theorem mem_reducedFiltration_of_forall_lt {d : ℕ} {l : List (RatFunc F)ˣ} (h : l.length = n)
    (hn : 1 ≤ n) (hl : ∀ a ∈ l, polyDegLt (F := F) d a) :
    milnorClassDeg (RatFunc F) n ⟨l, h⟩ ∈ reducedFiltration (F := F) d n := by
  cases l with
  | nil =>
      exfalso
      rw [List.length_nil] at h
      omega
  | cons b t =>
      exact mem_reducedFiltration h (polyDegLe_of_polyDegLt (hl b (by simp)))
        (fun a ha => hl a (by simp [ha]))

/-- One distinguished entry may sit anywhere: moving it to the front only changes the sign. -/
theorem mem_reducedFiltration_of_move {d : ℕ} (l₂ l₃ : List (RatFunc F)ˣ) (a : (RatFunc F)ˣ)
    (h : ([] ++ l₂ ++ a :: l₃).length = n)
    (hl₂ : ∀ x ∈ l₂, polyDegLt (F := F) d x) (hl₃ : ∀ x ∈ l₃, polyDegLt (F := F) d x)
    (ha : polyDegLe (F := F) d a) :
    milnorClassDeg (RatFunc F) n ⟨[] ++ l₂ ++ a :: l₃, h⟩ ∈ reducedFiltration (F := F) d n := by
  classical
  rw [milnorClassDeg_move (K := RatFunc F) (n := n) l₂ [] l₃ a h]
  refine AddSubgroup.zsmul_mem _ ?_ _
  have hhead : milnorClassDeg (RatFunc F) n
        ⟨[] ++ a :: (l₂ ++ l₃), length_move [] l₂ l₃ a h⟩
      = milnorClassDeg (RatFunc F) n ⟨a :: (l₂ ++ l₃), by
          have := length_move ([] : List (RatFunc F)ˣ) l₂ l₃ a h
          simpa using this⟩ :=
    congrArg (milnorClassDeg (RatFunc F) n) (Subtype.ext (by simp))
  rw [hhead]
  refine mem_reducedFiltration _ ha ?_
  intro x hx
  rcases List.mem_append.1 hx with h2 | h3
  · exact hl₂ x h2
  · exact hl₃ x h3

end GaloisForLFunctions.HTGeometry
