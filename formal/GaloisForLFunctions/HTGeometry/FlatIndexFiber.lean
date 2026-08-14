import GaloisForLFunctions.HTGeometry.FamilyJetFlattening

/-!
# The fibres of a flattened exponent profile

Flattening an exponent profile `e` on a finite variable type produces a slot tuple in which the
variable `j` occupies exactly `e j` slots.  Reading the profile back off the slot tuple is what
identifies the jet monomial a flattened split came from.
-/

open Finset

namespace GaloisForLFunctions

noncomputable section

/-- **The flattening has fibres of the prescribed sizes.**  The variable `j` occupies exactly
`e j` slots. -/
theorem card_filter_flatIndex {σ : Type*} [Fintype σ] [DecidableEq σ] (e : σ → ℕ) (j : σ) :
    (Finset.univ.filter (fun t : Fin (∑ j', e j') => flatIndex e t = j)).card = e j := by
  classical
  have hcard : Fintype.card (Σ j' : σ, Fin (e j')) = ∑ j', e j' := by
    rw [Fintype.card_sigma]; simp
  set eqv := (Fintype.equivFinOfCardEq hcard).symm with heqv
  have hfl : ∀ t : Fin (∑ j', e j'), flatIndex e t = (eqv t).1 := fun _ => rfl
  rw [Finset.card_filter]
  rw [Finset.sum_congr rfl (fun t (_ : t ∈ Finset.univ) => by rw [hfl t])]
  rw [Equiv.sum_comp eqv (fun p : Σ j' : σ, Fin (e j') => if p.1 = j then 1 else 0)]
  rw [Fintype.sum_sigma]
  have hinner : ∀ j' : σ,
      (∑ _x : Fin (e j'), if j' = j then (1 : ℕ) else 0) = if j' = j then e j' else 0 := by
    intro j'
    by_cases hj : j' = j
    · simp [hj]
    · simp [hj]
  rw [Finset.sum_congr rfl (fun j' (_ : j' ∈ Finset.univ) => hinner j')]
  rw [Finset.sum_ite_eq' Finset.univ j (fun j' => e j'), if_pos (Finset.mem_univ j)]

end

end GaloisForLFunctions
