import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Linarith

/-! # When the unit-separated record counts exactly the true component entries -/
open Set
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents
noncomputable section

/-- A physical entry is a visit with a nonempty preceding open interval
of absence. Endpoint-only contacts are included. -/
def Entry (E : Set ℝ) (u : ℝ) : Prop :=
  u ∈ E ∧ ∃ δ : ℝ, 0<δ ∧ ∀ z ∈ Ioo (u-δ) u, z ∉ E

/-- From the first recorded visit onward, each new record adds exactly
one true entry. The observation origin can be outside the visit set. -/
theorem record_count (E : Set ℝ) (a : ℝ) (F : ℝ → Finset ℝ) (t : ℕ → ℝ)
    (hor : t 0 = a) (hrec : ∀ j, IsLeast {v | t j+1 ≤ v ∧ v ∈ E} (t (j+1)))
    (hunit : ∀ v ∈ E, v+1 ∉ E) (hgap : ∀ v ∈ E, ∀ w, Entry E w → v<w → 1<w-v)
    (hF : ∀ u T, u ∈ F T ↔ a<u ∧ u≤T ∧ Entry E u) (k : ℕ) :
    (F (t (k+1))).card = (F (t 1)).card+k := by
  classical
  have hsucc (j : ℕ) : t j<t (j+1) := by linarith only [(hrec j).1.1]
  have hmono : StrictMono t := strictMono_nat_of_lt_succ hsucc
  induction k with
  | zero => simp only [Nat.zero_add,Nat.add_zero]
  | succ k ih =>
    let j := k+1
    have hv : t j ∈ E := (hrec k).1.2
    have hnext := hrec j
    have hstrict : t j+1 < t (j+1) :=
      lt_of_le_of_ne hnext.1.1 (fun hh => hunit _ hv (hh.symm ▸ hnext.1.2))
    have hentry : Entry E (t (j+1)) := by
      refine ⟨hnext.1.2,t (j+1)-(t j+1),sub_pos.mpr hstrict,?_⟩
      intro u hu he
      exact hu.2.not_ge (hnext.2 ⟨by linarith only [hu.1],he⟩)
    have hadd : F (t (j+1)) = insert (t (j+1)) (F (t j)) := by
      ext u
      rw [hF,Finset.mem_insert,hF]
      constructor
      · rintro ⟨ha,hup,he⟩
        by_cases hu : u≤t j
        · exact Or.inr ⟨ha,hu,he⟩
        · have hg := hgap _ hv _ he (lt_of_not_ge hu)
          exact Or.inl (le_antisymm hup (hnext.2 ⟨by linarith only [hg],he.1⟩))
      · rintro (rfl|⟨ha,hu,he⟩)
        · exact ⟨hor ▸ hmono (Nat.zero_lt_succ _),le_rfl,hentry⟩
        · exact ⟨ha,hu.trans (hsucc j).le,he⟩
    have hnot : t (j+1) ∉ F (t j) := fun h => (hsucc j).not_ge ((hF ..).1 h).2.1
    change (F (t (j+1))).card = _
    rw [hadd,Finset.card_insert_of_notMem hnot]
    dsimp only [j]
    omega

end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents
