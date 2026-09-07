import Mathlib.Data.Finset.Card
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic
/-!
# Finite energy-controlled partial orders

A safe unused element at every smaller selected subset produces a distinct
partial order whose every prefix stays below the initial energy.
-/

noncomputable section
open Finset
namespace RHTower

/-- A safe unused element at every smaller subset produces a distinct partial order under the initial energy. -/
theorem exists_partialSubsetEnergyOrder {α : Type*} [DecidableEq α]
    (F : Finset α → ℝ) (U : Finset α) (n : ℕ)
    (hstep : ∀ L⊆U,L.card<n → ∃ p∈U,p∉L ∧ F (insert p L)≤F L) :
    ∃ l : List α,l.Nodup ∧ l.length=n ∧ l.toFinset⊆U ∧
      ∀ k : ℕ,F (l.take k).toFinset≤F ∅ := by
  induction n with
  | zero => exact ⟨[],by simp,by simp,by simp,by simp⟩
  | succ n ih =>
    obtain ⟨l,hnd,hlen,hsub,hbound⟩ := ih (fun L hL hc => hstep L hL (by omega))
    obtain ⟨p,hp,hpn,hE⟩ := hstep l.toFinset hsub (by
      rw [List.toFinset_card_of_nodup hnd,hlen]; omega)
    have hpnot : p∉l := by simpa using hpn
    have hnd' : (l++[p]).Nodup := by
      rw [List.nodup_append_comm]
      simpa using List.nodup_cons.mpr ⟨hpnot,hnd⟩
    refine ⟨l++[p],hnd',by simp [hlen],?_,?_⟩
    · simpa using insert_subset hp hsub
    · intro k
      by_cases hk : k≤l.length
      · rw [List.take_append_of_le_length hk]
        exact hbound k
      · have hlong : (l++[p]).length≤k := by simp only [List.length_append,List.length_singleton]; omega
        rw [List.take_of_length_le hlong]
        have hh : F l.toFinset≤F ∅ := by simpa using hbound l.length
        simpa using hE.trans hh

end RHTower
