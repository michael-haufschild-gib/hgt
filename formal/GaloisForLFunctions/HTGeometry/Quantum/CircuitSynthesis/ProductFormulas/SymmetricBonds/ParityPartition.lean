import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-! # The smaller parity class of an open chain -/
namespace GaloisForLFunctions.HTGeometry.BondProducts.Symmetric

/-- One of the two bond parities contains at most half the bonds. -/
theorem shorter_parity (m : ℕ) : ∃ S : Finset (Fin m), 2*S.card ≤ m ∧
    (∀ i∈S, ∀ j∈S, i.val%2=j.val%2) ∧ (∀ i∈Sᶜ, ∀ j∈Sᶜ, i.val%2=j.val%2) := by
  classical
  let E := Finset.univ.filter (fun i : Fin m => i.val%2=0)
  have he (i : Fin m) : i ∈ E ↔ i.val%2=0 := by simp [E]
  have ev : ∀ i∈E, ∀ j∈E, i.val%2=j.val%2 := fun i hi j hj =>
    ((he i).mp hi).trans ((he j).mp hj).symm
  have od : ∀ i∈Eᶜ, ∀ j∈Eᶜ, i.val%2=j.val%2 := by
    intro i hi j hj
    have hi' := (he i).not.mp (Finset.mem_compl.mp hi)
    have hj' := (he j).not.mp (Finset.mem_compl.mp hj)
    omega
  have hcard : E.card+Eᶜ.card=m := by simpa only [Fintype.card_fin] using Finset.card_add_card_compl E
  by_cases h : 2*E.card ≤ m
  · exact ⟨E,h,ev,od⟩
  · exact ⟨Eᶜ,by omega,od,by simpa only [compl_compl] using ev⟩

end GaloisForLFunctions.HTGeometry.BondProducts.Symmetric
