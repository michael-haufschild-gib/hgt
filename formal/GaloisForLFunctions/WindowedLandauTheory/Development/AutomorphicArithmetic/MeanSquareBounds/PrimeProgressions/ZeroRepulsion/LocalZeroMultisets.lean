import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Multiset.Bind

/-! Represent the local zero multiplicities as finite multisets of shifted denominators. -/

open Finset Complex

noncomputable section

namespace QH.PrimeProgressions

def dhFam (Z : Finset ℂ) (m : ℂ → ℕ) (s : ℂ) : Multiset ℂ :=
  Z.val.bind (fun ρ => Multiset.replicate (m ρ) (s - ρ))

theorem dhFam_card (Z : Finset ℂ) (m : ℂ → ℕ) (s : ℂ) :
    (dhFam Z m s).card = ∑ ρ ∈ Z, m ρ := by
  simp only [dhFam, Multiset.card_bind, Function.comp_def, Multiset.card_replicate,
    Finset.sum_eq_multiset_sum]

theorem dhFam_sum {β : Type*} [AddCommMonoid β] (Z : Finset ℂ) (m : ℂ → ℕ) (s : ℂ)
    (f : ℂ → β) : ((dhFam Z m s).map f).sum = ∑ ρ ∈ Z, m ρ • f (s - ρ) := by
  unfold dhFam
  rw [Multiset.map_bind, Multiset.sum_bind, Finset.sum_eq_multiset_sum]
  congr 1
  refine Multiset.map_congr rfl fun ρ _ => ?_
  rw [Multiset.map_replicate, Multiset.sum_replicate]

theorem dhFam_mem (Z : Finset ℂ) (m : ℂ → ℕ) (s ρ : ℂ) (h : ρ ∈ Z) (hm : 1 ≤ m ρ) :
    s - ρ ∈ dhFam Z m s := by
  unfold dhFam
  rw [Multiset.mem_bind]
  exact ⟨ρ, h, Multiset.mem_replicate.2 ⟨by omega, rfl⟩⟩

theorem dhFlat (S : Multiset ℂ) : ∃ (N : ℕ) (w : Fin N → ℂ), Finset.univ.val.map w = S := by
  refine ⟨S.toList.length, S.toList.get, ?_⟩
  rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]

theorem dhFlat_sum {β : Type*} [AddCommMonoid β] {N : ℕ} (w : Fin N → ℂ) (S : Multiset ℂ)
    (h : Finset.univ.val.map w = S) (g : ℂ → β) : ∑ i, g (w i) = (S.map g).sum := by
  rw [← h, Multiset.map_map]
  rfl

end QH.PrimeProgressions
