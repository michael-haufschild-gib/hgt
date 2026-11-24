import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Finset.Card

/-! # Independent differences inside the fibers of a finite assignment -/

open Finset
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns
noncomputable section

/-- Choosing one representative per occupied class leaves exactly D−m
independent leaf coordinates. Each element is its representative or one
of the enumerated leaves. -/
theorem enumerate_classes {I J : Type*} [Fintype I] [DecidableEq J] (f : I → J) :
    let m := (univ.image f).card
    ∃ (rep : I → I) (leaf : Fin (Fintype.card I-m) → I),
      (∀ i, f (rep i)=f i) ∧ (∀ i j, f i=f j → rep i=rep j) ∧ Function.Injective leaf ∧
      (∀ i j, rep i≠leaf j) ∧ ∀ i, i=rep i ∨ ∃ j, leaf j=i := by
  classical
  intro m
  let S := univ.image f
  have pre (s : S) : ∃ i, f i=s.val := by
    obtain ⟨i,_,hi⟩ := mem_image.mp s.property
    exact ⟨i,hi⟩
  choose pick hp using pre
  have hinj : Function.Injective pick := fun i j h =>
    Subtype.ext ((hp i).symm.trans ((congrArg f h).trans (hp j)))
  let B := univ.image pick
  have hB : B.card=m := by
    rw [show B.card=(univ : Finset S).card from card_image_of_injective _ hinj,card_univ,Fintype.card_coe]
  have hcard : Fintype.card ↥(Bᶜ)=Fintype.card I-m := by rw [Fintype.card_coe,card_compl,hB]
  let e := (finCongr hcard.symm).trans (Fintype.equivFin ↥(Bᶜ)).symm
  let cl (i : I) : S := ⟨f i,mem_image.mpr ⟨i,mem_univ _,rfl⟩⟩
  let rep (i : I) := pick (cl i)
  let leaf (i : Fin (Fintype.card I-m)) := (e i).val
  refine ⟨rep,leaf,fun i => hp (cl i),fun i j h => congrArg pick (Subtype.ext h),
    Subtype.val_injective.comp e.injective,?_,?_⟩
  · intro i j he
    have hb : rep i∈B := mem_image.mpr ⟨cl i,mem_univ _,rfl⟩
    have hn : leaf j ∉ B := mem_compl.mp (e j).property
    exact hn (he ▸ hb)
  · intro i
    by_cases h : i∈B
    · obtain ⟨b,_,hb⟩ := mem_image.mp h
      have he : cl i=b := Subtype.ext (hb ▸ hp b)
      exact Or.inl (by change i=pick (cl i); rw [he,hb])
    · let u : ↥(Bᶜ) := ⟨i,mem_compl.mpr h⟩
      exact Or.inr ⟨e.symm u,congrArg Subtype.val (e.apply_symm_apply u)⟩

/-- Any assignment to at most m centers yields a star forest with as many
edges as the desired lower bound allows, even if some centers are unused. -/
theorem extract_class_forest {I J : Type*} [Fintype I] [DecidableEq J]
    (f : I → J) (r : ℕ) (hr : r+(univ.image f).card ≤ Fintype.card I) :
    ∃ (leaf root : Fin r → I), Function.Injective leaf ∧ (∀ i j, root i≠leaf j) ∧
      ∀ i, f (leaf i)=f (root i) := by
  obtain ⟨rep,l,hf,_,hi,hd,_⟩ := enumerate_classes f
  let e : Fin r ↪ Fin (Fintype.card I-(univ.image f).card) := Fin.castLEEmb (by omega)
  exact ⟨l ∘ e,fun i => rep (l (e i)),hi.comp e.injective,fun i j => hd _ _,fun i => (hf _).symm⟩

#print axioms enumerate_classes
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns
