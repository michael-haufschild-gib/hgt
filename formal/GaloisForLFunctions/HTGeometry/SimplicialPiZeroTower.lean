import GaloisForLFunctions.HTGeometry.SimplicialPiZeroSymmetricAlgebra

/-!
# Transfinite towers of positive cells

The positive-cell theorem is applied stage by stage: a relative cellular presentation attaches a
coproduct of positive relation cells at each stage, and degree zero is unchanged at every stage.
The limit stages need one further fact, that `π₀` commutes with the colimit of the tower — which it
does, being a left adjoint.  What the two facts give together is that the *whole* presentation
preserves degree zero, and that is what this file proves, for a sequential tower.

* `isIso_colimit_ι_zero` : a sequential diagram of isomorphisms has its first term for a colimit.
* `isIso_map_of_isIso_succ` : it is enough that each single step is an isomorphism.
* `simplicialPiZero_isIso_colimit_ι_zero_of_succ` : **a tower of positive-cell attachments
  preserves degree zero.**
-/

namespace GaloisForLFunctions.HTGeometry
open CategoryTheory CategoryTheory.Limits

universe u

section Tower

variable {C : Type*} [Category C] (D : ℕ ⥤ C)
  (hD : ∀ (i j : ℕ) (f : i ⟶ j), IsIso (D.map f))

/-- The comparison isomorphism from the first term of a sequential diagram of isomorphisms. -/
noncomputable def towerIso (n : ℕ) : D.obj 0 ≅ D.obj n :=
  @asIso _ _ _ _ (D.map (homOfLE (Nat.zero_le n))) (hD _ _ _)

theorem towerIso_hom (n : ℕ) : (towerIso D hD n).hom = D.map (homOfLE (Nat.zero_le n)) := rfl

theorem towerIso_hom_comp {n m : ℕ} (f : n ⟶ m) :
    (towerIso D hD n).hom ≫ D.map f = (towerIso D hD m).hom := by
  rw [towerIso_hom, towerIso_hom, ← D.map_comp]
  congr 1

theorem towerIso_zero_hom : (towerIso D hD 0).hom = 𝟙 (D.obj 0) := by
  rw [towerIso_hom, Subsingleton.elim (homOfLE (Nat.zero_le 0)) (𝟙 (0 : ℕ)), D.map_id]

theorem towerIso_zero_inv : (towerIso D hD 0).inv = 𝟙 (D.obj 0) := by
  have h := Iso.inv_hom_id (towerIso D hD 0)
  rw [towerIso_zero_hom, Category.comp_id] at h
  exact h

/-- The comparison cocone maps of a sequential diagram of isomorphisms. -/
noncomputable def towerCoconeι : D ⟶ (Functor.const ℕ).obj (D.obj 0) where
  app := fun n => (towerIso D hD n).inv
  naturality := fun n m f => by
    have h1 : (towerIso D hD n).inv ≫ (towerIso D hD m).hom = D.map f := by
      rw [← towerIso_hom_comp D hD f, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    show D.map f ≫ (towerIso D hD m).inv = (towerIso D hD n).inv ≫ 𝟙 _
    rw [Category.comp_id, ← h1, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The cocone on a sequential diagram of isomorphisms with vertex the first term. -/
noncomputable abbrev towerCocone : Cocone D := ⟨D.obj 0, towerCoconeι D hD⟩

theorem towerCocone_ι_app (n : ℕ) : (towerCocone D hD).ι.app n = (towerIso D hD n).inv := rfl

include hD in
/-- **In a sequential diagram all of whose maps are isomorphisms, the colimit is the first
term.** -/
theorem isIso_colimit_ι_zero [HasColimit D] : IsIso (colimit.ι D 0) := by
  refine ⟨colimit.desc D (towerCocone D hD), ?_, ?_⟩
  · have h0 := colimit.ι_desc (towerCocone D hD) 0
    rw [towerCocone_ι_app, towerIso_zero_inv] at h0
    exact h0
  · refine colimit.hom_ext fun n => ?_
    have h1 := colimit.ι_desc (towerCocone D hD) n
    rw [towerCocone_ι_app] at h1
    rw [← Category.assoc, h1, Category.comp_id, ← colimit.w D (homOfLE (Nat.zero_le n)), ← towerIso_hom D hD n,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end Tower

section TowerSucc

variable {C : Type*} [Category C]

/-- If every step of a sequential diagram is an isomorphism, so is every map of the diagram. -/
theorem isIso_map_of_isIso_succ (D : ℕ ⥤ C)
    (h : ∀ n : ℕ, IsIso (D.map (homOfLE (Nat.le_succ n)))) (i j : ℕ) (f : i ⟶ j) :
    IsIso (D.map f) := by
  have hij : i ≤ j := leOfHom f
  have key : ∀ (m : ℕ) (hm : i ≤ m), IsIso (D.map (homOfLE hm)) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
        rw [Subsingleton.elim (homOfLE (le_refl i)) (𝟙 i), D.map_id]
        infer_instance
    | succ n hn ih =>
        rw [Subsingleton.elim (homOfLE (Nat.le_succ_of_le hn))
          (homOfLE hn ≫ homOfLE (Nat.le_succ n)), D.map_comp]
        haveI := ih
        haveI := h n
        infer_instance
  rw [Subsingleton.elim f (homOfLE hij)]
  exact key j hij

end TowerSucc

/-- **A transfinite tower of positive cells preserves degree zero.** -/
theorem simplicialPiZero_isIso_colimit_ι_zero (A : ℕ ⥤ SimplicialObject CommRingCat.{u})
    (hA : ∀ (i j : ℕ) (f : i ⟶ j), IsIso (simplicialPiZero.map (A.map f))) :
    IsIso (simplicialPiZero.map (colimit.ι A 0)) := by
  haveI hι : IsIso (colimit.ι (A ⋙ simplicialPiZero) 0) :=
    isIso_colimit_ι_zero (A ⋙ simplicialPiZero) (fun i j f => hA i j f)
  haveI : IsIso (simplicialPiZero.map (colimit.ι A 0)
      ≫ (preservesColimitIso simplicialPiZero A).hom) := by
    rw [ι_preservesColimitIso_hom]
    exact hι
  exact IsIso.of_isIso_comp_right _ (preservesColimitIso simplicialPiZero A).hom

/-- **The full positive relative cellular presentation preserves degree zero.** -/
theorem simplicialPiZero_isIso_colimit_ι_zero_of_succ
    (A : ℕ ⥤ SimplicialObject CommRingCat.{u})
    (hA : ∀ n : ℕ, IsIso (simplicialPiZero.map (A.map (homOfLE (Nat.le_succ n))))) :
    IsIso (simplicialPiZero.map (colimit.ι A 0)) :=
  simplicialPiZero_isIso_colimit_ι_zero A
    (fun i j f => isIso_map_of_isIso_succ (A ⋙ simplicialPiZero) (fun n => hA n) i j f)

end GaloisForLFunctions.HTGeometry
