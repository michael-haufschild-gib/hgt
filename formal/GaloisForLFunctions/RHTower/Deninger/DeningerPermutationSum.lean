import GaloisForLFunctions.RHTower.Deninger.DeningerTreeShortExact
import Mathlib.Algebra.Group.Action.Sum

/-!
# Permutation representations of disjoint unions

The permutation representation on a disjoint union of two `G`-sets is the biproduct of the two
permutation representations, and an equivariant bijection induces an isomorphism of permutation
representations.

* `deningerPermLift` : a map of `G`-sets into a permutation representation extends to a linear map.
* `deningerPermRepIsoOfEquiv` : equivariant bijections induce isomorphisms.
* `deningerSumRepIso` : `k[X ⊕ Y] ≅ k[X] ⊞ k[Y]`.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits Representation

universe u

variable (k : Type u) [CommRing k] {G : Type u} [Group G]
  {X X' Y : Type u} [MulAction G X] [MulAction G X'] [MulAction G Y]

/-- The linear map determined by its values on the basis of a permutation representation. -/
noncomputable def deningerPermLift (F : X → MonoidAlgebra k X') :
    MonoidAlgebra k X →ₗ[k] MonoidAlgebra k X' :=
  Finsupp.lift (MonoidAlgebra k X') k X F ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

theorem deningerPermLift_single (F : X → MonoidAlgebra k X') (x : X) (c : k) :
    deningerPermLift k F (MonoidAlgebra.single x c) = c • F x := by
  show Finsupp.lift (MonoidAlgebra k X') k X F (Finsupp.single x c) = _
  rw [Finsupp.lift_apply, Finsupp.sum_single_index (by simp)]

theorem deningerPermLift_ext {f₁ f₂ : MonoidAlgebra k X →ₗ[k] MonoidAlgebra k X'}
    (h : ∀ x : X, f₁ (MonoidAlgebra.single x (1 : k)) =
      f₂ (MonoidAlgebra.single x (1 : k))) : f₁ = f₂ :=
  MonoidAlgebra.lhom_ext' fun x => LinearMap.ext_ring (h x)

/-- A map of `G`-sets extends to a morphism of permutation representations. -/
noncomputable def deningerPermHom (F : X → MonoidAlgebra k X')
    (hF : ∀ (g : G) (x : X),
      F (g • x) = Representation.ofMulAction k G X' g (F x)) :
    Rep.ofMulAction k G X ⟶ Rep.ofMulAction k G X' :=
  Rep.ofHom ⟨deningerPermLift k F, fun g => by
    refine deningerPermLift_ext k fun x => ?_
    show deningerPermLift k F (Representation.ofMulAction k G X g
        (MonoidAlgebra.single x (1 : k))) =
      Representation.ofMulAction k G X' g (deningerPermLift k F (MonoidAlgebra.single x (1 : k)))
    rw [Representation.ofMulAction_single, deningerPermLift_single, deningerPermLift_single,
      one_smul, one_smul, hF]⟩

theorem deningerPermHom_single (F : X → MonoidAlgebra k X')
    (hF : ∀ (g : G) (x : X), F (g • x) = Representation.ofMulAction k G X' g (F x))
    (x : X) (c : k) :
    (deningerPermHom k F hF).hom (MonoidAlgebra.single x c) = c • F x :=
  deningerPermLift_single k F x c

/-- An equivariant bijection induces an isomorphism of permutation representations. -/
noncomputable def deningerPermRepIsoOfEquiv (e : X ≃ X')
    (he : ∀ (g : G) (x : X), e (g • x) = g • e x) :
    Rep.ofMulAction k G X ≅ Rep.ofMulAction k G X' where
  hom := deningerPermHom k (fun x => MonoidAlgebra.single (e x) (1 : k)) (fun g x => by
    rw [Representation.ofMulAction_single, he])
  inv := deningerPermHom k (fun x' => MonoidAlgebra.single (e.symm x') (1 : k)) (fun g x' => by
    rw [Representation.ofMulAction_single]
    congr 1
    exact e.symm_apply_eq.2 (by rw [he, Equiv.apply_symm_apply]))
  hom_inv_id := by
    ext x
    simp [deningerPermHom, deningerPermLift_single]
  inv_hom_id := by
    ext x'
    simp [deningerPermHom, deningerPermLift_single]

section Sum

/-- The inclusion of the first summand. -/
noncomputable def deningerSumInl :
    Rep.ofMulAction k G X ⟶ Rep.ofMulAction k G (X ⊕ Y) :=
  deningerPermHom k (fun x => MonoidAlgebra.single (Sum.inl x : X ⊕ Y) (1 : k))
    (fun (g : G) x => by rw [Representation.ofMulAction_single]; simp)

/-- The inclusion of the second summand. -/
noncomputable def deningerSumInr :
    Rep.ofMulAction k G Y ⟶ Rep.ofMulAction k G (X ⊕ Y) :=
  deningerPermHom k (fun y => MonoidAlgebra.single (Sum.inr y : X ⊕ Y) (1 : k))
    (fun (g : G) y => by rw [Representation.ofMulAction_single]; simp)

/-- The projection to the first summand. -/
noncomputable def deningerSumFst :
    Rep.ofMulAction k G (X ⊕ Y) ⟶ Rep.ofMulAction k G X :=
  deningerPermHom k (Sum.elim (fun x => MonoidAlgebra.single x (1 : k)) (fun _ => 0))
    (fun (g : G) z => by
      cases z with
      | inl x =>
        show Sum.elim (fun x => MonoidAlgebra.single x (1 : k)) (fun _ => 0)
            ((g • Sum.inl x : X ⊕ Y)) = _
        rw [Sum.smul_inl]
        show MonoidAlgebra.single (g • x) (1 : k) =
          Representation.ofMulAction k G X g (MonoidAlgebra.single x (1 : k))
        rw [Representation.ofMulAction_single]
      | inr y =>
        show Sum.elim (fun x => MonoidAlgebra.single x (1 : k)) (fun _ => 0)
            ((g • Sum.inr y : X ⊕ Y)) = _
        rw [Sum.smul_inr]
        show (0 : MonoidAlgebra k X) = Representation.ofMulAction k G X g 0
        rw [map_zero])

/-- The projection to the second summand. -/
noncomputable def deningerSumSnd :
    Rep.ofMulAction k G (X ⊕ Y) ⟶ Rep.ofMulAction k G Y :=
  deningerPermHom k (Sum.elim (fun _ => 0) (fun y => MonoidAlgebra.single y (1 : k)))
    (fun (g : G) z => by
      cases z with
      | inl x =>
        show Sum.elim (fun _ => 0) (fun y => MonoidAlgebra.single y (1 : k))
            ((g • Sum.inl x : X ⊕ Y)) = _
        rw [Sum.smul_inl]
        show (0 : MonoidAlgebra k Y) = Representation.ofMulAction k G Y g 0
        rw [map_zero]
      | inr y =>
        show Sum.elim (fun _ => 0) (fun y => MonoidAlgebra.single y (1 : k))
            ((g • Sum.inr y : X ⊕ Y)) = _
        rw [Sum.smul_inr]
        show MonoidAlgebra.single (g • y) (1 : k) =
          Representation.ofMulAction k G Y g (MonoidAlgebra.single y (1 : k))
        rw [Representation.ofMulAction_single])

theorem deningerSumInl_fst :
    deningerSumInl (X := X) (Y := Y) k ≫ deningerSumFst k = 𝟙 (Rep.ofMulAction k G X) := by
  ext x
  simp [deningerSumInl, deningerSumFst, deningerPermHom, deningerPermLift_single]

theorem deningerSumInl_snd :
    (deningerSumInl k : Rep.ofMulAction k G X ⟶ Rep.ofMulAction k G (X ⊕ Y)) ≫
      deningerSumSnd k = 0 := by
  ext x
  simp [deningerSumInl, deningerSumSnd, deningerPermHom, deningerPermLift_single]

theorem deningerSumInr_fst :
    (deningerSumInr k : Rep.ofMulAction k G Y ⟶ Rep.ofMulAction k G (X ⊕ Y)) ≫
      deningerSumFst k = 0 := by
  ext y
  simp [deningerSumInr, deningerSumFst, deningerPermHom, deningerPermLift_single]

theorem deningerSumInr_snd :
    deningerSumInr (X := X) (Y := Y) k ≫ deningerSumSnd k = 𝟙 (Rep.ofMulAction k G Y) := by
  ext y
  simp [deningerSumInr, deningerSumSnd, deningerPermHom, deningerPermLift_single]

/-- **The permutation representation on a disjoint union is the biproduct.** -/
noncomputable def deningerSumRepIso :
    Rep.ofMulAction k G (X ⊕ Y) ≅
      Rep.ofMulAction k G X ⊞ Rep.ofMulAction k G Y where
  hom := biprod.lift (deningerSumFst k) (deningerSumSnd k)
  inv := biprod.desc (deningerSumInl k) (deningerSumInr k)
  hom_inv_id := by
    rw [biprod.lift_desc]
    ext z
    cases z with
    | inl x =>
      simp [Rep.add_hom, deningerSumInl, deningerSumInr, deningerSumFst, deningerSumSnd,
        deningerPermHom, deningerPermLift_single]
    | inr y =>
      simp [Rep.add_hom, deningerSumInl, deningerSumInr, deningerSumFst, deningerSumSnd,
        deningerPermHom, deningerPermLift_single]
  inv_hom_id := by
    refine biprod.hom_ext' _ _ ?_ ?_ <;> refine biprod.hom_ext _ _ ?_ ?_ <;>
      simp [deningerSumInl_fst, deningerSumInl_snd, deningerSumInr_fst, deningerSumInr_snd]

end Sum

end RHTower
