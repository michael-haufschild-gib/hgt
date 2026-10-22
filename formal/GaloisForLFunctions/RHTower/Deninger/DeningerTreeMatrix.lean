import GaloisForLFunctions.RHTower.Deninger.DeningerShear
import GaloisForLFunctions.RHTower.Deninger.DeningerTreeTwoFactor

/-!
# The boundary of the tree in coordinates

Transported through the decomposition of the edge and vertex representations of a two factor
amalgam, the boundary of the tree is a matrix.  Its first column meets the base cosets by the
identity, and so does its second, which is why the map has to be sheared before it is triangular.

* `deningerTreeMatrix` : the boundary in coordinates.
* `deningerEdgeIso_inl`, `deningerEdgeIso_inr`, `deningerVertexIso_fst` : the coordinates.
* `deningerTreeMatrix_inl_fst`, `deningerTreeMatrix_inr_fst` : both columns meet the base cosets by
  minus the identity.
* `deningerTreeMatrix_sub_fst` : their difference does not meet the base cosets.
* `deningerTreeMatrix_sub_snd_fst`, `deningerTreeMatrix_sub_snd_snd` : their difference meets each
  factor by the coset projection.
-/

namespace RHTower

open Monoid Monoid.PushoutI CategoryTheory CategoryTheory.Limits

universe u

variable {G : ULift.{u} Bool → Type u} {H : Type u} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} (k : Type u) [CommRing k]

/-- The boundary of the tree, in the coordinates of the two factor decomposition. -/
noncomputable def deningerTreeMatrix :
    (Rep.ofMulAction k (PushoutI φ) (PushoutI φ ⧸ (PushoutI.base φ).range) ⊞
      Rep.ofMulAction k (PushoutI φ) (PushoutI φ ⧸ (PushoutI.base φ).range)) ⟶
    (Rep.ofMulAction k (PushoutI φ) (PushoutI φ ⧸ (PushoutI.base φ).range) ⊞
      (Rep.ofMulAction k (PushoutI φ)
          (PushoutI φ ⧸ (PushoutI.of (φ := φ) (ULift.up true)).range) ⊞
        Rep.ofMulAction k (PushoutI φ)
          (PushoutI φ ⧸ (PushoutI.of (φ := φ) (ULift.up false)).range))) :=
  (deningerTreeEdgeRepIso (φ := φ) k).inv ≫ deningerTreeBoundaryHom (φ := φ) k ≫
    (deningerTreeVertexRepIso (φ := φ) k).hom

/-- The first edge family, in coordinates. -/
theorem deningerEdgeIso_inl :
    biprod.inl ≫ (deningerTreeEdgeRepIso (φ := φ) k).inv =
      deningerSumInl k ≫ (deningerPermRepIsoOfEquiv k (deningerEdgeEquivSum (φ := φ))
        deningerEdgeEquivSum_smul).inv := by
  rw [deningerTreeEdgeRepIso, Iso.trans_inv, ← Category.assoc]
  congr 1
  exact biprod.inl_desc _ _

/-- The second edge family, in coordinates. -/
theorem deningerEdgeIso_inr :
    biprod.inr ≫ (deningerTreeEdgeRepIso (φ := φ) k).inv =
      deningerSumInr k ≫ (deningerPermRepIsoOfEquiv k (deningerEdgeEquivSum (φ := φ))
        deningerEdgeEquivSum_smul).inv := by
  rw [deningerTreeEdgeRepIso, Iso.trans_inv, ← Category.assoc]
  congr 1
  exact biprod.inr_desc _ _

/-- The base vertices, in coordinates. -/
theorem deningerVertexIso_fst :
    (deningerTreeVertexRepIso (φ := φ) k).hom ≫ biprod.fst =
      (deningerPermRepIsoOfEquiv k (deningerVertexEquivSum (φ := φ))
        deningerVertexEquivSum_smul).hom ≫ deningerSumFst k := by
  rw [deningerTreeVertexRepIso, Iso.trans_hom, Iso.trans_hom, Category.assoc, Category.assoc]
  congr 1
  rw [biprod.mapIso_hom, biprod.map_fst, Iso.refl_hom, Category.comp_id]
  exact biprod.lift_fst _ _

section Basis

variable {X X' Y : Type u} [MulAction (PushoutI φ) X] [MulAction (PushoutI φ) X']
  [MulAction (PushoutI φ) Y]

theorem deningerPermIso_hom_single (e : X ≃ X')
    (he : ∀ (g : PushoutI φ) (x : X), e (g • x) = g • e x) (x : X) :
    (deningerPermRepIsoOfEquiv k e he).hom.hom (MonoidAlgebra.single x (1 : k)) =
      MonoidAlgebra.single (e x) (1 : k) := by
  show deningerPermLift k _ (MonoidAlgebra.single x (1 : k)) = _
  rw [deningerPermLift_single, one_smul]

theorem deningerPermIso_inv_single (e : X ≃ X')
    (he : ∀ (g : PushoutI φ) (x : X), e (g • x) = g • e x) (x' : X') :
    (deningerPermRepIsoOfEquiv k e he).inv.hom (MonoidAlgebra.single x' (1 : k)) =
      MonoidAlgebra.single (e.symm x') (1 : k) := by
  show deningerPermLift k _ (MonoidAlgebra.single x' (1 : k)) = _
  rw [deningerPermLift_single, one_smul]

theorem deningerSumInl_single (x : X) :
    (deningerSumInl (G := PushoutI φ) (X := X) (Y := Y) k).hom
        (MonoidAlgebra.single x (1 : k)) =
      MonoidAlgebra.single (Sum.inl x : X ⊕ Y) (1 : k) := by
  show deningerPermLift k _ (MonoidAlgebra.single x (1 : k)) = _
  rw [deningerPermLift_single, one_smul]

theorem deningerSumInr_single (y : Y) :
    (deningerSumInr (G := PushoutI φ) (X := X) (Y := Y) k).hom
        (MonoidAlgebra.single y (1 : k)) =
      MonoidAlgebra.single (Sum.inr y : X ⊕ Y) (1 : k) := by
  show deningerPermLift k _ (MonoidAlgebra.single y (1 : k)) = _
  rw [deningerPermLift_single, one_smul]

theorem deningerSumSnd_single_inl (x : X) :
    (deningerSumSnd (G := PushoutI φ) (X := X) (Y := Y) k).hom
        (MonoidAlgebra.single (Sum.inl x : X ⊕ Y) (1 : k)) = 0 := by
  show deningerPermLift k _ (MonoidAlgebra.single (Sum.inl x : X ⊕ Y) (1 : k)) = _
  rw [deningerPermLift_single, one_smul]
  rfl

theorem deningerSumSnd_single_inr (y : Y) :
    (deningerSumSnd (G := PushoutI φ) (X := X) (Y := Y) k).hom
        (MonoidAlgebra.single (Sum.inr y : X ⊕ Y) (1 : k)) =
      MonoidAlgebra.single y (1 : k) := by
  show deningerPermLift k _ (MonoidAlgebra.single (Sum.inr y : X ⊕ Y) (1 : k)) = _
  rw [deningerPermLift_single, one_smul]
  rfl

theorem deningerSumFst_single_inl (x : X) :
    (deningerSumFst (G := PushoutI φ) (X := X) (Y := Y) k).hom
        (MonoidAlgebra.single (Sum.inl x : X ⊕ Y) (1 : k)) =
      MonoidAlgebra.single x (1 : k) := by
  show deningerPermLift k _ (MonoidAlgebra.single (Sum.inl x : X ⊕ Y) (1 : k)) = _
  rw [deningerPermLift_single, one_smul]
  rfl

theorem deningerSumFst_single_inr (y : Y) :
    (deningerSumFst (G := PushoutI φ) (X := X) (Y := Y) k).hom
        (MonoidAlgebra.single (Sum.inr y : X ⊕ Y) (1 : k)) = 0 := by
  show deningerPermLift k _ (MonoidAlgebra.single (Sum.inr y : X ⊕ Y) (1 : k)) = _
  rw [deningerPermLift_single, one_smul]
  rfl

end Basis

/-- **The first column of the boundary meets the base cosets by minus the identity.** -/
theorem deningerTreeMatrix_inl_fst :
    biprod.inl ≫ deningerTreeMatrix (φ := φ) k ≫ biprod.fst = -𝟙 _ := by
  rw [deningerTreeMatrix, ← Category.assoc, ← Category.assoc, deningerEdgeIso_inl,
    Category.assoc, Category.assoc, Category.assoc, deningerVertexIso_fst]
  refine Rep.hom_ext (Representation.IntertwiningMap.ext
    (MonoidAlgebra.lhom_ext' fun x => LinearMap.ext_ring ?_))
  show (deningerSumFst k).hom ((deningerPermRepIsoOfEquiv k (deningerVertexEquivSum (φ := φ))
      deningerVertexEquivSum_smul).hom.hom ((deningerTreeBoundaryHom (φ := φ) k).hom
      ((deningerPermRepIsoOfEquiv k (deningerEdgeEquivSum (φ := φ))
        deningerEdgeEquivSum_smul).inv.hom
        ((deningerSumInl k).hom (MonoidAlgebra.single x (1 : k)))))) = _
  rw [deningerSumInl_single, deningerPermIso_inv_single]
  show (deningerSumFst k).hom ((deningerPermRepIsoOfEquiv k (deningerVertexEquivSum (φ := φ))
      deningerVertexEquivSum_smul).hom.hom (deningerTreeBoundary k
      (MonoidAlgebra.single (⟨ULift.up true, x⟩ : DeningerTreeEdge φ) (1 : k)))) = _
  rw [deningerTreeBoundary_single, one_smul, map_sub, map_sub,
    deningerPermIso_hom_single, deningerPermIso_hom_single]
  show (deningerSumFst k).hom (MonoidAlgebra.single
      (Sum.inr (Sum.inl (deningerEdgeHead (ULift.up true) x))) (1 : k)) -
    (deningerSumFst k).hom (MonoidAlgebra.single (Sum.inl x) (1 : k)) = _
  rw [deningerSumFst_single_inr, deningerSumFst_single_inl, zero_sub]
  rfl

/-- **The second column of the boundary also meets the base cosets by minus the identity.** -/
theorem deningerTreeMatrix_inr_fst :
    biprod.inr ≫ deningerTreeMatrix (φ := φ) k ≫ biprod.fst = -𝟙 _ := by
  rw [deningerTreeMatrix, ← Category.assoc, ← Category.assoc, deningerEdgeIso_inr,
    Category.assoc, Category.assoc, Category.assoc, deningerVertexIso_fst]
  refine Rep.hom_ext (Representation.IntertwiningMap.ext
    (MonoidAlgebra.lhom_ext' fun x => LinearMap.ext_ring ?_))
  show (deningerSumFst k).hom ((deningerPermRepIsoOfEquiv k (deningerVertexEquivSum (φ := φ))
      deningerVertexEquivSum_smul).hom.hom ((deningerTreeBoundaryHom (φ := φ) k).hom
      ((deningerPermRepIsoOfEquiv k (deningerEdgeEquivSum (φ := φ))
        deningerEdgeEquivSum_smul).inv.hom
        ((deningerSumInr k).hom (MonoidAlgebra.single x (1 : k)))))) = _
  rw [deningerSumInr_single, deningerPermIso_inv_single]
  show (deningerSumFst k).hom ((deningerPermRepIsoOfEquiv k (deningerVertexEquivSum (φ := φ))
      deningerVertexEquivSum_smul).hom.hom (deningerTreeBoundary k
      (MonoidAlgebra.single (⟨ULift.up false, x⟩ : DeningerTreeEdge φ) (1 : k)))) = _
  rw [deningerTreeBoundary_single, one_smul, map_sub, map_sub,
    deningerPermIso_hom_single, deningerPermIso_hom_single]
  show (deningerSumFst k).hom (MonoidAlgebra.single
      (Sum.inr (Sum.inr (deningerEdgeHead (ULift.up false) x))) (1 : k)) -
    (deningerSumFst k).hom (MonoidAlgebra.single (Sum.inl x) (1 : k)) = _
  rw [deningerSumFst_single_inr, deningerSumFst_single_inl, zero_sub]
  rfl

/-- **The difference of the two columns does not meet the base cosets.** -/
theorem deningerTreeMatrix_sub_fst :
    (biprod.inr - biprod.inl) ≫ deningerTreeMatrix (φ := φ) k ≫ biprod.fst = 0 := by
  rw [Preadditive.sub_comp, deningerTreeMatrix_inr_fst, deningerTreeMatrix_inl_fst, sub_self]

/-- The first factor vertices, in coordinates. -/
theorem deningerVertexIso_snd_fst :
    (deningerTreeVertexRepIso (φ := φ) k).hom ≫ biprod.snd ≫ biprod.fst =
      (deningerPermRepIsoOfEquiv k (deningerVertexEquivSum (φ := φ))
        deningerVertexEquivSum_smul).hom ≫ deningerSumSnd k ≫ deningerSumFst k := by
  have h1 : ∀ {X Y : Type u} [MulAction (PushoutI φ) X] [MulAction (PushoutI φ) Y],
      (deningerSumRepIso (G := PushoutI φ) (X := X) (Y := Y) k).hom ≫ biprod.fst =
        deningerSumFst k := fun {_ _} _ _ => biprod.lift_fst _ _
  have h2 : ∀ {X Y : Type u} [MulAction (PushoutI φ) X] [MulAction (PushoutI φ) Y],
      (deningerSumRepIso (G := PushoutI φ) (X := X) (Y := Y) k).hom ≫ biprod.snd =
        deningerSumSnd k := fun {_ _} _ _ => biprod.lift_snd _ _
  rw [deningerTreeVertexRepIso, Iso.trans_hom, Iso.trans_hom]
  simp only [Category.assoc]
  congr 1
  rw [biprod.mapIso_hom, ← Category.assoc (biprod.map _ _), biprod.map_snd, Category.assoc, h1,
    ← Category.assoc, h2]

/-- The head of an edge is the projection of cosets. -/
theorem deningerEdgeHead_eq_projMap (i : ULift.{u} Bool) :
    deningerEdgeHead (φ := φ) i = deningerCosetProjMap (deningerBaseRange_le φ i) := by
  funext x
  induction x using QuotientGroup.induction_on with
  | H g => rfl

/-- **The difference of the two columns meets the first factor by the coset projection.** -/
theorem deningerTreeMatrix_sub_snd_fst :
    (biprod.inr - biprod.inl) ≫ deningerTreeMatrix (φ := φ) k ≫ biprod.snd ≫ biprod.fst =
      -deningerCosetProj k (deningerBaseRange_le φ (ULift.up true)) := by
  have hinl : biprod.inl ≫ deningerTreeMatrix (φ := φ) k ≫ biprod.snd ≫ biprod.fst =
      deningerCosetProj k (deningerBaseRange_le φ (ULift.up true)) := by
    rw [deningerTreeMatrix]
    simp only [Category.assoc]
    rw [← Category.assoc biprod.inl, deningerEdgeIso_inl]
    simp only [Category.assoc]
    rw [deningerVertexIso_snd_fst]
    refine Rep.hom_ext (Representation.IntertwiningMap.ext
      (MonoidAlgebra.lhom_ext' fun x => LinearMap.ext_ring ?_))
    show (deningerSumFst k).hom ((deningerSumSnd k).hom
      ((deningerPermRepIsoOfEquiv k (deningerVertexEquivSum (φ := φ))
        deningerVertexEquivSum_smul).hom.hom ((deningerTreeBoundaryHom (φ := φ) k).hom
        ((deningerPermRepIsoOfEquiv k (deningerEdgeEquivSum (φ := φ))
          deningerEdgeEquivSum_smul).inv.hom
          ((deningerSumInl k).hom (MonoidAlgebra.single x (1 : k))))))) = _
    rw [deningerSumInl_single, deningerPermIso_inv_single]
    show (deningerSumFst k).hom ((deningerSumSnd k).hom
      ((deningerPermRepIsoOfEquiv k (deningerVertexEquivSum (φ := φ))
        deningerVertexEquivSum_smul).hom.hom (deningerTreeBoundary k
        (MonoidAlgebra.single (⟨ULift.up true, x⟩ : DeningerTreeEdge φ) (1 : k))))) = _
    rw [deningerTreeBoundary_single, one_smul, map_sub, map_sub, map_sub,
      deningerPermIso_hom_single, deningerPermIso_hom_single]
    show (deningerSumFst k).hom ((deningerSumSnd k).hom (MonoidAlgebra.single
        (Sum.inr (Sum.inl (deningerEdgeHead (ULift.up true) x))) (1 : k))) -
      (deningerSumFst k).hom ((deningerSumSnd k).hom
        (MonoidAlgebra.single (Sum.inl x) (1 : k))) = _
    rw [deningerSumSnd_single_inr, deningerSumSnd_single_inl, map_zero,
      deningerSumFst_single_inl, sub_zero, deningerEdgeHead_eq_projMap]
    show _ = deningerPermLift k _ (MonoidAlgebra.single x (1 : k))
    rw [deningerPermLift_single, one_smul]
  have hinr : biprod.inr ≫ deningerTreeMatrix (φ := φ) k ≫ biprod.snd ≫ biprod.fst = 0 := by
    rw [deningerTreeMatrix]
    simp only [Category.assoc]
    rw [← Category.assoc biprod.inr, deningerEdgeIso_inr]
    simp only [Category.assoc]
    rw [deningerVertexIso_snd_fst]
    refine Rep.hom_ext (Representation.IntertwiningMap.ext
      (MonoidAlgebra.lhom_ext' fun x => LinearMap.ext_ring ?_))
    show (deningerSumFst k).hom ((deningerSumSnd k).hom
      ((deningerPermRepIsoOfEquiv k (deningerVertexEquivSum (φ := φ))
        deningerVertexEquivSum_smul).hom.hom ((deningerTreeBoundaryHom (φ := φ) k).hom
        ((deningerPermRepIsoOfEquiv k (deningerEdgeEquivSum (φ := φ))
          deningerEdgeEquivSum_smul).inv.hom
          ((deningerSumInr k).hom (MonoidAlgebra.single x (1 : k))))))) = _
    rw [deningerSumInr_single, deningerPermIso_inv_single]
    show (deningerSumFst k).hom ((deningerSumSnd k).hom
      ((deningerPermRepIsoOfEquiv k (deningerVertexEquivSum (φ := φ))
        deningerVertexEquivSum_smul).hom.hom (deningerTreeBoundary k
        (MonoidAlgebra.single (⟨ULift.up false, x⟩ : DeningerTreeEdge φ) (1 : k))))) = _
    rw [deningerTreeBoundary_single, one_smul, map_sub, map_sub, map_sub,
      deningerPermIso_hom_single, deningerPermIso_hom_single]
    show (deningerSumFst k).hom ((deningerSumSnd k).hom (MonoidAlgebra.single
        (Sum.inr (Sum.inr (deningerEdgeHead (ULift.up false) x))) (1 : k))) -
      (deningerSumFst k).hom ((deningerSumSnd k).hom
        (MonoidAlgebra.single (Sum.inl x) (1 : k))) = _
    rw [deningerSumSnd_single_inr, deningerSumSnd_single_inl, map_zero,
      deningerSumFst_single_inr, sub_zero]
    rfl
  rw [Preadditive.sub_comp, hinl, hinr, zero_sub]

/-- The second factor vertices, in coordinates. -/
theorem deningerVertexIso_snd_snd :
    (deningerTreeVertexRepIso (φ := φ) k).hom ≫ biprod.snd ≫ biprod.snd =
      (deningerPermRepIsoOfEquiv k (deningerVertexEquivSum (φ := φ))
        deningerVertexEquivSum_smul).hom ≫ deningerSumSnd k ≫ deningerSumSnd k := by
  have h2 : ∀ {X Y : Type u} [MulAction (PushoutI φ) X] [MulAction (PushoutI φ) Y],
      (deningerSumRepIso (G := PushoutI φ) (X := X) (Y := Y) k).hom ≫ biprod.snd =
        deningerSumSnd k := fun {_ _} _ _ => biprod.lift_snd _ _
  rw [deningerTreeVertexRepIso, Iso.trans_hom, Iso.trans_hom]
  simp only [Category.assoc]
  congr 1
  rw [biprod.mapIso_hom, ← Category.assoc (biprod.map _ _), biprod.map_snd, Category.assoc, h2,
    ← Category.assoc, h2]

/-- **The difference of the two columns meets the second factor by the coset projection.** -/
theorem deningerTreeMatrix_sub_snd_snd :
    (biprod.inr - biprod.inl) ≫ deningerTreeMatrix (φ := φ) k ≫ biprod.snd ≫ biprod.snd =
      deningerCosetProj k (deningerBaseRange_le φ (ULift.up false)) := by
  have hinr : biprod.inr ≫ deningerTreeMatrix (φ := φ) k ≫ biprod.snd ≫ biprod.snd =
      deningerCosetProj k (deningerBaseRange_le φ (ULift.up false)) := by
    rw [deningerTreeMatrix]
    simp only [Category.assoc]
    rw [← Category.assoc biprod.inr, deningerEdgeIso_inr]
    simp only [Category.assoc]
    rw [deningerVertexIso_snd_snd]
    refine Rep.hom_ext (Representation.IntertwiningMap.ext
      (MonoidAlgebra.lhom_ext' fun x => LinearMap.ext_ring ?_))
    show (deningerSumSnd k).hom ((deningerSumSnd k).hom
      ((deningerPermRepIsoOfEquiv k (deningerVertexEquivSum (φ := φ))
        deningerVertexEquivSum_smul).hom.hom ((deningerTreeBoundaryHom (φ := φ) k).hom
        ((deningerPermRepIsoOfEquiv k (deningerEdgeEquivSum (φ := φ))
          deningerEdgeEquivSum_smul).inv.hom
          ((deningerSumInr k).hom (MonoidAlgebra.single x (1 : k))))))) = _
    rw [deningerSumInr_single, deningerPermIso_inv_single]
    show (deningerSumSnd k).hom ((deningerSumSnd k).hom
      ((deningerPermRepIsoOfEquiv k (deningerVertexEquivSum (φ := φ))
        deningerVertexEquivSum_smul).hom.hom (deningerTreeBoundary k
        (MonoidAlgebra.single (⟨ULift.up false, x⟩ : DeningerTreeEdge φ) (1 : k))))) = _
    rw [deningerTreeBoundary_single, one_smul, map_sub, map_sub, map_sub,
      deningerPermIso_hom_single, deningerPermIso_hom_single]
    show (deningerSumSnd k).hom ((deningerSumSnd k).hom (MonoidAlgebra.single
        (Sum.inr (Sum.inr (deningerEdgeHead (ULift.up false) x))) (1 : k))) -
      (deningerSumSnd k).hom ((deningerSumSnd k).hom
        (MonoidAlgebra.single (Sum.inl x) (1 : k))) = _
    rw [deningerSumSnd_single_inr, deningerSumSnd_single_inl, map_zero,
      deningerSumSnd_single_inr, sub_zero, deningerEdgeHead_eq_projMap]
    show _ = deningerPermLift k _ (MonoidAlgebra.single x (1 : k))
    rw [deningerPermLift_single, one_smul]
  have hinl : biprod.inl ≫ deningerTreeMatrix (φ := φ) k ≫ biprod.snd ≫ biprod.snd = 0 := by
    rw [deningerTreeMatrix]
    simp only [Category.assoc]
    rw [← Category.assoc biprod.inl, deningerEdgeIso_inl]
    simp only [Category.assoc]
    rw [deningerVertexIso_snd_snd]
    refine Rep.hom_ext (Representation.IntertwiningMap.ext
      (MonoidAlgebra.lhom_ext' fun x => LinearMap.ext_ring ?_))
    show (deningerSumSnd k).hom ((deningerSumSnd k).hom
      ((deningerPermRepIsoOfEquiv k (deningerVertexEquivSum (φ := φ))
        deningerVertexEquivSum_smul).hom.hom ((deningerTreeBoundaryHom (φ := φ) k).hom
        ((deningerPermRepIsoOfEquiv k (deningerEdgeEquivSum (φ := φ))
          deningerEdgeEquivSum_smul).inv.hom
          ((deningerSumInl k).hom (MonoidAlgebra.single x (1 : k))))))) = _
    rw [deningerSumInl_single, deningerPermIso_inv_single]
    show (deningerSumSnd k).hom ((deningerSumSnd k).hom
      ((deningerPermRepIsoOfEquiv k (deningerVertexEquivSum (φ := φ))
        deningerVertexEquivSum_smul).hom.hom (deningerTreeBoundary k
        (MonoidAlgebra.single (⟨ULift.up true, x⟩ : DeningerTreeEdge φ) (1 : k))))) = _
    rw [deningerTreeBoundary_single, one_smul, map_sub, map_sub, map_sub,
      deningerPermIso_hom_single, deningerPermIso_hom_single]
    show (deningerSumSnd k).hom ((deningerSumSnd k).hom (MonoidAlgebra.single
        (Sum.inr (Sum.inl (deningerEdgeHead (ULift.up true) x))) (1 : k))) -
      (deningerSumSnd k).hom ((deningerSumSnd k).hom
        (MonoidAlgebra.single (Sum.inl x) (1 : k))) = _
    rw [deningerSumSnd_single_inr, deningerSumSnd_single_inl, deningerSumSnd_single_inl,
      map_zero, sub_zero]
    rfl
  rw [Preadditive.sub_comp, hinl, hinr, sub_zero]

end RHTower
