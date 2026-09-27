import GaloisForLFunctions.HTGeometry.SchemeStalkPoints
import Mathlib.RingTheory.DualNumber

/-!
# Infinitesimal lifts of points and the group law

For a field `L` over `C` and an `L`-module `M`, the square-zero extension `L ⊕ M` is a local ring.
A point `w` of a `C`-scheme with values in `L ⊕ M` lifting a stalk point `stalkPoint x φ` is again a
stalk point at `x`, given by a homomorphism `ψ : O_x → L ⊕ M` with first component `φ`; its second
component is a `φ`-derivation.

For a group scheme the group law on lifts is addition of these derivations: if `w₁` lifts `p₁`
and `w₂` lifts `p₂`, the derivation of `w₁ w₂` (a lift of `p₁ p₂`) is the sum of the derivations of
`w₁ · p₂` and `p₁ · w₂`.  The proof passes through `L[ε₁, ε₂] = L ⊕ (L × L)`: the product of the two
lifts, placed in the two directions, is one lift whose two projections are `w₁ p₂` and `p₁ w₂` and
whose sum is `w₁ w₂`.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

section LocalRing

variable {L : Type u} [Field L] {M : Type u} [AddCommGroup M] [Module L M] [Module Lᵐᵒᵖ M]
  [IsCentralScalar L M]

/-- A square-zero extension of a field is a local ring. -/
instance isLocalRing_trivSqZeroExt [Nonempty M] : IsLocalRing (TrivSqZeroExt L M) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    rcases eq_or_ne a.fst 0 with h | h
    · right
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one, h,
        sub_zero]
      exact isUnit_one
    · left
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
      exact isUnit_iff_ne_zero.mpr h

/-- A homomorphism into a square-zero extension of a field whose first component is local is
local. -/
theorem isLocalHom_of_fst_comp {A : Type*} [CommRing A] (ψ : A →+* TrivSqZeroExt L M)
    (φ : A →+* L) [IsLocalHom φ] (h : ∀ a, (ψ a).fst = φ a) : IsLocalHom ψ :=
  ⟨fun a ha => IsLocalHom.map_nonunit (f := φ) a (by
    rw [← h]
    exact TrivSqZeroExt.isUnit_iff_isUnit_fst.mp ha)⟩

end LocalRing

variable {C : Type u} [Field C]

section Lift

variable (X : Over (Spec (.of C))) {L : Type u} [Field L] [Algebra C L]
  {M : Type u} [AddCommGroup M] [Module L M] [Module Lᵐᵒᵖ M] [IsCentralScalar L M] [Module C M]
  [IsScalarTower C L M] [IsScalarTower C Lᵐᵒᵖ M] [Nonempty M]

/-- The reduction `L ⊕ M → L`. -/
abbrev sqzFst : TrivSqZeroExt L M →ₐ[C] L := TrivSqZeroExt.fstHom C L M

/-- **Lifts of a stalk point are stalk points at the same point.** -/
theorem exists_stalkPoint_of_lift (x : X.left) (φ : X.left.presheaf.stalk x ⟶ CommRingCat.of L)
    [IsLocalHom φ.hom] (hφ : stalkConstants X x ≫ φ = CommRingCat.ofHom (algebraMap C L))
    (w : algebraicPointSource (K := C) (R := TrivSqZeroExt L M) ⟶ X)
    (hw : pointSourceMap (sqzFst (C := C) (L := L) (M := M)) ≫ w = stalkPoint X x φ hφ) :
    ∃ (ψ : X.left.presheaf.stalk x ⟶ CommRingCat.of (TrivSqZeroExt L M))
      (hψ : stalkConstants X x ≫ ψ = CommRingCat.ofHom (algebraMap C (TrivSqZeroExt L M))),
      ψ ≫ CommRingCat.ofHom (sqzFst (C := C) (L := L) (M := M)).toRingHom = φ ∧
        w = stalkPoint X x ψ hψ := by
  obtain ⟨y, ψ, hψ, hloc, rfl⟩ := exists_eq_stalkPoint X w
  rw [pointSourceMap_comp_stalkPoint] at hw
  haveI : IsLocalHom (ψ ≫ CommRingCat.ofHom (sqzFst (C := C) (L := L) (M := M)).toRingHom).hom :=
    ⟨fun a ha => hloc.map_nonunit a (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr ha)⟩
  obtain ⟨hyx, hψx⟩ := stalkPoint_eq_stalkPoint X hw
  subst hyx
  refine ⟨ψ, hψ, ?_, rfl⟩
  rw [hψx, TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]

omit [Nonempty M] in
/-- A homomorphism into `L ⊕ M` with local first component is local. -/
theorem isLocalHom_of_comp_sqzFst {x : X.left}
    (ψ : X.left.presheaf.stalk x ⟶ CommRingCat.of (TrivSqZeroExt L M))
    {φ : X.left.presheaf.stalk x ⟶ CommRingCat.of L} [IsLocalHom φ.hom]
    (h : ψ ≫ CommRingCat.ofHom (sqzFst (C := C) (L := L) (M := M)).toRingHom = φ) :
    IsLocalHom ψ.hom :=
  isLocalHom_of_fst_comp ψ.hom φ.hom fun a => by
    rw [← h]
    rfl

end Lift

/-! ### The group law on lifts -/

section GroupLaw

variable (G : Over (Spec (.of C))) [GrpObj G] {L : Type u} [Field L] [Algebra C L]

/-- The dual numbers `L[ε]`. -/
abbrev DualL (L : Type u) [Field L] := TrivSqZeroExt L L

/-- `L[ε₁, ε₂]`. -/
abbrev DualL₂ (L : Type u) [Field L] := TrivSqZeroExt L (L × L)

/-- Constant lift `L → L[ε]`. -/
abbrev dualInl : L →ₐ[C] DualL L := TrivSqZeroExt.inlAlgHom C L L

/-- `L[ε] → L[ε₁,ε₂]`, `ε ↦ ε₁`. -/
abbrev dualIncl₁ : DualL L →ₐ[C] DualL₂ L :=
  (TrivSqZeroExt.map (LinearMap.inl L L L)).restrictScalars C

/-- `L[ε] → L[ε₁,ε₂]`, `ε ↦ ε₂`. -/
abbrev dualIncl₂ : DualL L →ₐ[C] DualL₂ L :=
  (TrivSqZeroExt.map (LinearMap.inr L L L)).restrictScalars C

/-- `L[ε₁,ε₂] → L[ε]`, `ε₁ ↦ ε`, `ε₂ ↦ 0`. -/
abbrev dualProj₁ : DualL₂ L →ₐ[C] DualL L :=
  (TrivSqZeroExt.map (LinearMap.fst L L L)).restrictScalars C

/-- `L[ε₁,ε₂] → L[ε]`, `ε₁ ↦ 0`, `ε₂ ↦ ε`. -/
abbrev dualProj₂ : DualL₂ L →ₐ[C] DualL L :=
  (TrivSqZeroExt.map (LinearMap.snd L L L)).restrictScalars C

/-- `L[ε₁,ε₂] → L[ε]`, `ε₁, ε₂ ↦ ε`. -/
abbrev dualSum : DualL₂ L →ₐ[C] DualL L :=
  (TrivSqZeroExt.map (LinearMap.coprod LinearMap.id LinearMap.id)).restrictScalars C

theorem trivSqZeroExt_algHom_ext {A : Type u} [CommRing A] [Algebra C A]
    {M : Type u} [AddCommGroup M] [Module L M] [Module Lᵐᵒᵖ M] [IsCentralScalar L M]
    [Module C M] [IsScalarTower C L M] [IsScalarTower C Lᵐᵒᵖ M]
    {f g : TrivSqZeroExt L M →ₐ[C] A} (h : ∀ a b, f (a, b) = g (a, b)) : f = g :=
  AlgHom.ext fun ⟨a, b⟩ => h a b

section Compositions

omit [Algebra C L] in
theorem dualProj₁_comp_dualIncl₁ [Algebra C L] :
    (dualProj₁ (C := C) (L := L)).comp dualIncl₁ = AlgHom.id C (DualL L) :=
  AlgHom.ext fun a => TrivSqZeroExt.ext (by simp) (by simp)

omit [Algebra C L] in
theorem dualProj₂_comp_dualIncl₂ [Algebra C L] :
    (dualProj₂ (C := C) (L := L)).comp dualIncl₂ = AlgHom.id C (DualL L) :=
  AlgHom.ext fun a => TrivSqZeroExt.ext (by simp) (by simp)

omit [Algebra C L] in
theorem dualProj₁_comp_dualIncl₂ [Algebra C L] :
    (dualProj₁ (C := C) (L := L)).comp dualIncl₂ =
      (dualInl (C := C) (L := L)).comp (sqzFst (C := C) (L := L) (M := L)) :=
  AlgHom.ext fun a => TrivSqZeroExt.ext (by simp) (by simp)

omit [Algebra C L] in
theorem dualProj₂_comp_dualIncl₁ [Algebra C L] :
    (dualProj₂ (C := C) (L := L)).comp dualIncl₁ =
      (dualInl (C := C) (L := L)).comp (sqzFst (C := C) (L := L) (M := L)) :=
  AlgHom.ext fun a => TrivSqZeroExt.ext (by simp) (by simp)

omit [Algebra C L] in
theorem dualSum_comp_dualIncl₁ [Algebra C L] :
    (dualSum (C := C) (L := L)).comp dualIncl₁ = AlgHom.id C (DualL L) :=
  AlgHom.ext fun a => TrivSqZeroExt.ext (by simp) (by simp)

omit [Algebra C L] in
theorem dualSum_comp_dualIncl₂ [Algebra C L] :
    (dualSum (C := C) (L := L)).comp dualIncl₂ = AlgHom.id C (DualL L) :=
  AlgHom.ext fun a => TrivSqZeroExt.ext (by simp) (by simp)

omit [Algebra C L] in
theorem sqzFst_comp_dualIncl₁ [Algebra C L] :
    (sqzFst (C := C) (L := L) (M := L × L)).comp dualIncl₁ = sqzFst (C := C) (L := L) (M := L) :=
  AlgHom.ext fun a => by simp

omit [Algebra C L] in
theorem sqzFst_comp_dualIncl₂ [Algebra C L] :
    (sqzFst (C := C) (L := L) (M := L × L)).comp dualIncl₂ = sqzFst (C := C) (L := L) (M := L) :=
  AlgHom.ext fun a => by simp

end Compositions

omit [Field C] in
theorem pointSourceMap_id [Field C] {R : Type u} [CommRing R] [Algebra C R] :
    pointSourceMap (AlgHom.id C R) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (RingHom.id R)) = 𝟙 _
  rw [CommRingCat.ofHom_id, Spec.map_id]

/-- Pushing points forward along a map of `C`-algebras is a homomorphism of point groups. -/
theorem pointSourceMap_comp_mul {R S : Type u} [CommRing R] [CommRing S] [Algebra C R]
    [Algebra C S] (f : R →ₐ[C] S) (p q : algebraicPointSource (K := C) (R := R) ⟶ G) :
    pointSourceMap f ≫ (p * q) = (pointSourceMap f ≫ p) * (pointSourceMap f ≫ q) :=
  MonObj.comp_mul _ _ _

/-- **The group law on infinitesimal lifts is addition of derivations.** -/
theorem exists_stalkPoint_mul_of_lifts (x : G.left)
    (φ : G.left.presheaf.stalk x ⟶ CommRingCat.of L) [IsLocalHom φ.hom]
    (hφ : stalkConstants G x ≫ φ = CommRingCat.ofHom (algebraMap C L))
    (p₁ p₂ : algebraicPointSource (K := C) (R := L) ⟶ G) (hp : p₁ * p₂ = stalkPoint G x φ hφ)
    (w₁ w₂ : algebraicPointSource (K := C) (R := DualL L) ⟶ G)
    (hw₁ : pointSourceMap (sqzFst (C := C) (L := L) (M := L)) ≫ w₁ = p₁)
    (hw₂ : pointSourceMap (sqzFst (C := C) (L := L) (M := L)) ≫ w₂ = p₂)
    (ψ₁ ψ₂ : G.left.presheaf.stalk x ⟶ CommRingCat.of (DualL L))
    (hψ₁ : stalkConstants G x ≫ ψ₁ = CommRingCat.ofHom (algebraMap C (DualL L)))
    (hψ₂ : stalkConstants G x ≫ ψ₂ = CommRingCat.ofHom (algebraMap C (DualL L)))
    (hψ₁φ : ψ₁ ≫ CommRingCat.ofHom (sqzFst (C := C) (L := L) (M := L)).toRingHom = φ)
    (hψ₂φ : ψ₂ ≫ CommRingCat.ofHom (sqzFst (C := C) (L := L) (M := L)).toRingHom = φ)
    (h₁ : w₁ * (pointSourceMap (dualInl (C := C) (L := L)) ≫ p₂) = stalkPoint G x ψ₁ hψ₁)
    (h₂ : (pointSourceMap (dualInl (C := C) (L := L)) ≫ p₁) * w₂ = stalkPoint G x ψ₂ hψ₂) :
    ∃ (ψ : G.left.presheaf.stalk x ⟶ CommRingCat.of (DualL L))
      (hψ : stalkConstants G x ≫ ψ = CommRingCat.ofHom (algebraMap C (DualL L))),
      ψ ≫ CommRingCat.ofHom (sqzFst (C := C) (L := L) (M := L)).toRingHom = φ ∧
      (∀ a, (ψ a).snd = (ψ₁ a).snd + (ψ₂ a).snd) ∧ w₁ * w₂ = stalkPoint G x ψ hψ := by
  haveI := isLocalHom_of_comp_sqzFst G ψ₁ hψ₁φ
  haveI := isLocalHom_of_comp_sqzFst G ψ₂ hψ₂φ
  set W := (pointSourceMap (dualIncl₁ (C := C) (L := L)) ≫ w₁) *
    (pointSourceMap (dualIncl₂ (C := C) (L := L)) ≫ w₂)
  have hWfst : pointSourceMap (sqzFst (C := C) (L := L) (M := L × L)) ≫ W =
      stalkPoint G x φ hφ := by
    rw [pointSourceMap_comp_mul, ← Category.assoc, ← Category.assoc, ← pointSourceMap_comp,
      ← pointSourceMap_comp, sqzFst_comp_dualIncl₁, sqzFst_comp_dualIncl₂, hw₁, hw₂, hp]
  obtain ⟨Ψ, hΨ, hΨφ, hW⟩ := exists_stalkPoint_of_lift G x φ hφ W hWfst
  haveI := isLocalHom_of_comp_sqzFst G Ψ hΨφ
  have hproj : ∀ (π : DualL₂ L →ₐ[C] DualL L) (_ : (sqzFst (C := C) (L := L) (M := L)).comp π =
      sqzFst (C := C) (L := L) (M := L × L)),
      IsLocalHom (Ψ ≫ CommRingCat.ofHom π.toRingHom).hom := by
    intro π hπ
    refine isLocalHom_of_comp_sqzFst G _ (φ := φ) ?_
    rw [Category.assoc, ← CommRingCat.ofHom_comp]
    change Ψ ≫ CommRingCat.ofHom ((sqzFst (C := C) (L := L) (M := L)).comp π).toRingHom = φ
    rw [hπ, hΨφ]
  have hfst₁ : (sqzFst (C := C) (L := L) (M := L)).comp dualProj₁ =
      sqzFst (C := C) (L := L) (M := L × L) := AlgHom.ext fun a => by simp
  have hfst₂ : (sqzFst (C := C) (L := L) (M := L)).comp dualProj₂ =
      sqzFst (C := C) (L := L) (M := L × L) := AlgHom.ext fun a => by simp
  have hfstS : (sqzFst (C := C) (L := L) (M := L)).comp dualSum =
      sqzFst (C := C) (L := L) (M := L × L) := AlgHom.ext fun a => by simp
  haveI := hproj _ hfst₁
  haveI := hproj _ hfst₂
  -- the two projections of `W` are `w₁ p₂` and `p₁ w₂`
  have hP₁ : pointSourceMap (dualProj₁ (C := C) (L := L)) ≫ W = w₁ *
      (pointSourceMap (dualInl (C := C) (L := L)) ≫ p₂) := by
    rw [pointSourceMap_comp_mul, ← Category.assoc, ← Category.assoc, ← pointSourceMap_comp,
      ← pointSourceMap_comp, dualProj₁_comp_dualIncl₁, dualProj₁_comp_dualIncl₂,
      pointSourceMap_comp, Category.assoc, hw₂, pointSourceMap_id, Category.id_comp]
  have hP₂ : pointSourceMap (dualProj₂ (C := C) (L := L)) ≫ W =
      (pointSourceMap (dualInl (C := C) (L := L)) ≫ p₁) * w₂ := by
    rw [pointSourceMap_comp_mul, ← Category.assoc, ← Category.assoc, ← pointSourceMap_comp,
      ← pointSourceMap_comp, dualProj₂_comp_dualIncl₂, dualProj₂_comp_dualIncl₁,
      pointSourceMap_comp, Category.assoc, hw₁, pointSourceMap_id, Category.id_comp]
  have hΨ₁ : Ψ ≫ CommRingCat.ofHom (dualProj₁ (C := C) (L := L)).toRingHom = ψ₁ := by
    have e : pointSourceMap (dualProj₁ (C := C) (L := L)) ≫ stalkPoint G x Ψ hΨ =
        stalkPoint G x ψ₁ hψ₁ := by rw [← hW, hP₁, h₁]
    rw [pointSourceMap_comp_stalkPoint] at e
    exact stalkPoint_injective G e
  have hΨ₂ : Ψ ≫ CommRingCat.ofHom (dualProj₂ (C := C) (L := L)).toRingHom = ψ₂ := by
    have e : pointSourceMap (dualProj₂ (C := C) (L := L)) ≫ stalkPoint G x Ψ hΨ =
        stalkPoint G x ψ₂ hψ₂ := by rw [← hW, hP₂, h₂]
    rw [pointSourceMap_comp_stalkPoint] at e
    exact stalkPoint_injective G e
  refine ⟨Ψ ≫ CommRingCat.ofHom (dualSum (C := C) (L := L)).toRingHom, by
    rw [← Category.assoc, hΨ, ← CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.ofHom (RingHom.ext (dualSum (C := C) (L := L)).commutes), ?_, ?_, ?_⟩
  · rw [Category.assoc, ← CommRingCat.ofHom_comp]
    change Ψ ≫ CommRingCat.ofHom ((sqzFst (C := C) (L := L) (M := L)).comp dualSum).toRingHom = φ
    rw [hfstS, hΨφ]
  · intro a
    rw [← hΨ₁, ← hΨ₂]
    change (dualSum (C := C) (L := L) (Ψ a)).snd = (dualProj₁ (C := C) (L := L) (Ψ a)).snd +
      (dualProj₂ (C := C) (L := L) (Ψ a)).snd
    simp
  · rw [← pointSourceMap_comp_stalkPoint (hψ := hΨ), ← hW, pointSourceMap_comp_mul,
      ← Category.assoc, ← Category.assoc, ← pointSourceMap_comp, ← pointSourceMap_comp,
      dualSum_comp_dualIncl₁, dualSum_comp_dualIncl₂, pointSourceMap_id, Category.id_comp,
      Category.id_comp]

end GroupLaw

end

end GaloisForLFunctions.HTGeometry
