import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import GaloisForLFunctions.HTGeometry.SimplicialPiZero

/-!
# The free algebra on a positive cell, and degree zero of the attachment

The positive-cell theorem attaches to a connective commutative algebra `A` the free commutative
algebra on a `1`-connective object `K`, then kills it:
`A//K = A ⊗^L_{Free⁺(K)} 𝟙`, and asserts `π₀(A//K) ≅ π₀A`.

This file realises the whole statement in simplicial commutative rings, where nothing is left
abstract:

* the coefficient objects are simplicial abelian groups and `Free⁺` is the symmetric algebra over
  `ℤ`, which is exactly the `𝟙 ⊕ K ⊕ Sym²K ⊕ ⋯` of the paper proof;
* `π₀` is the colimit over the simplex category, i.e. the coequalizer of the two face maps;
* `1`-connectivity of `K` is `π₀K = 0`;
* `A//K` is the honest pushout, which exists because commutative rings have all colimits.

The proof is the one on paper, with the connectivity step turned into an adjunction argument:
`Sym` and `π₀` are both left adjoints, so `π₀ ∘ Sym` and `Sym ∘ π₀` are left adjoint to the same
functor and therefore agree; hence `π₀ Free⁺(K) ≅ Sym(π₀K) = Sym(0) = ℤ`, the unit, and the
augmentation is a `π₀`-isomorphism.  Since `π₀` preserves pushouts, so is the map it is pushed out
along.

* `symFree`, `symFreeAdj` : **the symmetric algebra over `ℤ`, left adjoint to the underlying
  additive group.**
* `piZeroSymFreeIso` : **`π₀` of a free simplicial commutative ring is the free commutative ring on
  `π₀`.**
* `piZeroSymFree_isInitial` : **a `1`-connective cell has the unit for its `π₀`.**
* `simplicialPiZero_isIso_of_positiveCell`,
  `simplicialPiZero_isIso_pushout_inl` : **`π₀(A//K) ≅ π₀A`.**
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory CategoryTheory.Limits

universe u

/-! ## The symmetric algebra as a free functor -/

/-- **Ring homomorphisms out of a symmetric algebra are determined on generators.** -/
theorem symRingHom_ext {M : Type u} [AddCommGroup M] {R : Type u} [CommRing R]
    {F G : SymmetricAlgebra ℤ M →+* R}
    (h : ∀ x, F (SymmetricAlgebra.ι ℤ M x) = G (SymmetricAlgebra.ι ℤ M x)) : F = G := by
  refine RingHom.ext fun a => ?_
  induction a using SymmetricAlgebra.induction with
  | algebraMap r =>
      have hr : (algebraMap ℤ (SymmetricAlgebra ℤ M)) r = (r : SymmetricAlgebra ℤ M) := by simp
      rw [hr, map_intCast, map_intCast]
  | ι x => exact h x
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

/-- **The free commutative ring on an abelian group**: the symmetric algebra over `ℤ`.  This is the
`Free⁺` of the positive-cell theorem: as a graded object it is `𝟙 ⊕ M ⊕ Sym²M ⊕ ⋯`. -/
noncomputable def symFree : AddCommGrpCat.{u} ⥤ CommRingCat.{u} where
  obj M := CommRingCat.of (SymmetricAlgebra ℤ M)
  map {M N} f := CommRingCat.ofHom
    (SymmetricAlgebra.lift ((SymmetricAlgebra.ι ℤ N).comp
      (AddMonoidHom.toIntLinearMap (AddCommGrpCat.Hom.hom f)))).toRingHom
  map_id M := by
    apply CommRingCat.hom_ext
    refine symRingHom_ext fun x => ?_
    simp
  map_comp {M N P} f g := by
    apply CommRingCat.hom_ext
    refine symRingHom_ext fun x => ?_
    simp

@[simp]
theorem symFree_map_ι {M N : AddCommGrpCat.{u}} (f : M ⟶ N) (x : M) :
    (symFree.map f).hom (SymmetricAlgebra.ι ℤ M x) = SymmetricAlgebra.ι ℤ N (f.hom x) := by
  show (SymmetricAlgebra.lift ((SymmetricAlgebra.ι ℤ N).comp
      (AddMonoidHom.toIntLinearMap (AddCommGrpCat.Hom.hom f)))).toRingHom
        (SymmetricAlgebra.ι ℤ M x) = _
  simp

/-- The additive group underlying a commutative ring. -/
def ringToAdd : CommRingCat.{u} ⥤ AddCommGrpCat.{u} where
  obj R := AddCommGrpCat.of R
  map f := AddCommGrpCat.ofHom f.hom.toAddMonoidHom

/-- The commutative ring map determined by an additive map out of the generators. -/
noncomputable def symLift {M : AddCommGrpCat.{u}} {R : CommRingCat.{u}}
    (g : M ⟶ ringToAdd.obj R) : symFree.obj M ⟶ R :=
  CommRingCat.ofHom
    (SymmetricAlgebra.lift (AddMonoidHom.toIntLinearMap (AddCommGrpCat.Hom.hom g))).toRingHom

@[simp]
theorem symLift_ι {M : AddCommGrpCat.{u}} {R : CommRingCat.{u}}
    (g : M ⟶ ringToAdd.obj R) (x : M) :
    (symLift g).hom (SymmetricAlgebra.ι ℤ M x) = g.hom x :=
  SymmetricAlgebra.lift_ι_apply _ x

/-- The unit of the symmetric-algebra adjunction: the generators. -/
noncomputable def symUnitHom (M : AddCommGrpCat.{u}) : M ⟶ ringToAdd.obj (symFree.obj M) :=
  AddCommGrpCat.ofHom (SymmetricAlgebra.ι ℤ M).toAddMonoidHom

@[simp]
theorem symUnitHom_apply (M : AddCommGrpCat.{u}) (x : M) :
    (symUnitHom M).hom x = SymmetricAlgebra.ι ℤ M x := rfl

@[simp]
theorem ringToAdd_map_apply {R S : CommRingCat.{u}} (f : R ⟶ S) (y : R) :
    (ringToAdd.map f).hom y = f.hom y := rfl

/-- **The symmetric algebra is left adjoint to the underlying additive group.** -/
noncomputable def symFreeAdj : symFree.{u} ⊣ ringToAdd.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M R =>
        { toFun := fun f => symUnitHom M ≫ ringToAdd.map f
          invFun := fun g => symLift g
          left_inv := fun f => by
            apply CommRingCat.hom_ext
            refine symRingHom_ext fun x => ?_
            exact symLift_ι (symUnitHom M ≫ ringToAdd.map f) x
          right_inv := fun g => by
            apply AddCommGrpCat.hom_ext
            refine AddMonoidHom.ext fun x => ?_
            simp }
      homEquiv_naturality_left_symm := fun {M N R} f g => by
        apply CommRingCat.hom_ext
        refine symRingHom_ext fun x => ?_
        show (symLift (f ≫ g)).hom (SymmetricAlgebra.ι ℤ M x)
          = ((symFree.map f) ≫ symLift g).hom (SymmetricAlgebra.ι ℤ M x)
        rw [symLift_ι, CommRingCat.hom_comp, RingHom.comp_apply, symFree_map_ι, symLift_ι]
        rfl }

/-! ## The simplicial level -/

/-- **`Free⁺` on a simplicial abelian group**, levelwise. -/
noncomputable def simplicialSymFree :
    SimplicialObject AddCommGrpCat.{u} ⥤ SimplicialObject CommRingCat.{u} :=
  (Functor.whiskeringRight SimplexCategoryᵒᵖ _ _).obj symFree

/-- The underlying simplicial abelian group of a simplicial commutative ring. -/
noncomputable def simplicialRingToAdd :
    SimplicialObject CommRingCat.{u} ⥤ SimplicialObject AddCommGrpCat.{u} :=
  (Functor.whiskeringRight SimplexCategoryᵒᵖ _ _).obj ringToAdd

/-- **`Free⁺` is a left adjoint on simplicial objects too.** -/
noncomputable def simplicialSymFreeAdj : simplicialSymFree.{u} ⊣ simplicialRingToAdd.{u} :=
  Adjunction.whiskerRight _ symFreeAdj

/-- **`π₀` of a simplicial abelian group**, the colimit over the simplex category. -/
noncomputable def addPiZero : SimplicialObject AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} := colim

/-- `π₀` is left adjoint to the constant simplicial abelian group. -/
noncomputable def addPiZeroAdj : addPiZero.{u} ⊣ Functor.const SimplexCategoryᵒᵖ := colimConstAdj

/-- Taking the underlying additive group of a constant simplicial ring gives a constant simplicial
abelian group. -/
noncomputable def constRingToAddIso :
    Functor.const SimplexCategoryᵒᵖ ⋙ simplicialRingToAdd.{u}
      ≅ ringToAdd.{u} ⋙ Functor.const SimplexCategoryᵒᵖ :=
  NatIso.ofComponents (fun R => Functor.constComp SimplexCategoryᵒᵖ R ringToAdd)

/-- `π₀ ∘ Free⁺` is a left adjoint. -/
noncomputable def piZeroSymFreeAdj :
    simplicialSymFree.{u} ⋙ simplicialPiZero ⊣ ringToAdd.{u} ⋙ Functor.const SimplexCategoryᵒᵖ :=
  (simplicialSymFreeAdj.comp simplicialPiZeroAdj).ofNatIsoRight constRingToAddIso

/-- `Free⁺ ∘ π₀` is a left adjoint to the *same* functor. -/
noncomputable def symFreePiZeroAdj :
    addPiZero.{u} ⋙ symFree.{u} ⊣ ringToAdd.{u} ⋙ Functor.const SimplexCategoryᵒᵖ :=
  addPiZeroAdj.comp symFreeAdj

/-- **`π₀` of a free simplicial commutative ring is the free commutative ring on `π₀`.**  This is
the connectivity mechanism of the positive-cell theorem: both sides are left adjoint to the same
functor. -/
noncomputable def piZeroSymFreeIso :
    simplicialSymFree.{u} ⋙ simplicialPiZero ≅ addPiZero.{u} ⋙ symFree.{u} :=
  Adjunction.leftAdjointUniq piZeroSymFreeAdj symFreePiZeroAdj

noncomputable instance symFree_preservesColimits :
    PreservesColimitsOfSize.{0, 0} symFree.{u} := symFreeAdj.leftAdjoint_preservesColimits

/-- **The free commutative ring on the zero group is the initial ring.** -/
noncomputable def symFree_isInitial {M : AddCommGrpCat.{u}} (hM : IsZero M) :
    IsInitial (symFree.obj M) :=
  IsInitial.isInitialObj symFree M hM.isInitial

/-- **A `1`-connective cell has the unit for its degree zero**: if `π₀K = 0` then
`π₀ Free⁺(K) ≅ 𝟙`. -/
noncomputable def piZeroSymFree_isInitial {K : SimplicialObject AddCommGrpCat.{u}}
    (hK : IsZero (addPiZero.obj K)) :
    IsInitial (simplicialPiZero.obj (simplicialSymFree.obj K)) :=
  IsInitial.ofIso (symFree_isInitial hK) (piZeroSymFreeIso.app K).symm

/-- Any morphism between initial objects is an isomorphism. -/
theorem isIso_of_isInitial {C : Type*} [Category C] {X Y : C} (hX : IsInitial X) (hY : IsInitial Y)
    (f : X ⟶ Y) : IsIso f :=
  ⟨hY.to X, hX.hom_ext _ _, hY.hom_ext _ _⟩

/-- **Selective positive cells preserve degree zero.**  If `K` is `1`-connective, then attaching
the free algebra on `K` to `A` and killing it does not change `π₀`: the pushout leg out of `A` is a
`π₀`-isomorphism.  This is `(2)` of the positive-cell theorem. -/
theorem simplicialPiZero_isIso_of_positiveCell
    {K : SimplicialObject AddCommGrpCat.{u}} (hK : IsZero (addPiZero.obj K))
    {A U D : SimplicialObject CommRingCat.{u}} (hU : IsInitial U)
    {v : simplicialSymFree.obj K ⟶ A} {aug : simplicialSymFree.obj K ⟶ U}
    {h : A ⟶ D} {i : U ⟶ D} (H : IsPushout v aug h i) :
    IsIso (simplicialPiZero.map h) := by
  haveI : IsIso (simplicialPiZero.map aug) :=
    isIso_of_isInitial (piZeroSymFree_isInitial hK)
      (IsInitial.isInitialObj simplicialPiZero U hU) _
  exact simplicialPiZero_isIso_of_isPushout H

/-- **The zero augmentation `Free⁺(K) → 𝟙`.** -/
noncomputable def symAug (K : SimplicialObject AddCommGrpCat.{u}) :
    simplicialSymFree.obj K ⟶ ⊥_ (SimplicialObject CommRingCat.{u}) :=
  (simplicialSymFreeAdj.homEquiv K _).symm 0

/-- **`π₀(A//K) ≅ π₀A`**, on the honest pushout along the zero augmentation. -/
theorem simplicialPiZero_isIso_pushout_inl
    {K : SimplicialObject AddCommGrpCat.{u}} (hK : IsZero (addPiZero.obj K))
    {A : SimplicialObject CommRingCat.{u}} (v : simplicialSymFree.obj K ⟶ A) :
    IsIso (simplicialPiZero.map (pushout.inl v (symAug K))) :=
  simplicialPiZero_isIso_of_positiveCell hK initialIsInitial
    (IsPushout.of_hasPushout v (symAug K))

end GaloisForLFunctions.HTGeometry
