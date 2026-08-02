import Mathlib.AlgebraicGeometry.Group.Abelian
import Mathlib.AlgebraicGeometry.Group.Smooth
import Mathlib.Algebra.Group.Hom.Basic
import GaloisForLFunctions.HTGeometry.FunctionFieldPullback

/-!
# Abelian varieties and multiplication morphisms

An abelian variety over a field is represented by a proper geometrically integral group scheme.
Mathlib proves that such a group scheme is commutative.  This file packages that definition and
constructs the categorical multiplication morphism `[m]`, its torsion subgroup on every functor of
points, and the increasing union of its `m`-power torsion.
-/

open CategoryTheory Limits
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

open AlgebraicGeometry

/-- Right translations compose according to multiplication of their translating points. -/
theorem GrpObj.mulRight_trans
    {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {G : C} [GrpObj G] (x y : 𝟙_ C ⟶ G) :
    (GrpObj.mulRight x).trans (GrpObj.mulRight y) = GrpObj.mulRight (x * y) := by
  apply Iso.ext
  simp [GrpObj.mulRight_hom, comp_lift_assoc, lift_lift_assoc]
  rw [MonObj.comp_mul]
  change _ = lift (𝟙 G)
    (lift (toUnit G ≫ x) (toUnit G ≫ y) ≫ μ) ≫ μ
  rfl

/-- A proper geometrically integral group scheme over a field.  Properness already includes local
finite type, and geometric integrality supplies the standard geometric reducedness and
irreducibility conditions. -/
class IsAbelianVariety
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] : Prop
    extends IsProper A.hom, GeometricallyIntegral A.hom

/-- Every abelian variety is a commutative group object. -/
noncomputable instance isCommMonObj_of_isAbelianVariety
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A] :
    IsCommMonObj A :=
  AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral A

/-- Abelian varieties are smooth over their ground field. -/
noncomputable instance smooth_of_isAbelianVariety
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A] :
    Smooth A.hom := by
  let e : A ≅ Over.mk A.hom := Over.isoMk (Iso.refl _)
  letI : GrpObj (Over.mk A.hom) := GrpObj.ofIso e
  exact AlgebraicGeometry.smooth_of_grpObj A.hom

/-- The underlying scheme of an abelian variety is integral. -/
noncomputable instance isIntegral_of_isAbelianVariety
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A] :
    IsIntegral A.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton A.hom

/-- The abelian function field as an algebra over its literal ground field. -/
@[implicit_reducible] noncomputable def abelianVarietyFunctionFieldAlgebra
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A] :
    Algebra K A.left.functionField :=
  RingHom.toAlgebra <|
    A.hom.functionFieldPullback.hom.comp
      (Scheme.specFunctionFieldAlgEquiv K).toRingHom

/-- Translation of an abelian variety by a rational point. -/
def abelianVarietyTranslationIso
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (x : 𝟙_ (Over (Spec (.of K))) ⟶ A) : A ≅ A :=
  GrpObj.mulRight x

/-- Underlying scheme isomorphism of translation by a rational point. -/
def abelianVarietyTranslationSchemeIso
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (x : 𝟙_ (Over (Spec (.of K))) ⟶ A) : A.left ≅ A.left :=
  (Over.forget (Spec (.of K))).mapIso (abelianVarietyTranslationIso A x)

/-- Translation of the abelian variety induces a ground-field-fixing automorphism of its function
field. -/
noncomputable def abelianVarietyTranslationFunctionFieldAlgEquiv
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (x : 𝟙_ (Over (Spec (.of K))) ⟶ A) :=
  letI := abelianVarietyFunctionFieldAlgebra A
  AlgEquiv.ofRingEquiv
    (f := Scheme.Iso.functionFieldPullbackRingEquiv
      (abelianVarietyTranslationSchemeIso A x))
    (fun r => by
      let f := (abelianVarietyTranslationSchemeIso A x).hom
      have h := f.functionFieldPullback_comp A.hom
      have hfs := Scheme.Hom.functionFieldPullback_congr
        (f ≫ A.hom) A.hom (abelianVarietyTranslationIso A x).hom.w
      rw [show algebraMap K A.left.functionField r =
        A.hom.functionFieldPullback (Scheme.specFunctionFieldAlgEquiv K r) from rfl]
      change f.functionFieldPullback
          (A.hom.functionFieldPullback (Scheme.specFunctionFieldAlgEquiv K r)) =
        A.hom.functionFieldPullback (Scheme.specFunctionFieldAlgEquiv K r)
      exact congrArg
        (fun q : (Spec (.of K)).functionField ⟶ A.left.functionField =>
          q (Scheme.specFunctionFieldAlgEquiv K r))
        (h.symm.trans hfs))

/-- Translation by the identity point induces the identity automorphism of the function field. -/
@[simp]
theorem abelianVarietyTranslationFunctionFieldAlgEquiv_one
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A] :
    letI := abelianVarietyFunctionFieldAlgebra A
    abelianVarietyTranslationFunctionFieldAlgEquiv A
        (1 : 𝟙_ (Over (Spec (.of K))) ⟶ A) = 1 := by
  letI := abelianVarietyFunctionFieldAlgebra A
  ext z
  change
    (abelianVarietyTranslationSchemeIso A
      (1 : 𝟙_ (Over (Spec (.of K))) ⟶ A)).hom.functionFieldPullback z = z
  have hiso :
      GrpObj.mulRight (1 : 𝟙_ (Over (Spec (.of K))) ⟶ A) = Iso.refl A := by
    rw [← MonObj.one_eq_one]
    exact GrpObj.mulRight_one A
  have hs := congrArg (fun e : A ≅ A => e.hom.left) hiso
  change
    (abelianVarietyTranslationSchemeIso A
      (1 : 𝟙_ (Over (Spec (.of K))) ⟶ A)).hom = 𝟙 A.left at hs
  have hp := Scheme.Hom.functionFieldPullback_congr _ _ hs
  calc
    _ = Scheme.Hom.functionFieldPullback (𝟙 A.left) z :=
      congrArg (fun q : A.left.functionField ⟶ A.left.functionField => q z) hp
    _ = z := congrArg
      (fun q : A.left.functionField ⟶ A.left.functionField => q z)
      (Scheme.Hom.functionFieldPullback_id A.left)

/-- Translation turns multiplication of rational points into multiplication of ground-field
automorphisms of the abelian function field. -/
theorem abelianVarietyTranslationFunctionFieldAlgEquiv_mul
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (x y : 𝟙_ (Over (Spec (.of K))) ⟶ A) :
    letI := abelianVarietyFunctionFieldAlgebra A
    abelianVarietyTranslationFunctionFieldAlgEquiv A (x * y) =
      abelianVarietyTranslationFunctionFieldAlgEquiv A x *
        abelianVarietyTranslationFunctionFieldAlgEquiv A y := by
  letI := abelianVarietyFunctionFieldAlgebra A
  ext z
  rw [AlgEquiv.mul_apply]
  change
    (abelianVarietyTranslationSchemeIso A (x * y)).hom.functionFieldPullback z =
      (abelianVarietyTranslationSchemeIso A x).hom.functionFieldPullback
        ((abelianVarietyTranslationSchemeIso A y).hom.functionFieldPullback z)
  have hs := congrArg (fun e : A ≅ A => e.hom.left) (GrpObj.mulRight_trans x y)
  change
    (abelianVarietyTranslationSchemeIso A x).hom ≫
        (abelianVarietyTranslationSchemeIso A y).hom =
      (abelianVarietyTranslationSchemeIso A (x * y)).hom at hs
  have hc := Scheme.Hom.functionFieldPullback_congr _ _ hs
  have hp :=
    (abelianVarietyTranslationSchemeIso A x).hom.functionFieldPullback_comp
      (abelianVarietyTranslationSchemeIso A y).hom
  calc
    _ = ((abelianVarietyTranslationSchemeIso A x).hom ≫
        (abelianVarietyTranslationSchemeIso A y).hom).functionFieldPullback z :=
      congrArg (fun q : A.left.functionField ⟶ A.left.functionField => q z) hc.symm
    _ = _ := congrArg
      (fun q : A.left.functionField ⟶ A.left.functionField => q z) hp

/-- Rational-point translation acts on the abelian function field by ground-field-fixing
automorphisms. -/
noncomputable def abelianVarietyTranslationFunctionFieldMonoidHom
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A] :
    letI := abelianVarietyFunctionFieldAlgebra A
    (𝟙_ (Over (Spec (.of K))) ⟶ A) →*
      (A.left.functionField ≃ₐ[K] A.left.functionField) := by
  letI := abelianVarietyFunctionFieldAlgebra A
  exact
    { toFun := abelianVarietyTranslationFunctionFieldAlgEquiv A
      map_one' := abelianVarietyTranslationFunctionFieldAlgEquiv_one A
      map_mul' := abelianVarietyTranslationFunctionFieldAlgEquiv_mul A }

/-- Categorical multiplication by an integer on an abelian variety. -/
def abelianVarietyMultiplication
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (m : ℤ) : A ⟶ A :=
  (𝟙 A) ^ m

/-- Multiplication by an integer is a homomorphism of the underlying commutative group object. -/
noncomputable instance isMonHom_abelianVarietyMultiplication
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (m : ℤ) : IsMonHom (abelianVarietyMultiplication A m) := by
  let G : Grp (Over (Spec (.of K))) := Grp.mk A
  let f : G ⟶ G := Grp.homMk (𝟙 A)
  change IsMonHom (f.hom.hom ^ m)
  rw [← Grp.Hom.hom_hom_zpow f m]
  infer_instance

/-- Multiplication acts on every functor-of-points value by pointwise integer power. -/
@[simp]
theorem comp_abelianVarietyMultiplication
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    {X : Over (Spec (.of K))} (x : X ⟶ A) (m : ℤ) :
    x ≫ abelianVarietyMultiplication A m = x ^ m := by
  simpa [abelianVarietyMultiplication] using GrpObj.comp_zpow x (𝟙 A) m

/-- Multiplication morphisms compose by multiplying their integer labels. -/
theorem abelianVarietyMultiplication_comp
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (m n : ℤ) :
    abelianVarietyMultiplication A m ≫ abelianVarietyMultiplication A n =
      abelianVarietyMultiplication A (m * n) := by
  rw [comp_abelianVarietyMultiplication]
  exact (zpow_mul (𝟙 A) m n).symm

/-- Iterating multiplication by `m` categorically gives multiplication by `m ^ n`. -/
theorem categoricalIterate_abelianVarietyMultiplication_left
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (m : ℤ) (n : ℕ) :
    (abelianVarietyMultiplication A m).left.categoricalIterate n =
      (abelianVarietyMultiplication A (m ^ n)).left := by
  induction n with
  | zero => simp [Scheme.Hom.categoricalIterate, abelianVarietyMultiplication]
  | succ n ih =>
      rw [Scheme.Hom.categoricalIterate_succ, ih]
      have h := congrArg
        (fun q : A ⟶ A => q.left)
        (abelianVarietyMultiplication_comp A (m ^ n) m)
      change (abelianVarietyMultiplication A (m ^ n)).left ≫
        (abelianVarietyMultiplication A m).left =
          (abelianVarietyMultiplication A ((m ^ n) * m)).left at h
      simpa only [pow_succ] using h

/-- Dominance of one multiplication morphism propagates to all of its iterated power levels. -/
instance isDominant_abelianVarietyMultiplication_pow
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (m : ℤ) [IsDominant (abelianVarietyMultiplication A m).left] (n : ℕ) :
    IsDominant (abelianVarietyMultiplication A (m ^ n)).left := by
  rw [← categoricalIterate_abelianVarietyMultiplication_left A m n]
  infer_instance

/-- Pullback by a dominant multiplication morphism on the abelian function field, as an algebra
endomorphism over the function field of the base.  Dominance is explicit until the multiplication
isogeny theorem is available in the algebraic-geometry library. -/
noncomputable def abelianVarietyMultiplicationFunctionFieldPullback
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (m : ℤ) [IsDominant (abelianVarietyMultiplication A m).left] :=
  letI := abelianVarietyFunctionFieldAlgebra A
  { toRingHom :=
      (abelianVarietyMultiplication A m).left.functionFieldPullback.hom
    commutes' := fun r => by
      let f := (abelianVarietyMultiplication A m).left
      have h := f.functionFieldPullback_comp A.hom
      have hfs := Scheme.Hom.functionFieldPullback_congr
        (f ≫ A.hom) A.hom (abelianVarietyMultiplication A m).w
      change f.functionFieldPullback
          (A.hom.functionFieldPullback (Scheme.specFunctionFieldAlgEquiv K r)) =
        A.hom.functionFieldPullback (Scheme.specFunctionFieldAlgEquiv K r)
      exact congrArg
        (fun q : (Spec (.of K)).functionField ⟶ A.left.functionField =>
          q (Scheme.specFunctionFieldAlgEquiv K r))
        (h.symm.trans hfs) :
      A.left.functionField →ₐ[K] A.left.functionField }

/-- The `n`-fold field pullback by `[m]` is pullback by `[m ^ n]`. -/
theorem abelianVarietyMultiplicationFunctionFieldPullback_pow_apply
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (m : ℤ) [IsDominant (abelianVarietyMultiplication A m).left]
    (n : ℕ) (z : A.left.functionField) :
    letI := abelianVarietyFunctionFieldAlgebra A
    ((abelianVarietyMultiplicationFunctionFieldPullback A m) ^ n) z =
      (abelianVarietyMultiplication A (m ^ n)).left.functionFieldPullback z := by
  letI := abelianVarietyFunctionFieldAlgebra A
  rw [AlgHom.coe_pow]
  exact (Scheme.Hom.functionFieldPullback_categoricalIterate_apply
    (abelianVarietyMultiplication A m).left n z).symm.trans <|
      congrArg (fun q : A.left.functionField ⟶ A.left.functionField => q z) <|
        Scheme.Hom.functionFieldPullback_congr
          ((abelianVarietyMultiplication A m).left.categoricalIterate n)
          (abelianVarietyMultiplication A (m ^ n)).left
          (categoricalIterate_abelianVarietyMultiplication_left A m n)

/-- `m`-torsion in every functor-of-points group of an abelian variety. -/
def abelianVarietyTorsionPoints
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (X : Over (Spec (.of K))) (m : ℤ) : Subgroup (X ⟶ A) :=
  (zpowGroupHom m).ker

/-- Deck transformations of the abelian function field obtained by translating by rational
`m`-torsion points. -/
noncomputable def abelianVarietyTorsionDeckGroup
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (m : ℤ) :
    letI := abelianVarietyFunctionFieldAlgebra A
    Subgroup (A.left.functionField ≃ₐ[K] A.left.functionField) := by
  letI := abelianVarietyFunctionFieldAlgebra A
  exact (abelianVarietyTorsionPoints A (𝟙_ (Over (Spec (.of K)))) m).map
    (abelianVarietyTranslationFunctionFieldMonoidHom A)

/-- A function-field automorphism belongs to the finite torsion deck group exactly when it is
translation by a rational torsion point. -/
theorem mem_abelianVarietyTorsionDeckGroup_iff
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (m : ℤ)
    (σ : letI := abelianVarietyFunctionFieldAlgebra A
      A.left.functionField ≃ₐ[K] A.left.functionField) :
    letI := abelianVarietyFunctionFieldAlgebra A
    σ ∈ abelianVarietyTorsionDeckGroup A m ↔
      ∃ x : 𝟙_ (Over (Spec (.of K))) ⟶ A,
        x ∈ abelianVarietyTorsionPoints A (𝟙_ (Over (Spec (.of K)))) m ∧
          abelianVarietyTranslationFunctionFieldAlgEquiv A x = σ := by
  letI := abelianVarietyFunctionFieldAlgebra A
  exact Subgroup.mem_map

@[simp]
theorem mem_abelianVarietyTorsionPoints_iff
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (X : Over (Spec (.of K))) (m : ℤ) (x : X ⟶ A) :
    x ∈ abelianVarietyTorsionPoints A X m ↔ x ^ m = 1 := by
  simp [abelianVarietyTorsionPoints]

/-- Kernel form: a point is `m`-torsion exactly when categorical multiplication sends it to the
identity point. -/
theorem mem_abelianVarietyTorsionPoints_iff_comp_eq_one
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (X : Over (Spec (.of K))) (m : ℤ) (x : X ⟶ A) :
    x ∈ abelianVarietyTorsionPoints A X m ↔
      x ≫ abelianVarietyMultiplication A m = 1 := by
  rw [mem_abelianVarietyTorsionPoints_iff,
    comp_abelianVarietyMultiplication]

/-- Translation by an `m`-torsion point is a deck transformation over multiplication by `m`. -/
theorem abelianVarietyTranslation_comp_multiplication_of_mem_torsion
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (m : ℤ) (x : 𝟙_ (Over (Spec (.of K))) ⟶ A)
    (hx : x ∈ abelianVarietyTorsionPoints A (𝟙_ (Over (Spec (.of K)))) m) :
    (abelianVarietyTranslationIso A x).hom ≫ abelianVarietyMultiplication A m =
      abelianVarietyMultiplication A m := by
  have hxm :=
    (mem_abelianVarietyTorsionPoints_iff_comp_eq_one A
      (𝟙_ (Over (Spec (.of K)))) m x).mp hx
  change
    ((𝟙 A) * (toUnit A ≫ x)) ≫ abelianVarietyMultiplication A m =
      abelianVarietyMultiplication A m
  rw [MonObj.mul_comp, Category.id_comp, Category.assoc, hxm]
  simp [CategoryTheory.Hom.one_def]

/-- Every finite torsion deck transformation fixes the image of multiplication pullback on the
abelian function field. -/
theorem abelianVarietyTranslationFunctionFieldAlgEquiv_fix_multiplicationPullback
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (m : ℤ) [IsDominant (abelianVarietyMultiplication A m).left]
    (x : 𝟙_ (Over (Spec (.of K))) ⟶ A)
    (hx : x ∈ abelianVarietyTorsionPoints A (𝟙_ (Over (Spec (.of K)))) m)
    (z : A.left.functionField) :
    letI := abelianVarietyFunctionFieldAlgebra A
    abelianVarietyTranslationFunctionFieldAlgEquiv A x
        (abelianVarietyMultiplicationFunctionFieldPullback A m z) =
      abelianVarietyMultiplicationFunctionFieldPullback A m z := by
  letI := abelianVarietyFunctionFieldAlgebra A
  let r := (abelianVarietyTranslationSchemeIso A x).hom
  let q := (abelianVarietyMultiplication A m).left
  change r.functionFieldPullback (q.functionFieldPullback z) = q.functionFieldPullback z
  have hp := r.functionFieldPullback_comp q
  have hs := congrArg (fun f : A ⟶ A => f.left)
    (abelianVarietyTranslation_comp_multiplication_of_mem_torsion A m x hx)
  have hc := Scheme.Hom.functionFieldPullback_congr (r ≫ q) q hs
  calc
    _ = (r ≫ q).functionFieldPullback z := congrArg
      (fun f : A.left.functionField ⟶ A.left.functionField => f z) hp.symm
    _ = _ := congrArg
      (fun f : A.left.functionField ⟶ A.left.functionField => f z) hc

/-- The whole finite torsion deck group fixes multiplication pullback pointwise. -/
theorem abelianVarietyTorsionDeckGroup_fix_multiplicationPullback
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (m : ℤ) [IsDominant (abelianVarietyMultiplication A m).left]
    (σ : letI := abelianVarietyFunctionFieldAlgebra A
      A.left.functionField ≃ₐ[K] A.left.functionField)
    (hσ : letI := abelianVarietyFunctionFieldAlgebra A
      σ ∈ abelianVarietyTorsionDeckGroup A m)
    (z : A.left.functionField) :
    letI := abelianVarietyFunctionFieldAlgebra A
    σ (abelianVarietyMultiplicationFunctionFieldPullback A m z) =
      abelianVarietyMultiplicationFunctionFieldPullback A m z := by
  letI := abelianVarietyFunctionFieldAlgebra A
  obtain ⟨x, hx, rfl⟩ :=
    (mem_abelianVarietyTorsionDeckGroup_iff A m σ).mp hσ
  exact
    abelianVarietyTranslationFunctionFieldAlgEquiv_fix_multiplicationPullback A m x hx z

/-- Union of all `m^n`-torsion point subgroups. -/
def abelianVarietyMultiplicationPrimaryTorsionPoints
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (X : Over (Spec (.of K))) (m : ℤ) : Subgroup (X ⟶ A) :=
  ⨆ n : ℕ, abelianVarietyTorsionPoints A X (m ^ n)

/-- Deck group generated by all rational `m`-primary torsion translations. -/
noncomputable def abelianVarietyMultiplicationPrimaryTorsionDeckGroup
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (m : ℤ) :
    letI := abelianVarietyFunctionFieldAlgebra A
    Subgroup (A.left.functionField ≃ₐ[K] A.left.functionField) := by
  letI := abelianVarietyFunctionFieldAlgebra A
  exact
    (abelianVarietyMultiplicationPrimaryTorsionPoints A
      (𝟙_ (Over (Spec (.of K)))) m).map
        (abelianVarietyTranslationFunctionFieldMonoidHom A)

/-- The full multiplication-primary deck group is exactly the union of its finite-depth deck
groups. -/
theorem abelianVarietyMultiplicationPrimaryTorsionDeckGroup_eq_iSup
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (m : ℤ) :
    letI := abelianVarietyFunctionFieldAlgebra A
    abelianVarietyMultiplicationPrimaryTorsionDeckGroup A m =
      ⨆ n : ℕ, abelianVarietyTorsionDeckGroup A (m ^ n) := by
  letI := abelianVarietyFunctionFieldAlgebra A
  exact Subgroup.map_iSup
    (abelianVarietyTranslationFunctionFieldMonoidHom A)
    (fun n : ℕ => abelianVarietyTorsionPoints A
      (𝟙_ (Over (Spec (.of K)))) (m ^ n))

/-- Every finite-level `m^n`-torsion subgroup lies in the full multiplication-primary torsion
group. -/
theorem abelianVarietyTorsionPoints_le_multiplicationPrimary
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (X : Over (Spec (.of K))) (m : ℤ) (n : ℕ) :
    abelianVarietyTorsionPoints A X (m ^ n) ≤
      abelianVarietyMultiplicationPrimaryTorsionPoints A X m :=
  le_iSup (fun r : ℕ => abelianVarietyTorsionPoints A X (m ^ r)) n

/-- Consecutive multiplication-primary torsion levels form an increasing tower. -/
theorem abelianVarietyTorsionPoints_pow_le_succ
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (X : Over (Spec (.of K))) (m : ℤ) (n : ℕ) :
    abelianVarietyTorsionPoints A X (m ^ n) ≤
      abelianVarietyTorsionPoints A X (m ^ (n + 1)) := by
  intro x hx
  rw [mem_abelianVarietyTorsionPoints_iff] at hx ⊢
  rw [pow_succ, zpow_mul, hx]
  simp

/-- The finite multiplication-primary torsion levels are monotone in their depth. -/
theorem monotone_abelianVarietyTorsionPoints_pow
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (X : Over (Spec (.of K))) (m : ℤ) :
    Monotone (fun n : ℕ => abelianVarietyTorsionPoints A X (m ^ n)) :=
  monotone_nat_of_le_succ (abelianVarietyTorsionPoints_pow_le_succ A X m)

/-- Consecutive finite-depth torsion deck groups form an increasing tower. -/
theorem abelianVarietyTorsionDeckGroup_pow_le_succ
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (m : ℤ) (n : ℕ) :
    letI := abelianVarietyFunctionFieldAlgebra A
    abelianVarietyTorsionDeckGroup A (m ^ n) ≤
      abelianVarietyTorsionDeckGroup A (m ^ (n + 1)) := by
  letI := abelianVarietyFunctionFieldAlgebra A
  exact Subgroup.map_mono
    (abelianVarietyTorsionPoints_pow_le_succ A
      (𝟙_ (Over (Spec (.of K)))) m n)

/-- Finite-depth torsion deck groups are monotone in depth. -/
theorem monotone_abelianVarietyTorsionDeckGroup_pow
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (m : ℤ) :
    letI := abelianVarietyFunctionFieldAlgebra A
    Monotone (fun n : ℕ => abelianVarietyTorsionDeckGroup A (m ^ n)) := by
  letI := abelianVarietyFunctionFieldAlgebra A
  exact monotone_nat_of_le_succ (abelianVarietyTorsionDeckGroup_pow_le_succ A m)

/-- Membership in multiplication-primary torsion is witnessed at one finite level. -/
theorem mem_abelianVarietyMultiplicationPrimaryTorsionPoints_iff
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (X : Over (Spec (.of K))) (m : ℤ) (x : X ⟶ A) :
    x ∈ abelianVarietyMultiplicationPrimaryTorsionPoints A X m ↔
      ∃ n : ℕ, x ∈ abelianVarietyTorsionPoints A X (m ^ n) := by
  exact Subgroup.mem_iSup_of_directed
    (monotone_abelianVarietyTorsionPoints_pow A X m).directed_le

/-- Membership in the full multiplication-primary deck group is witnessed at finite depth. -/
theorem mem_abelianVarietyMultiplicationPrimaryTorsionDeckGroup_iff
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (m : ℤ)
    (σ : letI := abelianVarietyFunctionFieldAlgebra A
      A.left.functionField ≃ₐ[K] A.left.functionField) :
    letI := abelianVarietyFunctionFieldAlgebra A
    σ ∈ abelianVarietyMultiplicationPrimaryTorsionDeckGroup A m ↔
      ∃ n : ℕ, σ ∈ abelianVarietyTorsionDeckGroup A (m ^ n) := by
  letI := abelianVarietyFunctionFieldAlgebra A
  rw [abelianVarietyMultiplicationPrimaryTorsionDeckGroup_eq_iSup]
  exact Subgroup.mem_iSup_of_directed
    (monotone_abelianVarietyTorsionDeckGroup_pow A m).directed_le

end

end GaloisForLFunctions.HTGeometry
