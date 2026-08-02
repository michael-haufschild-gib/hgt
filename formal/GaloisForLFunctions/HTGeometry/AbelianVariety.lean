import Mathlib.AlgebraicGeometry.Group.Abelian
import Mathlib.AlgebraicGeometry.Group.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import GaloisForLFunctions.HTGeometry.FunctionFieldPullback
import GaloisForLFunctions.HTGeometry.DeckClosureStableCore

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

/-- Right translation is faithful in its translating point. -/
theorem GrpObj.mulRight_injective
    {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {G : C} [GrpObj G] :
    Function.Injective (GrpObj.mulRight : (𝟙_ C ⟶ G) → (G ≅ G)) := by
  intro x y h
  have hh := congrArg Iso.hom h
  have hp := congrArg (fun f : G ⟶ G => η[G] ≫ f) hh
  have hp' : lift η[G] x ≫ μ = lift η[G] y ≫ μ := by
    simpa [GrpObj.mulRight_hom, comp_lift_assoc] using hp
  have hx : lift η[G] x ≫ μ = x := by
    change η[G] * x = x
    simpa only [MonObj.one_eq_one] using (_root_.one_mul x)
  have hy : lift η[G] y ≫ μ = y := by
    change η[G] * y = y
    simpa only [MonObj.one_eq_one] using (_root_.one_mul y)
  exact hx.symm.trans (hp'.trans hy)

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

/-- Intermediate field consisting of rational functions pulled back by multiplication by `m`. -/
noncomputable def abelianVarietyMultiplicationPullbackField
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (m : ℤ) [IsDominant (abelianVarietyMultiplication A m).left] :
    letI := abelianVarietyFunctionFieldAlgebra A
    IntermediateField K A.left.functionField := by
  letI := abelianVarietyFunctionFieldAlgebra A
  exact IntermediateField.map
    (abelianVarietyMultiplicationFunctionFieldPullback A m) ⊤

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

/-- The intermediate-field image of the `n`-fold pullback is the pullback field of multiplication
by `m ^ n`. -/
theorem map_abelianVarietyMultiplicationFunctionFieldPullback_pow_top
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (m : ℤ) [IsDominant (abelianVarietyMultiplication A m).left]
    (n : ℕ) :
    letI := abelianVarietyFunctionFieldAlgebra A
    IntermediateField.map
        ((abelianVarietyMultiplicationFunctionFieldPullback A m) ^ n) ⊤ =
      abelianVarietyMultiplicationPullbackField A (m ^ n) := by
  letI := abelianVarietyFunctionFieldAlgebra A
  change IntermediateField.map
      ((abelianVarietyMultiplicationFunctionFieldPullback A m) ^ n) ⊤ =
    IntermediateField.map
      (abelianVarietyMultiplicationFunctionFieldPullback A (m ^ n)) ⊤
  congr 1
  ext z
  exact abelianVarietyMultiplicationFunctionFieldPullback_pow_apply A m n z

/-- Scheme-theoretic kernel of multiplication by `m`, formed as the fiber over the identity
section. -/
def abelianVarietyTorsionScheme
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (m : ℤ) : Over (Spec (.of K)) :=
  pullback (abelianVarietyMultiplication A m) η[A]

/-- Canonical identification of the Cartesian monoidal unit in the over-category with the literal
identity object over the base scheme. -/
noncomputable def abelianVarietyTensorUnitIsoBase
    {K : Type u} [Field K] :
    𝟙_ (Over (Spec (.of K))) ≅ Over.mk (𝟙 (Spec (.of K))) :=
  isTerminalTensorUnit.uniqueUpToIso (Over.mkIdTerminal)

/-- Identity section of an abelian variety with literal source `Spec K`. -/
noncomputable def abelianVarietyIdentitySection
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A] :
    Spec (.of K) ⟶ A.left :=
  ((abelianVarietyTensorUnitIsoBase (K := K)).inv ≫ η[A]).left

/-- Literal scheme-theoretic kernel of multiplication by `m`.  Unlike the kernel object formed in
the over-category, this chosen model is definitionally a scheme pullback over `Spec K`. -/
noncomputable def abelianVarietyTorsionKernelScheme
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (m : ℤ) : Scheme :=
  pullback (abelianVarietyMultiplication A m).left
    (abelianVarietyIdentitySection A)

/-- Structural projection of the literal torsion-kernel scheme to the ground field. -/
noncomputable def abelianVarietyTorsionKernelProjection
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (m : ℤ) :
    abelianVarietyTorsionKernelScheme A m ⟶ Spec (.of K) :=
  pullback.snd (abelianVarietyMultiplication A m).left
    (abelianVarietyIdentitySection A)

/-- Canonical comparison between the kernel formed in the over-category and the literal scheme
pullback model. -/
noncomputable def abelianVarietyTorsionSchemeIsoKernelScheme
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (m : ℤ) :
    (abelianVarietyTorsionScheme A m).left ≅
      abelianVarietyTorsionKernelScheme A m := by
  let e : Spec (.of K) ≅ (𝟙_ (Over (Spec (.of K)))).left :=
    (Over.forget (Spec (.of K))).mapIso
      (abelianVarietyTensorUnitIsoBase (K := K)).symm
  letI : IsIso e.inv := inferInstance
  let q := pullback.map
    (abelianVarietyMultiplication A m).left η[A].left
    (abelianVarietyMultiplication A m).left (abelianVarietyIdentitySection A)
    (𝟙 A.left) e.inv (𝟙 A.left) (by simp) (by
      simp only [Category.comp_id]
      change η[A].left =
        ((abelianVarietyTensorUnitIsoBase (K := K)).hom ≫
          (abelianVarietyTensorUnitIsoBase (K := K)).inv ≫ η[A]).left
      exact congrArg Over.Hom.left
        (Iso.hom_inv_id_assoc
          (abelianVarietyTensorUnitIsoBase (K := K)) η[A]).symm)
  haveI : IsIso q := by
    dsimp only [q]
    apply pullback.map_isIso
  exact PreservesPullback.iso (Over.forget (Spec (.of K)))
      (abelianVarietyMultiplication A m) η[A] ≪≫
        @asIso _ _ _ _ q ‹IsIso q›

/-- Finiteness of multiplication propagates to the literal torsion-kernel scheme by base change. -/
noncomputable instance finite_abelianVarietyTorsionKernelProjection
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (m : ℤ) [IsFinite (abelianVarietyMultiplication A m).left] :
    IsFinite (abelianVarietyTorsionKernelProjection A m) := by
  dsimp only [abelianVarietyTorsionKernelProjection,
    abelianVarietyTorsionKernelScheme]
  infer_instance

/-- Étaleness of multiplication propagates to the literal torsion-kernel scheme by base change. -/
noncomputable instance etale_abelianVarietyTorsionKernelProjection
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (m : ℤ) [Etale (abelianVarietyMultiplication A m).left] :
    Etale (abelianVarietyTorsionKernelProjection A m) := by
  dsimp only [abelianVarietyTorsionKernelProjection,
    abelianVarietyTorsionKernelScheme]
  infer_instance

/-- A functor-of-points torsion element lifts canonically to the scheme-theoretic kernel. -/
def abelianVarietyTorsionSchemeLift
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (X : Over (Spec (.of K))) (m : ℤ) (x : X ⟶ A)
    (hx : x ≫ abelianVarietyMultiplication A m = 1) :
    X ⟶ abelianVarietyTorsionScheme A m :=
  pullback.lift x (toUnit X) (by
    simpa only [CategoryTheory.Hom.one_def] using hx)

@[reassoc (attr := simp)]
theorem abelianVarietyTorsionSchemeLift_fst
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (X : Over (Spec (.of K))) (m : ℤ) (x : X ⟶ A)
    (hx : x ≫ abelianVarietyMultiplication A m = 1) :
    abelianVarietyTorsionSchemeLift A X m x hx ≫ pullback.fst _ _ = x :=
  pullback.lift_fst _ _ _

/-- Every point of the scheme-theoretic kernel projects to an `m`-torsion point. -/
theorem abelianVarietyTorsionScheme_point_fst_comp_multiplication
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (X : Over (Spec (.of K))) (m : ℤ)
    (t : X ⟶ abelianVarietyTorsionScheme A m) :
    (t ≫ pullback.fst (abelianVarietyMultiplication A m) η[A]) ≫
        abelianVarietyMultiplication A m = 1 := by
  dsimp only [abelianVarietyTorsionScheme] at t ⊢
  rw [Category.assoc, pullback.condition]
  change t ≫ pullback.snd _ _ ≫ η[A] = toUnit X ≫ η[A]
  rw [← Category.assoc]
  rw [toUnit_unique (t ≫ pullback.snd _ _) (toUnit X)]

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

/-- Functor-of-points torsion is represented exactly by the scheme-theoretic kernel of
multiplication. -/
noncomputable def abelianVarietyTorsionPointsEquivSchemePoints
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (X : Over (Spec (.of K))) (m : ℤ) :
    {x : X ⟶ A // x ∈ abelianVarietyTorsionPoints A X m} ≃
      (X ⟶ abelianVarietyTorsionScheme A m) where
  toFun x := abelianVarietyTorsionSchemeLift A X m x
    ((mem_abelianVarietyTorsionPoints_iff_comp_eq_one A X m x).mp x.property)
  invFun t :=
    ⟨t ≫ pullback.fst (abelianVarietyMultiplication A m) η[A],
      (mem_abelianVarietyTorsionPoints_iff_comp_eq_one A X m _).mpr
        (abelianVarietyTorsionScheme_point_fst_comp_multiplication A X m t)⟩
  left_inv x := by
    apply Subtype.ext
    exact abelianVarietyTorsionSchemeLift_fst A X m x _
  right_inv t := by
    dsimp only
    apply pullback.hom_ext
    · exact abelianVarietyTorsionSchemeLift_fst A X m _ _
    · apply toUnit_unique

/-- Two functor-of-points values have the same image under multiplication by `m` exactly when
their quotient is `m`-torsion. -/
theorem comp_abelianVarietyMultiplication_eq_iff_div_mem_torsion
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (X : Over (Spec (.of K))) (m : ℤ) (x y : X ⟶ A) :
    x ≫ abelianVarietyMultiplication A m =
        y ≫ abelianVarietyMultiplication A m ↔
      x / y ∈ abelianVarietyTorsionPoints A X m := by
  rw [comp_abelianVarietyMultiplication, comp_abelianVarietyMultiplication,
    mem_abelianVarietyTorsionPoints_iff, div_zpow, div_eq_one]

/-- Fibers of multiplication by `m` are precisely orbits under right translation by `m`-torsion
points, on every functor-of-points group. -/
theorem comp_abelianVarietyMultiplication_eq_iff_exists_torsion_mul
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (X : Over (Spec (.of K))) (m : ℤ) (x y : X ⟶ A) :
    x ≫ abelianVarietyMultiplication A m =
        y ≫ abelianVarietyMultiplication A m ↔
      ∃ t ∈ abelianVarietyTorsionPoints A X m, x = y * t := by
  rw [comp_abelianVarietyMultiplication_eq_iff_div_mem_torsion]
  constructor
  · intro h
    refine ⟨x / y, h, ?_⟩
    rw [mul_comm, div_mul_cancel]
  · rintro ⟨t, ht, rfl⟩
    rw [mem_abelianVarietyTorsionPoints_iff] at ht ⊢
    rw [mul_div_cancel_left]
    exact ht

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

/-- The multiplication-pullback field is contained in the fixed field of the concrete torsion
translation deck group. -/
theorem abelianVarietyMultiplicationPullbackField_le_fixedField_torsionDeckGroup
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (m : ℤ) [IsDominant (abelianVarietyMultiplication A m).left] :
    letI := abelianVarietyFunctionFieldAlgebra A
    abelianVarietyMultiplicationPullbackField A m ≤
      IntermediateField.fixedField (abelianVarietyTorsionDeckGroup A m) := by
  letI := abelianVarietyFunctionFieldAlgebra A
  intro y hy
  change y ∈ IntermediateField.map
    (abelianVarietyMultiplicationFunctionFieldPullback A m) ⊤ at hy
  rw [IntermediateField.mem_map] at hy
  obtain ⟨z, _, rfl⟩ := hy
  rw [IntermediateField.mem_fixedField_iff]
  intro σ hσ
  exact abelianVarietyTorsionDeckGroup_fix_multiplicationPullback A m σ hσ z

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

/-- At every depth, the actual multiplication-pullback image is contained in the fixed field of
the corresponding finite torsion deck group. -/
theorem map_abelianVarietyMultiplicationFunctionFieldPullback_pow_top_le_fixedField
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (m : ℤ) [IsDominant (abelianVarietyMultiplication A m).left]
    (n : ℕ) :
    letI := abelianVarietyFunctionFieldAlgebra A
    IntermediateField.map
        ((abelianVarietyMultiplicationFunctionFieldPullback A m) ^ n) ⊤ ≤
      IntermediateField.fixedField (abelianVarietyTorsionDeckGroup A (m ^ n)) := by
  letI := abelianVarietyFunctionFieldAlgebra A
  rw [map_abelianVarietyMultiplicationFunctionFieldPullback_pow_top]
  exact
    abelianVarietyMultiplicationPullbackField_le_fixedField_torsionDeckGroup A (m ^ n)

/-- The stable multiplication tail is fixed by every multiplication-primary torsion translation.
This is the unconditional inclusion half of the Manin-horizon identity. -/
theorem stableRangeCore_abelianVarietyMultiplicationFunctionFieldPullback_le_fixedField_primary
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (m : ℤ) [IsDominant (abelianVarietyMultiplication A m).left] :
    letI := abelianVarietyFunctionFieldAlgebra A
    stableRangeCore (abelianVarietyMultiplicationFunctionFieldPullback A m) ≤
      IntermediateField.fixedField
        (abelianVarietyMultiplicationPrimaryTorsionDeckGroup A m) := by
  letI := abelianVarietyFunctionFieldAlgebra A
  rw [stableRangeCore,
    abelianVarietyMultiplicationPrimaryTorsionDeckGroup_eq_iSup,
    fixedField_iSup]
  exact iInf_mono fun n =>
    map_abelianVarietyMultiplicationFunctionFieldPullback_pow_top_le_fixedField A m n

end

end GaloisForLFunctions.HTGeometry
