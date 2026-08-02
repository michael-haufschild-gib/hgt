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

/-- Categorical multiplication by an integer on an abelian variety. -/
def abelianVarietyMultiplication
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (m : ℤ) : A ⟶ A :=
  (𝟙 A) ^ m

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

/-- Pullback by a dominant multiplication morphism on the abelian function field, as an algebra
endomorphism over the function field of the base.  Dominance is explicit until the multiplication
isogeny theorem is available in the algebraic-geometry library. -/
noncomputable def abelianVarietyMultiplicationFunctionFieldPullback
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (m : ℤ) [IsDominant (abelianVarietyMultiplication A m).left] :=
  A.hom.functionFieldPullbackAlgHomOver
    (abelianVarietyMultiplication A m).left
    (abelianVarietyMultiplication A m).w

/-- `m`-torsion in every functor-of-points group of an abelian variety. -/
def abelianVarietyTorsionPoints
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (X : Over (Spec (.of K))) (m : ℤ) : Subgroup (X ⟶ A) :=
  (zpowGroupHom m).ker

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

/-- Union of all `m^n`-torsion point subgroups. -/
def abelianVarietyMultiplicationPrimaryTorsionPoints
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (X : Over (Spec (.of K))) (m : ℤ) : Subgroup (X ⟶ A) :=
  ⨆ n : ℕ, abelianVarietyTorsionPoints A X (m ^ n)

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

/-- Membership in multiplication-primary torsion is witnessed at one finite level. -/
theorem mem_abelianVarietyMultiplicationPrimaryTorsionPoints_iff
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (X : Over (Spec (.of K))) (m : ℤ) (x : X ⟶ A) :
    x ∈ abelianVarietyMultiplicationPrimaryTorsionPoints A X m ↔
      ∃ n : ℕ, x ∈ abelianVarietyTorsionPoints A X (m ^ n) := by
  exact Subgroup.mem_iSup_of_directed
    (monotone_abelianVarietyTorsionPoints_pow A X m).directed_le

end

end GaloisForLFunctions.HTGeometry
