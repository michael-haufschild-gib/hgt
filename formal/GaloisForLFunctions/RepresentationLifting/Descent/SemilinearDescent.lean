import GaloisForLFunctions.RepresentationLifting.Descent.SemilinearInvariantSpan
import Mathlib.RepresentationTheory.Invariants
import Mathlib.Algebra.Module.RingHom

/-!
# Descent to the fixed field

A semilinear representation of a finite faithful group of field automorphisms
has invariant vectors of the original dimension over the fixed field. The
coordinate equivalence identifies actual representation invariants with a
finite power of that field, rather than merely comparing dimensions.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting
open Module
variable (G L V : Type*) [Group G] [Field L]
  [MulSemiringAction G L]
  [AddCommGroup V] [Module L V] [DistribMulAction G V] [SMulDistribClass G L V]

/-- Restriction of scalar multiplication to the fixed field. -/
abbrev semilinearFixedFieldModule : Module (FixedPoints.subfield G L) V :=
  Module.compHom V (algebraMap (FixedPoints.subfield G L) L)

attribute [local instance] semilinearFixedFieldModule

/-- Fixed-field restriction agrees with the original field action. -/
local instance semilinearFixedFieldTower : IsScalarTower (FixedPoints.subfield G L) L V where
  smul_assoc a b v := by
    change ((a : L) * b) • v = (a : L) • (b • v)
    exact mul_smul _ _ _

/-- The group action commutes with multiplication by fixed scalars. -/
local instance semilinearFixedFieldComm : SMulCommClass G (FixedPoints.subfield G L) V where
  smul_comm g a v := by
    change g • ((a : L) • v) = (a : L) • (g • v)
    rw [smul_distrib_smul, a.property g]

/-- Restricting semilinear scalars to the fixed field gives an ordinary representation. -/
def semilinearFixedRepresentation : Representation (FixedPoints.subfield G L) G V :=
  @Representation.ofDistribMulAction (FixedPoints.subfield G L) G V
    _ _ _ (semilinearFixedFieldModule G L V) _ (semilinearFixedFieldComm G L V)

variable [Fintype G] [FaithfulSMul G L] [FiniteDimensional L V]

/-- Coordinates in an invariant basis. -/
def semilinearCoordinateEquiv : V ≃ₗ[L] (Fin (Module.finrank L V) → L) :=
  (semilinear_exists_coordinate_equiv G L V).choose

theorem semilinearCoordinateEquiv_action (g : G) (v : V) (i : Fin (Module.finrank L V)) :
    semilinearCoordinateEquiv G L V (g • v) i =
      g • semilinearCoordinateEquiv G L V v i :=
  (semilinear_exists_coordinate_equiv G L V).choose_spec g v i

/-- Actual invariant vectors are exactly fixed-field coordinate vectors. -/
def semilinearFixedCoordinates :
    (semilinearFixedRepresentation G L V).invariants ≃ₗ[FixedPoints.subfield G L]
      (Fin (Module.finrank L V) → FixedPoints.subfield G L) where
  toFun v i := ⟨semilinearCoordinateEquiv G L V v i, fun g => by
    rw [← semilinearCoordinateEquiv_action]
    exact congrArg (fun w => semilinearCoordinateEquiv G L V w i) (v.property g)⟩
  invFun f := ⟨(semilinearCoordinateEquiv G L V).symm (fun i => (f i : L)), by
    intro g
    apply (semilinearCoordinateEquiv G L V).injective
    ext i
    change semilinearCoordinateEquiv G L V
      (g • (semilinearCoordinateEquiv G L V).symm (fun j => (f j : L))) i = _
    simp only [semilinearCoordinateEquiv_action, LinearEquiv.apply_symm_apply]
    exact (f i).property g⟩
  left_inv v := by
    apply Subtype.ext
    exact (semilinearCoordinateEquiv G L V).symm_apply_apply v
  right_inv f := by
    funext i
    apply Subtype.ext
    exact congrFun ((semilinearCoordinateEquiv G L V).apply_symm_apply
      (fun j => (f j : L))) i
  map_add' v w := by
    ext i
    change semilinearCoordinateEquiv G L V (v.val + w.val) i =
      semilinearCoordinateEquiv G L V v.val i + semilinearCoordinateEquiv G L V w.val i
    simp only [map_add, Pi.add_apply]
  map_smul' a v := by
    ext i
    change semilinearCoordinateEquiv G L V ((a : L) • v.val) i =
      (a : L) • semilinearCoordinateEquiv G L V v.val i
    simp only [map_smul, Pi.smul_apply]

/-- Galois descent preserves dimension, over the fixed field on invariants. -/
theorem semilinearFixed_finrank :
    Module.finrank (FixedPoints.subfield G L) (semilinearFixedRepresentation G L V).invariants =
      Module.finrank L V := by
  simpa using (semilinearFixedCoordinates G L V).finrank_eq

end GaloisForLFunctions.RepresentationLifting
