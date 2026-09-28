import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Fundamental groups of continuous monoid homomorphisms

Continuous monoid homomorphisms preserve the identity basepoint. Their induced
fundamental-group homomorphisms preserve composition without basepoint casts
in the public interface.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] [Monoid X] [Monoid Y] [Monoid Z]

/-- A continuous monoid homomorphism induces a homomorphism of fundamental
groups based at the identity. -/
def fundamentalGroupContinuousHom (f : X →ₜ* Y) :
    FundamentalGroup X 1 →* FundamentalGroup Y 1 :=
  FundamentalGroup.mapOfEq f.toContinuousMap f.map_one

/-- The induced map acts by composing representative loops. -/
theorem fundamentalGroupContinuousHom_mk (f : X →ₜ* Y) (p : Path (1 : X) 1) :
    fundamentalGroupContinuousHom f (Path.Homotopic.Quotient.mk p) =
      Path.Homotopic.Quotient.mk
        ((p.map f.continuous).cast f.map_one.symm f.map_one.symm) := by
  exact FundamentalGroup.mapOfEq_apply _ _ _

/-- Induced fundamental-group homomorphisms preserve composition. -/
theorem fundamentalGroupContinuousHom_comp (g : Y →ₜ* Z) (f : X →ₜ* Y) :
    fundamentalGroupContinuousHom (g.comp f) =
      (fundamentalGroupContinuousHom g).comp (fundamentalGroupContinuousHom f) := by
  ext p
  induction p using Path.Homotopic.Quotient.ind with
  | mk p =>
    simp only [MonoidHom.comp_apply, fundamentalGroupContinuousHom_mk]
    congr 1

/-- The identity continuous homomorphism induces the identity on loop classes. -/
theorem fundamentalGroupContinuousHom_id :
    fundamentalGroupContinuousHom (ContinuousMonoidHom.id X) =
      MonoidHom.id (FundamentalGroup X 1) := by
  ext p
  induction p using Path.Homotopic.Quotient.ind with
  | mk p =>
    rw [fundamentalGroupContinuousHom_mk]
    rfl

end

end GaloisForLFunctions.HTGeometry
