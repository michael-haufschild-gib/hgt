import GaloisForLFunctions.HTGeometry.CriticalObservationField
import Mathlib.FieldTheory.Normal.Closure

/-!
# Geometric monodromy of the actual critical function-field extension

This module fixes the field-theoretic object whose permutation group is the geometric monodromy
of the critical raw/reciprocal observation map.  The source field is embedded in an algebraic
closure of itself, its normal closure is taken over the actual observation field, and the Galois
group of that normal closure acts on all observation-field embeddings of the source.

No abstract cover datum is introduced: every field below is built from `criticalObservationField`
and `criticalSourceField`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option synthInstance.maxHeartbeats 100000

/-- An algebraic closure containing the actual critical source field. -/
abbrev criticalSourceAlgebraicClosure (K : Type*) [Field K] (m n : ℕ) :=
  AlgebraicClosure (criticalSourceField K m n)

/-- The observation field acts on the chosen algebraic closure through the actual source-field
inclusion. -/
noncomputable instance criticalObservationAlgebraicClosureAlgebra
    (K : Type*) [Field K] (m n : ℕ) :
    Algebra (criticalObservationField K m n)
      (criticalSourceAlgebraicClosure K m n) :=
  ((algebraMap (criticalSourceField K m n)
      (criticalSourceAlgebraicClosure K m n)).comp
    (algebraMap (criticalObservationField K m n)
      (criticalSourceField K m n))).toAlgebra

/-- Normal closure of the actual critical source field over the actual observation field. -/
abbrev criticalNormalClosure (K : Type*) [Field K] (m n : ℕ) :=
  IntermediateField.normalClosure
    (criticalObservationField K m n) (criticalSourceField K m n)
      (criticalSourceAlgebraicClosure K m n)

/-- Geometric sheets: embeddings of the actual critical source into its normal closure over the
actual critical observation field. -/
abbrev criticalGeometricSheet (K : Type*) [Field K] (m n : ℕ) :=
  criticalSourceField K m n →ₐ[criticalObservationField K m n]
    criticalNormalClosure K m n

/-- Galois group of the normal closure acts on the geometric sheets by postcomposition. -/
noncomputable def criticalNormalClosureAction (K : Type*) [Field K] (m n : ℕ) :
    (criticalNormalClosure K m n ≃ₐ[criticalObservationField K m n]
      criticalNormalClosure K m n) →*
      Equiv.Perm (criticalGeometricSheet K m n) where
  toFun σ :=
    { toFun := fun f => σ.toAlgHom.comp f
      invFun := fun f => σ.symm.toAlgHom.comp f
      left_inv := fun f => by
        apply AlgHom.ext
        intro x
        simp
      right_inv := fun f => by
        apply AlgHom.ext
        intro x
        simp }
  map_one' := by
    apply Equiv.ext
    intro f
    apply AlgHom.ext
    intro x
    rfl
  map_mul' σ τ := by
    apply Equiv.ext
    intro f
    apply AlgHom.ext
    intro x
    rfl

/-- **Actual geometric monodromy subgroup** of the critical horizon map. -/
noncomputable def criticalGeometricMonodromy (K : Type*) [Field K] (m n : ℕ) :
    Subgroup (Equiv.Perm (criticalGeometricSheet K m n)) :=
  MonoidHom.range (criticalNormalClosureAction K m n)

end

end GaloisForLFunctions.HTGeometry
