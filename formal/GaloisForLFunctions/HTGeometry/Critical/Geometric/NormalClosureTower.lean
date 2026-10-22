import GaloisForLFunctions.HTGeometry.Critical.Geometric.Monodromy

/-!
# Normality, algebraicity and separability of the critical normal closure

The observation field has characteristic zero and the source field is finite over it, so the
chosen algebraic closure is algebraic and normal over the observation field, and the normal
closure inside it is normal and separable.  These four facts are the standing hypotheses of every
valuation- and inertia-level statement about the Schur place.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option synthInstance.maxHeartbeats 200000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}

/-- The chosen algebraic closure of the source field is algebraic over the observation field. -/
theorem criticalSourceAlgebraicClosure_isAlgebraic (hm : 0 < m) (hn : 0 < n) :
    Algebra.IsAlgebraic (criticalObservationField K m n)
      (criticalSourceAlgebraicClosure K m n) := by
  letI : FiniteDimensional (criticalObservationField K m n) (criticalSourceField K m n) :=
    criticalSourceField_finiteDimensional_criticalObservationField K hm hn
  letI : IsScalarTower (criticalObservationField K m n) (criticalSourceField K m n)
      (criticalSourceAlgebraicClosure K m n) :=
    AlgebraicClosure.instIsScalarTower (criticalSourceField K m n)
  exact Algebra.IsAlgebraic.trans (criticalObservationField K m n)
    (criticalSourceField K m n) (criticalSourceAlgebraicClosure K m n)

/-- The chosen algebraic closure of the source field is normal over the observation field: it is
algebraically closed, so every minimal polynomial splits. -/
theorem criticalSourceAlgebraicClosure_normal (hm : 0 < m) (hn : 0 < n) :
    Normal (criticalObservationField K m n) (criticalSourceAlgebraicClosure K m n) := by
  letI := criticalSourceAlgebraicClosure_isAlgebraic K hm hn
  exact { splits' _ := IsAlgClosed.splits _ }

/-- The normal closure of the source field is normal over the observation field. -/
theorem criticalNormalClosure_normal (hm : 0 < m) (hn : 0 < n) :
    Normal (criticalObservationField K m n) (criticalNormalClosure K m n) := by
  letI : FiniteDimensional (criticalObservationField K m n) (criticalSourceField K m n) :=
    criticalSourceField_finiteDimensional_criticalObservationField K hm hn
  letI : Algebra.IsSeparable (criticalObservationField K m n) (criticalSourceField K m n) :=
    inferInstance
  letI : IsScalarTower (criticalObservationField K m n) (criticalSourceField K m n)
      (criticalSourceAlgebraicClosure K m n) :=
    AlgebraicClosure.instIsScalarTower (criticalSourceField K m n)
  letI := criticalSourceAlgebraicClosure_isAlgebraic K hm hn
  letI := criticalSourceAlgebraicClosure_normal K hm hn
  exact normalClosure.normal (criticalObservationField K m n)
    (criticalSourceField K m n) (criticalSourceAlgebraicClosure K m n)

omit [CharZero K] [IsAlgClosed K] in
/-- Source-field algebra structure on the normal closure, named for the same reason. -/
noncomputable instance criticalNormalClosureSourceAlgebra :
    Algebra (criticalSourceField K m n) (criticalNormalClosure K m n) :=
  inferInstance

omit [CharZero K] [IsAlgClosed K] in
/-- Scalar tower from the observation field through the source field into the chosen algebraic
closure, named for the same reason. -/
noncomputable instance criticalObservationSourceAlgebraicClosureTower :
    IsScalarTower (criticalObservationField K m n) (criticalSourceField K m n)
      (criticalSourceAlgebraicClosure K m n) :=
  inferInstance

omit [CharZero K] [IsAlgClosed K] in
/-- Observation-field algebra structure on the field range of a sheet, named for the same
reason. -/
noncomputable instance criticalGeometricSheetFieldRangeAlgebra
    (σ : criticalGeometricSheet K m n) :
    Algebra (criticalObservationField K m n) ↥(AlgHom.fieldRange σ) :=
  inferInstance

omit [CharZero K] [IsAlgClosed K] in
/-- Observation-field algebra structure on the normal closure, named so that instance search
closes it in one step instead of rebuilding the intermediate-field tower. -/
noncomputable instance criticalNormalClosureObservationAlgebra :
    Algebra (criticalObservationField K m n) (criticalNormalClosure K m n) :=
  inferInstance

omit [IsAlgClosed K] in
/-- The observation field has characteristic zero, inherited from the ground field. -/
theorem criticalObservationField_charZero :
    CharZero (criticalObservationField K m n) :=
  Algebra.charZero_of_charZero K _

/-- The normal closure is integral over the observation field, being finite over it. -/
theorem criticalNormalClosure_isIntegral (hm : 0 < m) (hn : 0 < n) :
    Algebra.IsIntegral (criticalObservationField K m n) (criticalNormalClosure K m n) := by
  letI : FiniteDimensional (criticalObservationField K m n) (criticalNormalClosure K m n) :=
    criticalNormalClosure_finiteDimensional K hm hn
  exact Algebra.IsIntegral.of_finite _ _

/-- An integral extension of a characteristic-zero field is separable, so the normal closure is
separable over the observation field. -/
theorem criticalNormalClosure_isSeparable (hm : 0 < m) (hn : 0 < n) :
    Algebra.IsSeparable (criticalObservationField K m n) (criticalNormalClosure K m n) := by
  letI := criticalObservationField_charZero K (m := m) (n := n)
  letI := criticalNormalClosure_isIntegral K hm hn
  exact Algebra.IsSeparable.of_integral _ _

end

end GaloisForLFunctions.HTGeometry
