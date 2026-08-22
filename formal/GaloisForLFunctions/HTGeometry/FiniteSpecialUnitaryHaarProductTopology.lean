import GaloisForLFunctions.HTGeometry.FiniteSpecialUnitaryHaarTopology
import GaloisForLFunctions.HTGeometry.FiniteSpecialUnitaryHaarProduct

/-!
# Topological Haar structure of independent finite special-unitary gate laws

The independent finite product of normalized `SU(d)` Haar laws is itself Haar
on the pointwise gate-tuple group, and is bi-invariant.  This is the exact
probability space of a fixed finite circuit architecture.
-/

open MeasureTheory MeasureTheory.Measure TopologicalSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- An independent finite tuple of normalized special-unitary Haar gates is
itself a Haar measure on the pointwise gate-tuple group. -/
noncomputable instance finiteSpecialUnitaryHaarProductIsHaarMeasure
    (κ ι : Type*) [Fintype κ] [Fintype ι] [DecidableEq ι] :
    IsHaarMeasure (finiteSpecialUnitaryHaarProduct κ ι) := by
  unfold finiteSpecialUnitaryHaarProduct
  infer_instance

/-- Right translation preserves the independent finite product Haar law. -/
theorem map_finiteSpecialUnitaryHaarProduct_mul_right
    {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (V : κ → Matrix.specialUnitaryGroup ι ℂ) :
    Measure.map (fun U : κ → Matrix.specialUnitaryGroup ι ℂ => U * V)
        (finiteSpecialUnitaryHaarProduct κ ι) =
      finiteSpecialUnitaryHaarProduct κ ι := by
  have hprob :
      Measure.map (fun U : κ → Matrix.specialUnitaryGroup ι ℂ => U * V)
          (finiteSpecialUnitaryHaarProduct κ ι) Set.univ = 1 := by
    rw [Measure.map_apply_of_aemeasurable
      (measurable_mul_const V).aemeasurable MeasurableSet.univ]
    exact finiteSpecialUnitaryHaarProduct_apply_univ κ ι
  have hscalar := isMulLeftInvariant_eq_smul_of_regular
    (Measure.map (fun U : κ → Matrix.specialUnitaryGroup ι ℂ => U * V)
      (finiteSpecialUnitaryHaarProduct κ ι))
    (finiteSpecialUnitaryHaarProduct κ ι)
  have hfactor :
      haarScalarFactor
          (Measure.map (fun U : κ → Matrix.specialUnitaryGroup ι ℂ => U * V)
            (finiteSpecialUnitaryHaarProduct κ ι))
          (finiteSpecialUnitaryHaarProduct κ ι) = 1 := by
    have huniv := congrArg
      (fun μ : Measure (κ → Matrix.specialUnitaryGroup ι ℂ) => μ Set.univ)
      hscalar
    rw [hprob, Measure.smul_apply,
      finiteSpecialUnitaryHaarProduct_apply_univ] at huniv
    simpa using huniv.symm
  rw [hfactor] at hscalar
  simpa using hscalar

/-- Independent finite special-unitary Haar gates are right invariant as a
gate-tuple law. -/
noncomputable instance finiteSpecialUnitaryHaarProductIsMulRightInvariant
    (κ ι : Type*) [Fintype κ] [Fintype ι] [DecidableEq ι] :
    IsMulRightInvariant (finiteSpecialUnitaryHaarProduct κ ι) where
  map_mul_right_eq_self := map_finiteSpecialUnitaryHaarProduct_mul_right

end

end GaloisForLFunctions.HTGeometry
