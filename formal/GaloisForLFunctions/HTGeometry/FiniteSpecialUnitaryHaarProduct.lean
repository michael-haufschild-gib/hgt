import GaloisForLFunctions.HTGeometry.FiniteSpecialUnitaryHaarMeasure
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Independent finite products of special-unitary Haar gates

For a fixed circuit architecture, the paper samples one independent Haar-random
`SU(d)` gate for each gate location.  The finite product measure below is that
law, expressed directly as mathlib's product measure; its probability proof is
therefore inherited from the factor Haar probabilities.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Independent normalized Haar choices of one finite special-unitary gate at
every index in a finite gate set. -/
def finiteSpecialUnitaryHaarProduct
    (κ ι : Type*) [Fintype κ] [Fintype ι] [DecidableEq ι] :
    Measure (κ → Matrix.specialUnitaryGroup ι ℂ) :=
  Measure.pi fun _ => finiteSpecialUnitaryHaar ι

/-- Independent finite products of normalized special-unitary Haar gates are
probability measures. -/
noncomputable instance finiteSpecialUnitaryHaarProductIsProbabilityMeasure
    (κ ι : Type*) [Fintype κ] [Fintype ι] [DecidableEq ι] :
    IsProbabilityMeasure (finiteSpecialUnitaryHaarProduct κ ι) := by
  unfold finiteSpecialUnitaryHaarProduct
  infer_instance

/-- The independent gate law gives full mass to its sample space. -/
theorem finiteSpecialUnitaryHaarProduct_apply_univ
    (κ ι : Type*) [Fintype κ] [Fintype ι] [DecidableEq ι] :
    finiteSpecialUnitaryHaarProduct κ ι Set.univ = 1 :=
  measure_univ

end

end GaloisForLFunctions.HTGeometry
