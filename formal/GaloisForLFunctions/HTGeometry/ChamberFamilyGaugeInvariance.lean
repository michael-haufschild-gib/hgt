import GaloisForLFunctions.HTGeometry.UpperEndAffineGauge
import GaloisForLFunctions.HTGeometry.UpperEndRationalCoordinateDifferentialAdjoin

/-!
# The chamber family shares one differential field

Inserting finitely many signed atoms adds a rational function of the coordinate to the transform.
Adding a rational function is an affine gauge with unit multiplier, so it changes neither
differential independence nor hypertranscendence over the embedded coordinate field.

Every member of a chamber family therefore carries the same embedded differential-translation field
and the same generator class modulo the rational coordinate field; only the signs of the inserted
atoms distinguish them, and those are invisible to the unpointed field.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

local instance chamberGaugeDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance chamberGaugeComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance chamberGaugeDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance chamberCoordinateFieldDifferential :
    Differential upperEndRationalCoordinateField :=
  derivationClosedDifferential _ upperEndRationalCoordinateField_derivationClosed

local instance chamberCoordinateFieldDifferentialAlgebra :
    DifferentialAlgebra upperEndRationalCoordinateField upperEndMeroField :=
  ⟨fun x ↦ derivationClosedDifferential_apply
    upperEndRationalCoordinateField
    upperEndRationalCoordinateField_derivationClosed x⟩

/-- **Adding a rational function preserves hypertranscendence.**  The unit-multiplier case of the
affine gauge invariance, which is the form the chamber family needs. -/
theorem hypertranscendentalOver_upperEnd_addRational_iff
    (x : upperEndMeroField) (b : upperEndRationalCoordinateField) :
    HypertranscendentalOver upperEndRationalCoordinateField
        (x + (b : upperEndMeroField)) ↔
      HypertranscendentalOver upperEndRationalCoordinateField x := by
  have h := hypertranscendentalOver_upperEnd_affineGauge_iff x 1 b one_ne_zero
  simpa using h

/-- **Adding rational functions preserves differential independence.**  The family form: a whole
tuple may be shifted by rational functions without changing its differential independence. -/
theorem differentialIndependent_upperEnd_addRational_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → upperEndMeroField) (b : ι → upperEndRationalCoordinateField) :
    DifferentialIndependent upperEndRationalCoordinateField
        (fun i => x i + (b i : upperEndMeroField)) ↔
      DifferentialIndependent upperEndRationalCoordinateField x := by
  have h := differentialIndependent_upperEnd_affineGauge_iff x (fun _ => 1) b
    (fun _ => one_ne_zero)
  simpa using h

end

end GaloisForLFunctions.HTGeometry
