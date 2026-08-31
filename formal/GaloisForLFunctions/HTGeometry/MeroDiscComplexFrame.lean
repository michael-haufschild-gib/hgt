import GaloisForLFunctions.HTGeometry.MeroScalingDifferential
import GaloisForLFunctions.HTGeometry.AnalyticJetFieldBridge

/-!
# The complex differential frame of a disc germ field

The meromorphic germ field of an open connected disc is a complex algebra through the constant
germs, its derivation kills the constants, and the contracting scaling fixes them.  On the
coordinate germ the scaling acts by the scaling constant.

These are the four data the contracting Ritt bridge consumes: a complex differential field, a
complex algebra endomorphism twisting the derivation by a constant, and a coordinate on which that
endomorphism acts by the same constant.
-/

namespace GaloisForLFunctions.HTGeometry

open Bottcher Set Filter Topology
open scoped Differential

noncomputable section

/-- The complex algebra structure on a meromorphic germ field, through the constant germs. -/
@[reducible] def meroComplexAlgebra (U : Set ℂ) [IsDomain (analyticSubring U)] : Algebra ℂ (meroField U) :=
  ((algebraMap (analyticSubring U) (meroField U)).comp (constToAnalytic U)).toAlgebra

theorem meroComplexAlgebra_algebraMap (U : Set ℂ) [IsDomain (analyticSubring U)] (a : ℂ) :
    letI := meroComplexAlgebra U
    algebraMap ℂ (meroField U) a
      = algebraMap (analyticSubring U) (meroField U) (constToAnalytic U a) := rfl

theorem analyticSubringDeriv_constToAnalytic {U : Set ℂ} (hUo : IsOpen U) (a : ℂ) :
    analyticSubringDeriv hUo (constToAnalytic U a) = 0 := by
  apply Subtype.ext
  change analyticGermDeriv hUo ((constToAnalytic U a : analyticSubring U) : Germ (𝓟 U) ℂ) = 0
  have hcoe : ((constToAnalytic U a : analyticSubring U) : Germ (𝓟 U) ℂ)
      = ((fun _ : ℂ => a : ℂ → ℂ) : Germ (𝓟 U) ℂ) := rfl
  rw [hcoe]
  change ((deriv (fun _ : ℂ => a) : ℂ → ℂ) : Germ (𝓟 U) ℂ) = 0
  rw [deriv_const']
  rfl

/-- **The meromorphic derivation kills the constants.** -/
theorem meroDeriv_algebraMap_complex {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (a : ℂ) :
    letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
    letI := meroComplexAlgebra U
    letI := meroFieldDifferential hUo hUc hUne
    (algebraMap ℂ (meroField U) a)′ = 0 := by
  letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
  letI := meroComplexAlgebra U
  letI := meroFieldDifferential hUo hUc hUne
  rw [meroComplexAlgebra_algebraMap, meroFieldDifferential_algebraMap,
    analyticSubringDeriv_constToAnalytic, map_zero]

/-- **The scaling fixes the constants.** -/
theorem scaleMero_algebraMap_complex {U : Set ℂ} {mu : ℂ} (hmu : mu ≠ 0)
    (hmaps : Set.MapsTo (scaleMap mu) U U)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (a : ℂ) :
    letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
    letI := meroComplexAlgebra U
    scaleMero hmu hmaps hUo hUc hUne (algebraMap ℂ (meroField U) a)
      = algebraMap ℂ (meroField U) a := by
  letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
  letI := meroComplexAlgebra U
  rw [meroComplexAlgebra_algebraMap, scaleMero,
    Bottcher.precompMeroMap_algebraMap, Bottcher.precompAnalyticMap_constToAnalytic]

/-- The coordinate germ of a domain. -/
def coordMero (U : Set ℂ) [IsDomain (analyticSubring U)] : meroField U :=
  analyticMeroElement (fun w : ℂ => w) (fun _ _ => analyticAt_id)

/-- **The scaling acts on the coordinate by the scaling constant.** -/
theorem scaleMero_coordMero {U : Set ℂ} {mu : ℂ} (hmu : mu ≠ 0)
    (hmaps : Set.MapsTo (scaleMap mu) U U)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) :
    letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
    letI := meroComplexAlgebra U
    scaleMero hmu hmaps hUo hUc hUne (coordMero U)
      = algebraMap ℂ (meroField U) mu * coordMero U := by
  letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
  letI := meroComplexAlgebra U
  rw [coordMero, analyticMeroElement, scaleMero, Bottcher.precompMeroMap_algebraMap,
    meroComplexAlgebra_algebraMap, ← map_mul]
  congr 1

end

end GaloisForLFunctions.HTGeometry
