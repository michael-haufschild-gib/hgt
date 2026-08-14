import GaloisForLFunctions.RHTower.FieldOneFiniteStageClassInvariantL2
import GaloisForLFunctions.RHTower.FieldOnePositiveUnitsLogHaar
import GaloisForLFunctions.RHTower.EvenL2LogUnitary
import GaloisForLFunctions.HTGeometry.WeightedDensityL2

/-!
# Common Haar normalization for `w_∞` and `w_S`

The archimedean logarithmic model naturally uses the pushforward of Lebesgue
measure under `exp`, while the literal finite-stage source unitary uses the
canonical Haar measure on positive units.  These Haar measures differ by the
strictly positive Haar scalar.  This file constructs the exact density
unitary between them and hence the source-normalized archimedean unitary

`w_∞ : L²(ℝ)^ev ≃ L²(ℝ_+^*, d*u)`

with precisely the same target and Haar normalization as the literal `w_S`.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory MeasureTheory.Measure IsDedekindDomain
open scoped NNReal

/-- Constant Radon--Nikodym weight from logarithmic Haar to canonical Haar. -/
def fieldOnePositiveUnitsHaarLogWeight (_ : ℝ≥0ˣ) : ℝ :=
  haarScalarFactor fieldOnePositiveUnitsHaarMeasure
    fieldOnePositiveUnitsLogHaarMeasure

theorem fieldOnePositiveUnitsHaar_eq_withDensity :
    fieldOnePositiveUnitsHaarMeasure =
      fieldOnePositiveUnitsLogHaarMeasure.withDensity
        (GaloisForLFunctions.HTGeometry.realDensity
          fieldOnePositiveUnitsHaarLogWeight) := by
  rw [fieldOnePositiveUnitsHaar_eq_smul_logHaar]
  change _ = fieldOnePositiveUnitsLogHaarMeasure.withDensity
    (fun _ => ENNReal.ofReal
      (haarScalarFactor fieldOnePositiveUnitsHaarMeasure
        fieldOnePositiveUnitsLogHaarMeasure : ℝ))
  rw [MeasureTheory.withDensity_const]
  simp

theorem fieldOnePositiveUnitsHaarLogWeight_measurable :
    Measurable fieldOnePositiveUnitsHaarLogWeight :=
  measurable_const

theorem fieldOnePositiveUnitsHaarLogWeight_pos (x : ℝ≥0ˣ) :
    0 < fieldOnePositiveUnitsHaarLogWeight x :=
  fieldOnePositiveUnitsHaar_logScalar_pos

/-- Exact unitary from canonical positive-unit Haar to logarithmic Haar. -/
def fieldOnePositiveUnitsHaarToLogUnitary :
    FieldOnePositiveUnitsL2 ≃ₗᵢ[ℂ]
      Lp ℂ 2 fieldOnePositiveUnitsLogHaarMeasure := by
  change Lp ℂ 2 fieldOnePositiveUnitsHaarMeasure ≃ₗᵢ[ℂ]
    Lp ℂ 2 fieldOnePositiveUnitsLogHaarMeasure
  rw [fieldOnePositiveUnitsHaar_eq_withDensity]
  exact GaloisForLFunctions.HTGeometry.weightedDensityUnitary
    fieldOnePositiveUnitsHaarLogWeight
    fieldOnePositiveUnitsHaarLogWeight_measurable
    fieldOnePositiveUnitsHaarLogWeight_pos

/-- Pullback by `exp` between positive-unit logarithmic Haar and Lebesgue L². -/
def fieldOnePositiveUnitsLogPullbackUnitary :
    Lp ℂ 2 fieldOnePositiveUnitsLogHaarMeasure ≃ₗᵢ[ℂ]
      Lp (α := ℝ) ℂ 2 :=
  RHTower.MellinL2.lpCompMeasurePreservingEquiv
    fieldOnePositiveUnitsExpHomeomorph.toMeasurableEquiv
    fieldOnePositiveUnitsExp_measurePreserving

/-- Source-normalized archimedean `w_∞`, with exactly the target used by the
literal finite-stage `w_S`. -/
def fieldOneEvenToPositiveUnitsHaarUnitary :
    RHTower.evenSubspace ≃ₗᵢ[ℂ] FieldOnePositiveUnitsL2 :=
  RHTower.logEvenUnitary.trans
    (fieldOnePositiveUnitsLogPullbackUnitary.symm.trans
      fieldOnePositiveUnitsHaarToLogUnitary.symm)

end

end GaloisForLFunctions.RHTower
