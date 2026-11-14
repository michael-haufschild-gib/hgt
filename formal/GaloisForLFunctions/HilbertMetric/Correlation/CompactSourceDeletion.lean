import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Exceptional compact sources

The exact square-integral expansion turns Cauchy--Schwarz into a deletion
bound for continuous compactly supported sources. Integrability is proved
from the source type, including when either energy vanishes.
-/

open MeasureTheory
open scoped CompactlySupported

namespace GaloisForLFunctions.HilbertMetric
noncomputable section

/-- The real square-integral energy of a compact source. -/
def compactEnergy (f : C_c(ℝ, ℝ)) : ℝ := ∫ u, f u ^ 2

theorem compactEnergy_nonneg (f : C_c(ℝ, ℝ)) : 0 ≤ compactEnergy f :=
  integral_nonneg fun _ => sq_nonneg _

private theorem square_integrable (f : C_c(ℝ, ℝ)) : Integrable (fun u => f u ^ 2) :=
  (f.continuous.pow 2).integrable_of_hasCompactSupport (f.hasCompactSupport.pow (by omega))

/-- Polarization for actual compact sources, with no integrability premises. -/
theorem compactEnergy_sub (f g : C_c(ℝ, ℝ)) :
    compactEnergy (f - g) = compactEnergy f + compactEnergy g - 2 * ∫ u, f u * g u := by
  have hi : Integrable (fun u => f u * g u) :=
    (f.continuous.mul g.continuous).integrable_of_hasCompactSupport f.hasCompactSupport.mul_right
  have he : (fun u => (f - g) u ^ 2) = fun u => f u ^ 2 + g u ^ 2 - 2 * (f u * g u) := by
    funext u
    change (f u - g u) ^ 2 = _
    ring
  unfold compactEnergy
  rw [he, integral_sub ((square_integrable f).add (square_integrable g)) (hi.const_mul 2),
    integral_add (square_integrable f) (square_integrable g), integral_const_mul]

/-- Sharp centered deletion inequality for a compact-source energy. -/
theorem compactEnergy_deletion_centered (f g : C_c(ℝ, ℝ)) :
    (compactEnergy (f - g) - compactEnergy f - compactEnergy g) ^ 2 ≤
      4 * compactEnergy f * compactEnergy g := by
  have h := HTGeometry.sq_integral_mul_le f.continuous.aestronglyMeasurable
    g.continuous.aestronglyMeasurable (square_integrable f) (square_integrable g)
  change (∫ u, f u * g u) ^ 2 ≤ compactEnergy f * compactEnergy g at h
  rw [compactEnergy_sub]
  nlinarith only [h]

/-- Absolute energy error paid by the exceptional source and its mixed term. -/
theorem compactEnergy_deletion_error (f g : C_c(ℝ, ℝ)) :
    |compactEnergy (f - g) - compactEnergy f| ≤
      compactEnergy g + 2 * Real.sqrt (compactEnergy f * compactEnergy g) := by
  have h := HTGeometry.sq_integral_mul_le f.continuous.aestronglyMeasurable
    g.continuous.aestronglyMeasurable (square_integrable f) (square_integrable g)
  have ha : |∫ u, f u * g u| ≤ Real.sqrt (compactEnergy f * compactEnergy g) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt h
  have hb := abs_le.mp ha
  rw [compactEnergy_sub, abs_le]
  constructor <;> linarith [compactEnergy_nonneg g]

end
end GaloisForLFunctions.HilbertMetric

#print axioms GaloisForLFunctions.HilbertMetric.compactEnergy_deletion_centered
#print axioms GaloisForLFunctions.HilbertMetric.compactEnergy_deletion_error
