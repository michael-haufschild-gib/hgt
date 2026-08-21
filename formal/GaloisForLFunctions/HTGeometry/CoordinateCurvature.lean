import GaloisForLFunctions.HTGeometry.ConformalMetricDalembertian

/-!
# Coordinate curvature tensors for smooth pseudo-metric charts

This file supplies the standard coordinate formulas for the Levi--Civita Christoffel symbols,
Riemann tensor, Ricci tensor, scalar curvature, and Einstein tensor of the existing
`SmoothPseudoMetric` structure.  The definitions use the chart inverse already supplied by that
structure.

They are coordinate formulas only; this file does not establish their transformation laws or
connect them to the manifold-valued Levi--Civita development.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators ContDiff

noncomputable section

/-- Coordinate Christoffel symbols `Γⁱ_{jk}` of a smooth pseudo-metric. -/
def coordinateChristoffel {d : ℕ} (g : SmoothPseudoMetric d)
    (x : Fin d → ℝ) (upper lower₁ lower₂ : Fin d) : ℝ :=
  (1 / 2 : ℝ) * ∑ metricIndex,
    g.chart.inverseMetric x upper metricIndex *
      (coordPartial lower₁ (fun y => g.metric y metricIndex lower₂) x +
        coordPartial lower₂ (fun y => g.metric y metricIndex lower₁) x -
          coordPartial metricIndex (fun y => g.metric y lower₁ lower₂) x)

/-- Coordinate Riemann tensor `Rⁱ_{jkl}` with the derivative convention
`∂ₖ Γⁱ_{lj} - ∂ₗ Γⁱ_{kj} + Γⁱ_{km}Γᵐ_{lj} - Γⁱ_{lm}Γᵐ_{kj}`. -/
def coordinateRiemann {d : ℕ} (g : SmoothPseudoMetric d)
    (x : Fin d → ℝ) (upper lower deriv₁ deriv₂ : Fin d) : ℝ :=
  coordPartial deriv₁ (fun y => coordinateChristoffel g y upper deriv₂ lower) x -
    coordPartial deriv₂ (fun y => coordinateChristoffel g y upper deriv₁ lower) x +
      ∑ mid : Fin d, (coordinateChristoffel g x upper deriv₁ mid *
            coordinateChristoffel g x mid deriv₂ lower -
          coordinateChristoffel g x upper deriv₂ mid *
            coordinateChristoffel g x mid deriv₁ lower)

/-- Coordinate Ricci tensor `R_{jl} = Rⁱ_{jil}`. -/
def coordinateRicci {d : ℕ} (g : SmoothPseudoMetric d)
    (x : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun lower₁ lower₂ => ∑ upper,
    coordinateRiemann g x upper lower₁ upper lower₂

/-- Coordinate scalar curvature obtained by contracting the Ricci tensor with the chart inverse. -/
def coordinateScalarCurvature {d : ℕ} (g : SmoothPseudoMetric d)
    (x : Fin d → ℝ) : ℝ :=
  ∑ lower₁, ∑ lower₂,
    g.chart.inverseMetric x lower₁ lower₂ * coordinateRicci g x lower₁ lower₂

/-- Coordinate Einstein tensor `G_{ij} = R_{ij} - R g_{ij}/2`. -/
def coordinateEinsteinTensor {d : ℕ} (g : SmoothPseudoMetric d)
    (x : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun lower₁ lower₂ =>
    coordinateRicci g x lower₁ lower₂ -
      (1 / 2 : ℝ) * coordinateScalarCurvature g x * g.metric x lower₁ lower₂

end

end GaloisForLFunctions.HTGeometry
