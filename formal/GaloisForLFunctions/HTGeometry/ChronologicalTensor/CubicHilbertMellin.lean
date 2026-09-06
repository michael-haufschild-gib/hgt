import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicHilbertTrace
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicCuspMellin

/-!
# Zeta zeros in the analytic Hilbert heat response

The kernel uses the basis-independent analytic operator trace of the actual
physical Hilbert flow and the actual continuous reference integral. Their
proved identification with the cusp kernel transfers absolute Mellin
convergence, analyticity, the Gamma-zeta formula, and all strip zero orders.
-/

open Complex Set MeasureTheory
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section

attribute [local instance] cubicGradedLineNormedGroup cubicGradedLineInnerProductSpace
  cubicGradedLine_complete

def cubicHilbertResponseKernel (t : ℝ) : ℂ :=
  if 0<t then ((cubicCuspContinuousHeat t-
    ContinuousLinearMap.opTrace (cubicHilbertHeatOperator (Real.log t)) : ℝ) : ℂ) else 0

theorem cubicHilbertResponseKernel_eq : cubicHilbertResponseKernel=cubicCuspKernel := by
  funext t
  simp only [cubicHilbertResponseKernel,cubicCuspKernel,cubicHilbertHeatOperator_trace]

theorem cubicHilbertResponseKernel_converges :
    ∀ s ∈ fusionMellinStrip, MellinConvergent cubicHilbertResponseKernel s := by
  rw [cubicHilbertResponseKernel_eq]
  exact cubicCuspKernel_converges

theorem cubicHilbertResponseKernel_mellin :
    EqOn (mellin cubicHilbertResponseKernel) (fun s => -Complex.Gamma s*riemannZeta s)
      fusionMellinStrip := by
  rw [cubicHilbertResponseKernel_eq]
  exact cubicCuspKernel_mellin

theorem cubicHilbertResponseKernel_analytic :
    AnalyticOnNhd ℂ (mellin cubicHilbertResponseKernel) fusionMellinStrip := by
  rw [cubicHilbertResponseKernel_eq]
  exact cubicCuspKernel_mellin_analytic

theorem cubicHilbertResponseKernel_zeroLocus :
    {s ∈ fusionMellinStrip | mellin cubicHilbertResponseKernel s=0}=
      {s ∈ fusionMellinStrip | riemannZeta s=0} := by
  rw [cubicHilbertResponseKernel_eq]
  exact cubicCuspKernel_zeroLocus

theorem cubicHilbertResponseKernel_zeroMultiplicity :
    EqOn (analyticOrderAt (mellin cubicHilbertResponseKernel))
      (analyticOrderAt riemannZeta) fusionMellinStrip := by
  rw [cubicHilbertResponseKernel_eq]
  exact cubicCuspKernel_zeroMultiplicity

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
