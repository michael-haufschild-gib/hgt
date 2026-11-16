import GaloisForLFunctions.HilbertMetric.Spectral.ClippedTrace
import GaloisForLFunctions.HTGeometry.PureBipartiteEntanglementEntropy

/-!
# Clipped Schmidt energy

The two reduced matrices of a pure bipartite state share every clipped quadratic
energy. Centering the spectrum at one introduces precisely the dimension
difference. The block bound also detects deviation from a maximally mixed
unnormalized reduction, without normalization or full-rank assumptions.
-/

open Matrix
open scoped NNReal
namespace GaloisForLFunctions.HilbertMetric
open Clipped HTGeometry
noncomputable section
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Subsystems of any pure state have the same clipped quadratic energy. -/
theorem pureStateReduced_clippedEnergy (ψ : ι × κ → ℂ) (c : ℝ≥0) :
    energy c (pureStateReducedLeft ψ) = energy c (pureStateReducedRight ψ) :=
  energy_gram (bipartitePureStateMatrix ψ) c

/-- Zero Schmidt modes contribute the exact ambient-dimension correction. -/
theorem pureStateReduced_clippedDefect (ψ : ι × κ → ℂ) (τ : ℝ≥0) :
    defectEnergy τ (pureStateReducedLeft ψ) - Fintype.card ι =
      defectEnergy τ (pureStateReducedRight ψ) - Fintype.card κ :=
  defectEnergy_gram (bipartitePureStateMatrix ψ) τ

/-- Purity and total mass give a clipped lower bound for either reduction. -/
theorem pureStateReduced_clippedDefect_lower (ψ : ι × κ → ℂ) (τ : ℝ≥0) :
    min ((trace (pureStateReducedLeft ψ * pureStateReducedLeft ψ)).re -
      2 * (trace (pureStateReducedLeft ψ)).re + Fintype.card ι) ((τ : ℝ) ^ 2) ≤
        defectEnergy τ (pureStateReducedLeft ψ) :=
  defectEnergy_min_bound (pureStateReducedLeft_isHermitian ψ) τ

#print axioms pureStateReduced_clippedEnergy
#print axioms pureStateReduced_clippedDefect
#print axioms pureStateReduced_clippedDefect_lower

end
end GaloisForLFunctions.HilbertMetric
