import GaloisForLFunctions.HTGeometry.MultiplierClosedGraph
import GaloisForLFunctions.HTGeometry.CarlemanOperatorBound
import Mathlib.Analysis.Fourier.LpSpace

/-!
# The cutoff graph relation and its commutator defect

A Fourier multiplier with an arbitrary measurable symbol has closed graph on `L²`, because the
graph of multiplication is closed and the `L²` Fourier transform is a homeomorphism.  Adding the
support condition keeps it closed, so the graph domain of Suzuki's finite-aperture symbol is
complete.

Cutting a solution of the graph relation to the physical interval produces exactly one defect, the
commutator with the cutoff: `H(Pc) = P(Hc) + [H,P]c`, and on the interior the defect is
`-P H (1-P) c`.  The bounded part of the symbol contributes at most `2‖q‖∞`; the logarithmic part
contributes the cross-boundary Carleman block, whose kernel `1/(s+t)` is bounded on `L²` with norm
at most `π`.
-/

open MeasureTheory Filter Topology
open scoped FourierTransform

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- **`(19)`: the graph of a Fourier multiplier is closed on `L²`.**  No bound on the symbol is
used, so this covers the growing logarithmic weight. -/
theorem isClosed_fourierMultiplierGraph (m : ℝ → ℂ) :
    IsClosed {p : Lp ℂ 2 (volume : Measure ℝ) × Lp ℂ 2 (volume : Measure ℝ) |
      ((𝓕 p.2 : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
        =ᵐ[volume] fun ξ => m ξ * ((𝓕 p.1 : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ} := by
  have hcont : Continuous fun p : Lp ℂ 2 (volume : Measure ℝ) × Lp ℂ 2 (volume : Measure ℝ) =>
      ((𝓕 p.1 : Lp ℂ 2 (volume : Measure ℝ)), (𝓕 p.2 : Lp ℂ 2 (volume : Measure ℝ))) := by
    exact ((Lp.fourierTransformₗᵢ ℝ ℂ).continuous.comp continuous_fst).prodMk
      ((Lp.fourierTransformₗᵢ ℝ ℂ).continuous.comp continuous_snd)
  exact (isClosed_multiplierGraph m).preimage hcont

/-- **`(23)`: cutting the graph relation leaves exactly the cutoff commutator.** -/
theorem cutoff_graph_identity {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A P : H →L[ℂ] H) (c : H) :
    A (P c) = P (A c) + (A (P c) - P (A c)) := by
  abel

/-- **`(10)`: on the interior the cutoff defect is the exterior transport.** -/
theorem cutoff_defect_eq {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A P : H →L[ℂ] H) (hP : ∀ x, P (P x) = P x) (c : H) :
    P (A (P c) - P (A c)) = -(P (A (c - P c))) := by
  have hlin : A (c - P c) = A c - A (P c) := by
    rw [map_sub]
  rw [hlin, map_sub, map_sub, hP (A c)]
  abel

/-- **`(25)`, bounded part: the commutator with a contraction costs at most twice the norm.** -/
theorem norm_commutator_le {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A P : H →L[ℂ] H) (hP : ‖P‖ ≤ 1) :
    ‖A ∘L P - P ∘L A‖ ≤ 2 * ‖A‖ := by
  have h1 : ‖A ∘L P‖ ≤ ‖A‖ * ‖P‖ := ContinuousLinearMap.opNorm_comp_le A P
  have h2 : ‖P ∘L A‖ ≤ ‖P‖ * ‖A‖ := ContinuousLinearMap.opNorm_comp_le P A
  have hA : 0 ≤ ‖A‖ := norm_nonneg A
  have h3 : ‖A ∘L P - P ∘L A‖ ≤ ‖A ∘L P‖ + ‖P ∘L A‖ := norm_sub_le _ _
  nlinarith [h1, h2, h3, hA, norm_nonneg P]

/-- **`(26)`: the cross-boundary Carleman block is bounded on `L²` with norm at most `π`.**  This
is the analytic content of the cutoff defect's logarithmic part. -/
theorem lintegral_carlemanBlock_sq_le {F : ℝ → ENNReal} (hF : Measurable F) :
    (∫⁻ s in Set.Ioi (0:ℝ),
        (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (1 / (s + t)) * F t) ^ 2)
      ≤ ENNReal.ofReal (Real.pi ^ 2) * ∫⁻ t in Set.Ioi (0:ℝ), F t ^ 2 :=
  lintegral_carleman_sq_le hF

end

end RHTower
