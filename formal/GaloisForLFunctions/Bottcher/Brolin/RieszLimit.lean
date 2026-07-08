/-
# Böttcher tower — Brolin GAP-A: the limit Riesz identity `μ_c = (2π)⁻¹ ΔG_c`

This module discharges the **limit** step of GAP-A for the constructed Brolin
measure `gapAMu c`: it is the smooth-distributional Laplacian of the dynamical
Green function,

  `IsRieszMeasureOfSmooth (gapAMu c) (greenFunctionDyn c)`,   i.e.  `μ_c = (2π)⁻¹ ΔG_c`,

**conditional only on** `volume (filledJulia c) = 0` (the classical fact that the
disconnected/hyperbolic Julia set is Lebesgue-null).  No `L¹_loc` convergence is
used: the Fubini bridge `isRieszMeasureOfSmooth_of_potentialRep_ae_carrier`
(RieszPerLevel) turns the smooth Riesz identity into the a.e. logarithmic-potential
representation `G_c = −Uᵘ`, which holds on the basin unconditionally
(`green_eq_neg_logPotential_gapAMu_on_basin`) and hence a.e. once the Julia set is
null.  The remaining input `volume (filledJulia c) = 0` is the single named
analytic fact for this limb.
-/
import GaloisForLFunctions.Bottcher.Brolin.RieszPerLevel
import GaloisForLFunctions.Bottcher.Brolin.GapAMuCore
import GaloisForLFunctions.Bottcher.JuliaMeasureZero

open MeasureTheory Complex Filter Metric Set Laplacian InnerProductSpace
open scoped Laplacian Real Topology

namespace Bottcher

noncomputable section

/-- **GAP-A limit identity for the Brolin measure** (`μ_c = (2π)⁻¹ ΔG_c`), tested
against `C²` compactly supported functions, conditional on the Julia set being
Lebesgue-null.  Combines the basin potential representation
`green_eq_neg_logPotential_gapAMu_on_basin` (unconditional) with the Fubini bridge
`isRieszMeasureOfSmooth_of_potentialRep_ae_carrier`. -/
theorem isRieszMeasureOfSmooth_gapAMu_of_filledJulia_null (c : ℂ)
    (hnull : volume (filledJulia c) = 0) :
    IsRieszMeasureOfSmooth (gapAMu c) (greenFunctionDyn c) := by
  haveI : IsProbabilityMeasure (gapAMu c) := (gapAMu_isProbOn_filledJulia c).1
  have hcarrier : gapAMu c (Metric.closedBall 0 (max 2 ‖c‖))ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.mpr (filledJulia_subset_closedBall c))
      (gapAMu_isProbOn_filledJulia c).2
  have hae : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ filledJulia c := by
    rw [ae_iff]; simpa using hnull
  have hrep : (fun z => greenFunctionDyn c z)
      =ᵐ[volume] fun z => - logPotential (gapAMu c) z := by
    filter_upwards [hae] with z hz
    exact green_eq_neg_logPotential_gapAMu_on_basin hz
  exact isRieszMeasureOfSmooth_of_potentialRep_ae_carrier (gapAMu c) hcarrier _ hrep

end

/-- **`gapAMu c` is the Riesz measure of the dynamical Green function for `‖c‖ ≥ 4** (unconditional).
Large parameters make the filled Julia set Lebesgue-null (`volume_filledJulia_eq_zero_of_four_le_norm`),
which discharges the `hnull` hypothesis of `isRieszMeasureOfSmooth_gapAMu_of_filledJulia_null`.  So for
`‖c‖ ≥ 4`, `μ_c = (2π)⁻¹ ΔG_c` with no analytic side condition. -/
theorem isRieszMeasureOfSmooth_gapAMu_of_four_le_norm {c : ℂ} (hc : (4 : ℝ) ≤ ‖c‖) :
    IsRieszMeasureOfSmooth (gapAMu c) (greenFunctionDyn c) :=
  isRieszMeasureOfSmooth_gapAMu_of_filledJulia_null c
    (volume_filledJulia_eq_zero_of_four_le_norm hc)

/-- **`gapAMu c` is the Riesz measure of the dynamical Green function under the first-pullback radius
separation** (unconditional).  The explicit conditions `1/2 < r < ‖c‖`, `2 ≤ ‖c‖`,
`2‖c‖ < (‖c‖ − r)²` force the filled Julia set Lebesgue-null
(`volume_filledJulia_eq_zero_of_first_pullback_radius`), discharging `hnull`.  This extends the
Riesz representation `μ_c = (2π)⁻¹ ΔG_c` past `‖c‖ ≥ 4` to the whole first-pullback regime. -/
theorem isRieszMeasureOfSmooth_gapAMu_of_first_pullback_radius {c : ℂ} {r : ℝ}
    (hrhalf : ((1 : ℝ) / 2) < r) (h2c : (2 : ℝ) ≤ ‖c‖) (hrc : r < ‖c‖)
    (hbig : 2 * ‖c‖ < (‖c‖ - r) ^ 2) :
    IsRieszMeasureOfSmooth (gapAMu c) (greenFunctionDyn c) :=
  isRieszMeasureOfSmooth_gapAMu_of_filledJulia_null c
    (volume_filledJulia_eq_zero_of_first_pullback_radius hrhalf h2c hrc hbig)

end Bottcher
