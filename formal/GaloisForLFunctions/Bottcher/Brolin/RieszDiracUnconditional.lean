import GaloisForLFunctions.Bottcher.Brolin.RieszFundamental
import GaloisForLFunctions.Bottcher.Brolin.RieszLogIBP

/-!
# The atomic Riesz identity, unconditionally

`isRieszMeasureOfSmooth_dirac` was stated under the fundamental-solution identity
`FundamentalSolutionProp` (`(2π)⁻¹ Δ log‖· − ρ‖ = δ_ρ` against `C²` compactly supported tests),
which `fundamentalSolutionProp_holds` proves by integration by parts on annuli.
-/

namespace Bottcher

noncomputable section

open MeasureTheory

/-- The Dirac mass at `ρ` is the Riesz measure of the logarithmic kernel `log‖· − ρ‖`. -/
theorem isRieszMeasureOfSmooth_dirac_unconditional (ρ : ℂ) :
    IsRieszMeasureOfSmooth (Measure.dirac ρ) (fun z => Real.log ‖z - ρ‖) :=
  isRieszMeasureOfSmooth_dirac fundamentalSolutionProp_holds ρ

end

end Bottcher
