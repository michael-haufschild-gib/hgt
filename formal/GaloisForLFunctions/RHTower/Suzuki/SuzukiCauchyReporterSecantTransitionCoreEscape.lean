import GaloisForLFunctions.RHTower.Suzuki.SuzukiCauchyReporterSecantSharpArithmeticLocalization
import GaloisForLFunctions.RHTower.Suzuki.SuzukiNaturalApertureCauchyEnergyEscape

/-!
# Escape of the exact positive Suzuki transition core

The exact reporter-secant transition does not produce a bounded arithmetic remainder.  The raw
natural Suzuki Cauchy energy already has a linear lower bound along apertures `8n`, while sharp
arithmetic localization bounds that energy above by its positive transition core.  Consequently
the transition core itself grows at least linearly and tends to positive infinity.

This localizes the earlier raw-wall scaling obstruction: anchor-visible prime mass survives inside
the exact positive Gram sector, not in the favorable transition-separated tail.  Hence deleting
all nonpositive cross-scale interactions can never supply the missing cofinal Ward bound.  A viable
assembly must compensate or renormalize the positive transition core before passage to the limit.
-/

open Filter

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The exact positive transition core inherits the linear PNT-sized lower bound of the full raw
natural Suzuki Cauchy energy. -/
theorem eventually_suzukiNaturalApertureTransitionCoreCauchyEnergy_ge_linear :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) / 288 ≤
        suzukiNaturalApertureTransitionCoreCauchyEnergy (8 * n) := by
  filter_upwards [eventually_suzukiNaturalApertureCauchyEnergy_ge_linear] with n hn
  exact hn.trans (suzukiNaturalApertureCauchyEnergy_le_transitionCore (8 * n))

/-- **Exact-core escape.**  Even after every favorable transition-separated pair is removed, the
remaining positive arithmetic sector diverges along the cofinal aperture subsequence `8n`. -/
theorem tendsto_suzukiNaturalApertureTransitionCoreCauchyEnergy_eight_mul_atTop :
    Tendsto (fun n : ℕ =>
      suzukiNaturalApertureTransitionCoreCauchyEnergy (8 * n)) atTop atTop := by
  rw [tendsto_atTop]
  intro B
  filter_upwards [eventually_suzukiNaturalApertureTransitionCoreCauchyEnergy_ge_linear,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (288 * B)] with n hcore hn
  calc
    B ≤ (n : ℝ) / 288 := by linarith
    _ ≤ suzukiNaturalApertureTransitionCoreCauchyEnergy (8 * n) := hcore

end

end GaloisForLFunctions.RHTower
