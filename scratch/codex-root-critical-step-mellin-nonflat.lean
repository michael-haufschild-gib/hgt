import GaloisForLFunctions.RHTower.MobiusDivisorCriticalStepMellinWeld
import GaloisForLFunctions.RHTower.MobiusDivisorCriticalSourceFiniteJet

noncomputable section
open Filter Topology Complex
namespace RHTower

/-- The literal critical step-source Mellin integral has an isolated,
finite-order zero at the pole from the convergent side. -/
theorem criticalStepSourceMellin_eventually_ne_zero_right :
    ∀ᶠ s : ℂ in 𝓝 1, 1 < s.re → criticalStepSourceMellin s ≠ 0 := by
  obtain ⟨r, hr, g, hga, hg0, hfac⟩ := criticalSourceCurrentGap_finiteJet
  have hgne : ∀ᶠ s : ℂ in 𝓝 1, g s ≠ 0 :=
    hga.continuousAt.eventually_ne hg0
  filter_upwards [hfac, hgne] with s hs hgs hsr
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hsr
    norm_num at hsr
  have hs0 : s ≠ 0 := ne_zero_of_re_pos (by linarith)
  have hnum : centeredPrimeTailCurrentContinuation 1 -
      centeredPrimeTailCurrentContinuation s ≠ 0 := by
    rw [hs]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hs1)) hgs
  rw [criticalStepSourceMellin_eq_centeredCurrentGap hsr]
  exact div_ne_zero hnum hs0

end RHTower
