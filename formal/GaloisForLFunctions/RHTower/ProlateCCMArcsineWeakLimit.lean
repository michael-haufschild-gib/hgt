import GaloisForLFunctions.RHTower.ProlateDunsterWeakLimit

/-!
# Exact prolate weak limit is the CCM arcsine leakage law

The Dunster analysis constructs the weak limit from endpoint-normalized exact radial prolate
solutions.  The CCM leakage analysis independently constructs the same positive density.  This
module closes the cross-route identification: every exact high-bandwidth, low-separation prolate
family converges tailwise to the CCM radial leakage measure divided by `pi`.
-/

noncomputable section

open Filter MeasureTheory Set

namespace GaloisForLFunctions.RHTower

/-- **Prolate--CCM leakage identification in the exact weak limit.** -/
theorem tendsto_integral_Ioi_radialProlateDensity_to_ccmLeakage
    {ι : Type*} {l : Filter ι} {c s : ι → ℝ}
    {R DR DDR : ι → ℝ → ℝ}
    (hc : Tendsto c l atTop) (hs : Tendsto s l (nhds 0))
    (hs0 : ∀ᶠ i in l, 0 ≤ s i)
    (hR1 : ∀ᶠ i in l, R i 1 = 1)
    (hR : ∀ᶠ i in l, ∀ t, HasDerivAt (R i) (DR i t) t)
    (hDR : ∀ᶠ i in l, ∀ t, HasDerivAt (DR i) (DDR i t) t)
    (hode : ∀ᶠ i in l, ∀ t, (t ^ 2 - 1) * DDR i t + 2 * t * DR i t
      - (s i * c i ^ 2 - c i ^ 2 * t ^ 2) * R i t = 0)
    {a : ℝ} (ha : 1 < a) :
    Tendsto (fun i => ∫ x in Ioi a, radialProlateDensity (c i) (R i) x) l
      (nhds ((∫ x in Ioi a, _root_.RHTower.radialLeakageDensity x) / Real.pi)) := by
  have h := tendsto_integral_Ioi_radialProlateDensity hc hs hs0 hR1 hR hDR hode ha
  have hlimit : (∫ x in Ioi a, profileDensity x) =
      (∫ x in Ioi a, _root_.RHTower.radialLeakageDensity x) / Real.pi := by
    rw [← MeasureTheory.integral_div]
    exact setIntegral_congr_fun measurableSet_Ioi fun x _ =>
      profileDensity_eq_radialLeakageDensity_div_pi x
  rw [hlimit] at h
  exact h

end GaloisForLFunctions.RHTower

end
