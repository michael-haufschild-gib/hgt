import GaloisForLFunctions.RHTower.EulerFisherColdEndDistance
import GaloisForLFunctions.RHTower.HeatEchoEulerMixedColdEndUniversalityLaw

/-!
# Heat-depth Euler cold-end density and distance

Integer heat depth translates the Euler inverse temperature.  The mixed heat/Euler law controls
the pointwise second Fisher moment on this discrete ray, while the cold-end distance law controls
the entire continuous tail beginning at the same translated temperature.  Their common parameter
therefore carries both a local density scale and a remaining-distance scale.
-/

namespace GaloisForLFunctions

open Filter Topology Set MeasureTheory

noncomputable section

/-- **Heat-depth Euler density-distance universality law.**  Along every integer heat-depth ray,
the dyadically normalized local conformal density tends `(log 2)^2`, while the square-root
normalized remaining radial distance from the same translated inverse temperature tends `2`. -/
theorem tendsto_heatApertureEulerColdEnd_density_and_remainingDistance
    (sigma : ℝ) (q : ℕ) :
    Tendsto (fun k : ℕ =>
      (2 : ℝ) ^ (1 - sigma + (q : ℝ) + (k : ℝ)) *
        heatApertureEulerMixedMoment sigma q k 2)
      atTop (𝓝 ((Real.log 2) ^ 2)) ∧
    Tendsto (fun k : ℕ =>
      (2 : ℝ) ^ ((1 - sigma + (q : ℝ) + (k : ℝ)) / 2) *
        ∫ u in Ioi (1 - sigma + (q : ℝ) + (k : ℝ)),
          Real.sqrt (RHTower.fisherWeightedTsumMoment
            (RHTower.eulerPrimePowerWeight u) RHTower.eulerPrimePowerEnergy 2))
      atTop (𝓝 2) := by
  have hshift : Tendsto
      (fun k : ℕ => 1 - sigma + (q : ℝ) + (k : ℝ)) atTop atTop := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds :
        Tendsto (fun k : ℕ => (k : ℝ) + (1 - sigma + (q : ℝ))) atTop atTop)
  exact ⟨tendsto_heatApertureEulerMixedMoment_dyadicScaled sigma q 2,
    RHTower.eulerColdEndRadialDistance_tendsto.comp hshift⟩

end

end GaloisForLFunctions
