import GaloisForLFunctions.RHTower.LegStripFarTail

/-!
# Infinite harmonic midpoint steepness universality law

The literal harmonic steepness theorem treats the balanced finite block of `2i+2` poles.  The
far-tail theorem independently proves that every remaining ahead pole contributes a negligible
amount after the same quadratic rescaling.  Adding them closes the infinite one-sided harmonic
carrier: its midpoint energy has exactly the balanced universal limit `π²/c²`.
-/

open Real Filter Topology

namespace RHTower

noncomputable section

/-- Midpoint energy of the balanced harmonic block completed by every farther ahead pole. -/
def harmonicInfiniteMidpointEnergy (c : ℝ) (i : ℕ) : ℝ :=
  spurLatticeEnergy (Finset.range (2 * i + 2)) (harmPole c) (harmMid c i) +
    (1 / 4) *
      ∑' m : ℕ,
        (rcsch ((harmPole c (2 * i + 2 + m) - harmMid c i) / 2)) ^ 2

/-- **Infinite harmonic midpoint steepness universality law.**  For every harmonic spacing
parameter `c > 1`, completing the balanced block by the entire infinite ahead tail leaves the
quadratically rescaled midpoint steepness unchanged. -/
theorem harmonicInfiniteMidpointEnergy_steepness
    {c : ℝ} (hc : 1 < c) :
    Tendsto (fun i : ℕ =>
      harmonicInfiniteMidpointEnergy c i / (((i + 1 : ℕ) : ℝ)) ^ 2)
      atTop (𝓝 (Real.pi ^ 2 / c ^ 2)) := by
  have hnear := harmonic_midpoint_energy_steepness (by linarith : 0 < c)
  have hfar := (farEnergyTail_div_tendsto hc).const_mul (1 / 4 : ℝ)
  have hsum := hnear.add hfar
  rw [show Real.pi ^ 2 / c ^ 2 = Real.pi ^ 2 / c ^ 2 + (1 / 4 : ℝ) * 0 by ring]
  convert hsum using 1
  funext i
  rw [harmonicInfiniteMidpointEnergy, add_div, mul_div_assoc]
  push_cast
  rfl

end

end RHTower
