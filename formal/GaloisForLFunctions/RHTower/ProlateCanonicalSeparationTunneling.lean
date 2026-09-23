import GaloisForLFunctions.RHTower.BandKaiserTrialSpace
import GaloisForLFunctions.RHTower.ProlateCanonicalRadialFamily
import GaloisForLFunctions.RHTower.ProlateSeparationTunneling

/-!
# Canonical signed prolate modes: reduction of separation convergence to WKB tunneling

The conditioned Kaiser packet spaces already give every fixed signed-greedy mode an upper leakage
clock arbitrarily close to the optimal `exp (-4πa²)` clock.  Consequently, to prove that the
canonical radial separation ratio tends to zero it is enough to show one concrete fact: whenever
that ratio stays above `ε > 0`, exterior tunneling has a strictly slower Gaussian clock.

This module makes that reduction for the actual selected mode family.  It removes all trial-space,
dimension, operator-spectrum, and Gaussian-domination work from the remaining WKB theorem.
-/

noncomputable section

open Filter

namespace RHTower

/-- Every fixed actual signed leakage has any Gaussian upper exponent strictly below `4π`. -/
theorem eventually_evenProlateSignedLeakage_le_exp_clock_loss
    (n : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ a : ℝ in atTop,
      evenProlateSignedLeakage a n ≤
        Real.exp (-((4 * Real.pi - η) * a ^ (2 : ℕ))) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hε : 0 < η / (2 * Real.pi) := by positivity
  have hkaiser := eventually_evenProlateSignedLeakage_le_kaiser
    (n := n) hε
  filter_upwards [hkaiser] with a ha
  convert ha using 1
  congr 2
  field_simp [Real.pi_ne_zero]
  ring

/-- **Concrete separation reduction for the canonical signed mode.**  A WKB lower bound with any
strict clock gain at each positive separation threshold forces the selected radial ratio to zero.
The upper estimate is discharged unconditionally by the actual Kaiser trial spaces. -/
theorem tendsto_signedModeRadialData_s_zero_of_tunneling_lower
    (n : ℕ)
    (htunnel : ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ a : ℝ in atTop,
        ε ≤ (signedModeRadialData a n).s →
          Real.exp (-((4 * Real.pi - δ) * a ^ (2 : ℕ))) ≤
            evenProlateSignedLeakage a n) :
    Tendsto (fun a : ℝ => (signedModeRadialData a n).s) atTop (nhds 0) := by
  apply tendsto_separation_zero_of_arbitrarily_sharp_gaussian_upper_of_tunneling_lower
    (β := 4 * Real.pi) (d := fun a => evenProlateSignedLeakage a n)
    (s := fun a => (signedModeRadialData a n).s) (by positivity)
    (eventually_signedModeRadialData_s_nonneg n)
  · intro η hη _hηβ
    exact eventually_evenProlateSignedLeakage_le_exp_clock_loss n hη
  · exact htunnel

end RHTower

end
