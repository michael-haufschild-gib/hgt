import GaloisForLFunctions.BlackHoleRingdown.TheRingdownRateIsTheZeroFreeStrip
import GaloisForLFunctions.CountingHolography.ThermalizationFasterThanTheSquareRootIsAZeroFreeStrip

/-!
# The two rates of the modular horizon are one exponent

The horizon has two late-time laws. In time, the field of a compact pulse rings down after its mean
growth is removed. In space, a long closed horocycle at height `y` thermalizes: the horocycle mean of a
pseudo-Eisenstein series tends to its limit. Under RH the rates are `e^{-τ/4}` and `y^{3/4}`.

They are one exponent at every strength (`pulse_ringdown_iff_horocycle_rate`): for `0 < δ ≤ 1/4`,

  every pulse rings down at `e^{-(δ-ε)τ}` for every `ε > 0`
  ⟺ every horocycle mean converges at `y^{1/2+δ-ε}` for every `ε > 0`,

and both say that every zero with `Re ρ > 0` has `Re ρ ≤ 1 - 2δ`. The poles `ρ/2` of the Eisenstein
series give the time mode `e^{(ρ-1)τ/2}` and the space mode `y^{1-ρ/2}`. A horocycle at height `y` is the
unit horocycle pushed by the geodesic flow for time `log(1/y)`, and its length `1/y` contributes the
volume factor `y^{1/2}`: `y^{1-ρ/2} = y^{1/2} · e^{-(1-ρ)/2 · log(1/y)}`. So the thermalization exponent
is `½` plus the ringdown exponent, exactly.
-/

open Complex Set
open scoped ContDiff

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open CountingHolography RingdownRate

/-- **One exponent.** For `0 < δ ≤ 1/4`, every compact pulse rings down at rate `e^{-(δ-ε)τ}` for every
`ε > 0` iff every closed horocycle thermalizes at rate `y^{1/2+δ-ε}` for every `ε > 0`. -/
theorem pulse_ringdown_iff_horocycle_rate {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4) :
    (∀ ε : ℝ, 0 < ε → ∀ (h : CompactPulse) (x Y : ℝ), 0 < Y → ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ →
        ‖pulseField h τ x Y‖ ≤ C * Real.exp (-(δ - ε) * τ)) ↔
      ∀ ε : ℝ, 0 < ε → ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioi 1 →
        ∃ c : ℂ, ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
          ‖horocycleMean (pseudoEisenstein fun t => (φ t : ℂ)) y - c‖ ≤ C * y ^ (1 / 2 + δ - ε) := by
  rw [← zeroFreeStrip_iff_pulse_ringdown hδ0 hδ, zeroFreeStrip_iff_fareyCount_rate hδ0 hδ]
  exact forall_congr' fun ε => imp_congr_right fun _ =>
    (horocycle_rate_iff_fareyCount_rate (1 / 2 + δ - ε)).symm

end GaloisForLFunctions.BlackHoleRingdown
