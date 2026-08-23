import GaloisForLFunctions.HTGeometry.ConductorPlancherelPairing
import GaloisForLFunctions.HTGeometry.ConductorHankelForm

/-!
# The real-place conductor commutator is bounded

On a core of strictly anticausal sources and strictly causal readers the conductor symbol pairs
through its resolvent superposition.  The constant part of the superposition contributes nothing,
because a source supported on one half line is orthogonal to a reader supported on the other; and
each resolvent contributes a rank-one Hankel pairing whose rate integral is the conductor kernel.
That kernel sits under the Carleman kernel, so the whole pairing is bounded by `π` times the two
`L²` norms.

This replaces the Coifman--Rochberg--Weiss commutator theorem for this symbol: the physical-side
kernel `(b(x) - b(y))/(x - y)` has divergent row integrals, but the Fourier-side Hankel kernel
carries the factor `e^{-2πr}` and an elementary Schur test closes it.
-/

open Complex Real Set Filter Topology MeasureTheory FourierTransform ENNReal
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- **A half-line source is orthogonal to a half-line reader.**  Hence the constant part of the
resolvent superposition contributes nothing to the conductor pairing. -/
theorem fourier_pairing_eq_zero {φ ψ : ℝ → ℂ}
    (hφ : Integrable φ) (hψ : Integrable ψ) (hFψ : Integrable (𝓕 ψ)) (hψc : Continuous ψ)
    (hφ0 : ∀ s : ℝ, 0 ≤ s → φ s = 0) (hψ0 : ∀ t : ℝ, t ≤ 0 → ψ t = 0) :
    (∫ ξ : ℝ, 𝓕 φ ξ * (starRingEnd ℂ) (𝓕 ψ ξ)) = 0 := by
  rw [plancherel_pairing hφ hψ hFψ hψc]
  have hzero : ∀ x : ℝ, φ x * (starRingEnd ℂ) (ψ x) = 0 := by
    intro x
    rcases le_or_gt x 0 with h | h
    · simp [hψ0 x h]
    · simp [hφ0 x h.le]
  simp [hzero]

/-- **The bounded conductor commutator.**  The total rate variation of the resolvent pairings —
which is the conductor symbol pairing, the constant part contributing nothing — is bounded by `π`
times the two `L²` norms of the core functions. -/
theorem enorm_conductorPairing_le {φ ψ : ℝ → ℂ}
    (hφm : Measurable φ) (hψm : Measurable ψ)
    (hφ : Integrable φ) (hψ : Integrable ψ) (hFψ : Integrable (𝓕 ψ)) (hψc : Continuous ψ)
    (hφ0 : ∀ s : ℝ, 0 ≤ s → φ s = 0) (hψ0 : ∀ t : ℝ, t ≤ 0 → ψ t = 0) :
    (∫⁻ lam in Ioi (0:ℝ), ‖∫ ξ : ℝ,
        (((lam + 2 : ℝ) : ℂ) + 2 * Complex.I * ξ)⁻¹ * 𝓕 φ ξ * (starRingEnd ℂ) (𝓕 ψ ξ)‖ₑ)
      ≤ ENNReal.ofReal Real.pi
        * ((∫⁻ t in Ioi (0:ℝ), ‖ψ t‖ₑ ^ 2) ^ ((1 : ℝ) / 2)
          * (∫⁻ v in Ioi (0:ℝ), ‖φ (-v)‖ₑ ^ 2) ^ ((1 : ℝ) / 2)) := by
  refine le_trans (le_of_eq ?_) (enorm_lam_resolvent_pairing_le hφm hψm)
  refine setLIntegral_congr_fun measurableSet_Ioi (fun lam hlam => ?_)
  have hlam0 : (0 : ℝ) < lam := hlam
  have ha : (0 : ℝ) < lam + 2 := by linarith
  rw [resolvent_pairing_eq_hankelForm ha hφ hψ hFψ hψc hφ0 hψ0]

end RHTower
