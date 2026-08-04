import GaloisForLFunctions.HTGeometry.ClockProbeTranslation
import GaloisForLFunctions.HTGeometry.ClockLocalTwoSpecies

/-!
# Determination and scale reconstruction for coupled transverse potentials

A potential with coupled transverse dependence has a clock probe at every event, so it has probes on
open regions in the sense the determination theorems use. Two consequences follow at once: such a
potential is determined by its probes, and the two-species scale law holds for it in every dimension
at least three.

The scale law is stated with the effective potential of the massive species assumed to be of the
class — that is what makes its probes available. The massless species needs nothing, since its
probe is the explicit exponential.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

open scoped ContDiff

namespace ClockDatum

variable {V Vs Vt : ℝ → ℝ → ℂ → ℂ} {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ}
  (hD : ClockDatum V Vs Vt ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T)

include hD

/-- **A potential with coupled transverse dependence has probes on open regions at every event.** -/
theorem openProbes_nullTransverse (hVreal : ∀ s t w : ℝ, (V s t ((w : ℝ) : ℂ)).im = 0)
    (hbound : ∀ s t : ℝ, ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv) (hT : 0 < T) (n : ℕ) :
    OpenProbes
      (SmoothPseudoMetric.ofSignature (slabEps (n + 1))
        (slabEps_ne_zero (n + 1))).chart.dalembert
      (nullTransLift (fun s t w => (V s t ((w : ℝ) : ℂ)).re) n) := by
  intro x
  obtain ⟨W, hWopen, hxW, U, hUon, hUne, _⟩ :=
    hD.exists_clockProbe_nullTransverse_at hVreal hT n x
      (fun s t _ _ z hz => hbound (s + (x 0 + x 1)) (t + (x 0 - x 1)) z hz)
  exact ⟨W, hWopen, hxW, U, hUon, hUne⟩

/-- **A potential with coupled transverse dependence is determined by its probes**, in every
dimension at least three. -/
theorem nullTransversePotential_eq_of_openProbes
    (hVreal : ∀ s t w : ℝ, (V s t ((w : ℝ) : ℂ)).im = 0)
    (hbound : ∀ s t : ℝ, ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv) (hT : 0 < T) (n : ℕ)
    {other : (Fin (n + 3) → ℝ) → ℝ}
    (h : ∀ (u : (Fin (n + 3) → ℝ) → ℝ) (W : Set (Fin (n + 3) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps (n + 1))
            (slabEps_ne_zero (n + 1))).chart.dalembert
          (nullTransLift (fun s t w => (V s t ((w : ℝ) : ℂ)).re) n) u W →
        SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps (n + 1))
            (slabEps_ne_zero (n + 1))).chart.dalembert other u W) :
    other = nullTransLift (fun s t w => (V s t ((w : ℝ) : ℂ)).re) n :=
  potential_eq_of_openProbes (hD.openProbes_nullTransverse hVreal hbound hT n) h

/-- **The two-species scale law in every dimension at least three**, for an effective potential with
coupled transverse dependence.

Two species of the same conjugation weight and different calibrated masses, probed on open regions,
return the conformal scale of the spacetime: the difference of the potentials the two species see,
divided by the mass gap, is `e^{2σ}`. -/
theorem twoSpecies_scale_reconstruction_nullTransverse
    (hVreal : ∀ s t w : ℝ, (V s t ((w : ℝ) : ℂ)).im = 0)
    (hbound : ∀ s t : ℝ, ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv) (hT : 0 < T) (n : ℕ) (a : ℝ)
    {massSq : ℝ} (hmass : massSq ≠ 0)
    {σ : (Fin (n + 3) → ℝ) → ℝ} (hσ : ContDiff ℝ ∞ σ)
    (heff : (SmoothPseudoMetric.ofSignature (slabEps (n + 1))
        (slabEps_ne_zero (n + 1))).chart.conformalPotential a massSq σ
      = nullTransLift (fun s t w => (V s t ((w : ℝ) : ℂ)).re) n)
    {other₁ other₂ : (Fin (n + 3) → ℝ) → ℝ}
    (h₁ : ∀ (u : (Fin (n + 3) → ℝ) → ℝ) (W : Set (Fin (n + 3) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps (n + 1))
            (slabEps_ne_zero (n + 1))).chart.dalembert
          ((SmoothPseudoMetric.ofSignature (slabEps (n + 1))
            (slabEps_ne_zero (n + 1))).chart.conformalPotential a massSq σ) u W →
        SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps (n + 1))
            (slabEps_ne_zero (n + 1))).chart.dalembert other₁ u W)
    (h₂ : ∀ (u : (Fin (n + 3) → ℝ) → ℝ) (W : Set (Fin (n + 3) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps (n + 1))
            (slabEps_ne_zero (n + 1))).chart.dalembert
          ((SmoothPseudoMetric.ofSignature (slabEps (n + 1))
            (slabEps_ne_zero (n + 1))).chart.conformalPotential a 0 σ) u W →
        SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps (n + 1))
            (slabEps_ne_zero (n + 1))).chart.dalembert other₂ u W)
    (x : Fin (n + 3) → ℝ) :
    (other₁ x - other₂ x) / massSq = Real.exp (2 * σ x) := by
  have hop : OpenProbes
      (SmoothPseudoMetric.ofSignature (slabEps (n + 1))
        (slabEps_ne_zero (n + 1))).chart.dalembert
      ((SmoothPseudoMetric.ofSignature (slabEps (n + 1))
        (slabEps_ne_zero (n + 1))).chart.conformalPotential a massSq σ) := by
    rw [heff]
    exact hD.openProbes_nullTransverse hVreal hbound hT n
  exact scale_reconstruction_of_openProbes _ a hσ hmass hop h₁ h₂ x

end ClockDatum

end GaloisForLFunctions.HTGeometry
