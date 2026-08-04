import GaloisForLFunctions.HTGeometry.ClockTubeProbeTranslation
import GaloisForLFunctions.HTGeometry.ClockLocalTwoSpecies

/-!
# Determination and scale reconstruction for potentials coupling several transverse coordinates

A potential coupling several transverse coordinates has a clock probe at every event, so it has
probes on open regions in the sense the determination theorems use. Two consequences follow at once:
such a potential is determined by its probes, and the two-species scale law holds for it in every
dimension at least `k + 2`.

The scale law is stated with the effective potential of the massive species assumed to be of the
class — that is what makes its probes available. The massless species needs nothing, since its probe
is the explicit exponential.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

open scoped ContDiff

variable {k : ℕ}

namespace TubeDatum

variable {V Vs Vt : ℝ → ℝ → (Fin k → ℂ) → ℂ} {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ}
  (hD : TubeDatum V Vs Vt ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T)

include hD

/-- **A potential coupling several transverse coordinates has probes on open regions at every
event.** -/
theorem openProbes_nullMulti
    (hVreal : ∀ (s t : ℝ) (y : Fin k → ℝ), (V s t (realTube y)).im = 0)
    (hbound : ∀ s t : ℝ, ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv) (hT : 0 < T) (n : ℕ) :
    OpenProbes
      (SmoothPseudoMetric.ofSignature (slabEps (k + n))
        (slabEps_ne_zero (k + n))).chart.dalembert
      (nullMultiLift (fun s t y => (V s t (realTube y)).re) n) := by
  intro x
  obtain ⟨W, hWopen, hxW, U, hUon, hUne, _⟩ :=
    hD.exists_clockProbe_nullMulti_at hVreal hT n x
      (fun s t _ _ z hz => hbound (s + (x 0 + x 1)) (t + (x 0 - x 1)) z hz)
  exact ⟨W, hWopen, hxW, U, hUon, hUne⟩

/-- **A potential coupling several transverse coordinates is determined by its probes**, in every
dimension at least `k + 2`. -/
theorem nullMultiPotential_eq_of_openProbes
    (hVreal : ∀ (s t : ℝ) (y : Fin k → ℝ), (V s t (realTube y)).im = 0)
    (hbound : ∀ s t : ℝ, ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv) (hT : 0 < T) (n : ℕ)
    {other : (Fin (k + n + 2) → ℝ) → ℝ}
    (h : ∀ (u : (Fin (k + n + 2) → ℝ) → ℝ) (W : Set (Fin (k + n + 2) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps (k + n))
            (slabEps_ne_zero (k + n))).chart.dalembert
          (nullMultiLift (fun s t y => (V s t (realTube y)).re) n) u W →
        SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps (k + n))
            (slabEps_ne_zero (k + n))).chart.dalembert other u W) :
    other = nullMultiLift (fun s t y => (V s t (realTube y)).re) n :=
  potential_eq_of_openProbes (hD.openProbes_nullMulti hVreal hbound hT n) h

/-- **The two-species scale law in every dimension at least `k + 2`**, for an effective potential
coupling several transverse coordinates.

Two species of the same conjugation weight and different calibrated masses, probed on open regions,
return the conformal scale of the spacetime: the difference of the potentials the two species see,
divided by the mass gap, is `e^{2σ}`. -/
theorem twoSpecies_scale_reconstruction_nullMulti
    (hVreal : ∀ (s t : ℝ) (y : Fin k → ℝ), (V s t (realTube y)).im = 0)
    (hbound : ∀ s t : ℝ, ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv) (hT : 0 < T) (n : ℕ) (a : ℝ)
    {massSq : ℝ} (hmass : massSq ≠ 0)
    {σ : (Fin (k + n + 2) → ℝ) → ℝ} (hσ : ContDiff ℝ ∞ σ)
    (heff : (SmoothPseudoMetric.ofSignature (slabEps (k + n))
        (slabEps_ne_zero (k + n))).chart.conformalPotential a massSq σ
      = nullMultiLift (fun s t y => (V s t (realTube y)).re) n)
    {other₁ other₂ : (Fin (k + n + 2) → ℝ) → ℝ}
    (h₁ : ∀ (u : (Fin (k + n + 2) → ℝ) → ℝ) (W : Set (Fin (k + n + 2) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps (k + n))
            (slabEps_ne_zero (k + n))).chart.dalembert
          ((SmoothPseudoMetric.ofSignature (slabEps (k + n))
            (slabEps_ne_zero (k + n))).chart.conformalPotential a massSq σ) u W →
        SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps (k + n))
            (slabEps_ne_zero (k + n))).chart.dalembert other₁ u W)
    (h₂ : ∀ (u : (Fin (k + n + 2) → ℝ) → ℝ) (W : Set (Fin (k + n + 2) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps (k + n))
            (slabEps_ne_zero (k + n))).chart.dalembert
          ((SmoothPseudoMetric.ofSignature (slabEps (k + n))
            (slabEps_ne_zero (k + n))).chart.conformalPotential a 0 σ) u W →
        SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps (k + n))
            (slabEps_ne_zero (k + n))).chart.dalembert other₂ u W)
    (x : Fin (k + n + 2) → ℝ) :
    (other₁ x - other₂ x) / massSq = Real.exp (2 * σ x) := by
  have hop : OpenProbes
      (SmoothPseudoMetric.ofSignature (slabEps (k + n))
        (slabEps_ne_zero (k + n))).chart.dalembert
      ((SmoothPseudoMetric.ofSignature (slabEps (k + n))
        (slabEps_ne_zero (k + n))).chart.conformalPotential a massSq σ) := by
    rw [heff]
    exact hD.openProbes_nullMulti hVreal hbound hT n
  exact scale_reconstruction_of_openProbes _ a hσ hmass hop h₁ h₂ x

end TubeDatum

end GaloisForLFunctions.HTGeometry
