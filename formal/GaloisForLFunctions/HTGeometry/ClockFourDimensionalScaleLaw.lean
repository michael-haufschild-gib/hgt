import GaloisForLFunctions.HTGeometry.ClockTubeCoupledScaleExample
import GaloisForLFunctions.HTGeometry.ClockTubeDatumExample

/-!
# The two-species scale law in four dimensions

The physical case of the construction is `k = 2` transverse coordinates and no spectator directions:
Minkowski space of dimension `2 + 0 + 2 = 4`, one timelike and three spacelike directions, with the
potential coupling the two null coordinates and *both* transverse ones.

This file states that case explicitly. Nothing is proved here that is not already proved in the
several-variable chapter; the point is that the physical dimension is an instance of it, and that
the instance is inhabited by an explicit scale.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

open scoped ContDiff

/-- The Minkowski signature of four-dimensional spacetime, as the construction uses it. -/
noncomputable abbrev fourEps : Fin 4 → ℝ := slabEps 2

/-- **Clock probes at every event of four-dimensional spacetime**, for a potential coupling the two
null coordinates and both transverse ones. -/
theorem TubeDatum.exists_clockProbe_fourDim {V Vs Vt : ℝ → ℝ → (Fin 2 → ℂ) → ℂ}
    {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ} (hD : TubeDatum V Vs Vt ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T)
    (hVreal : ∀ (s t : ℝ) (y : Fin 2 → ℝ), (V s t (realTube y)).im = 0) (hT : 0 < T)
    (x : Fin 4 → ℝ)
    (hmass : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube 2 ρ₀,
      ‖V (s + (x 0 + x 1)) (t + (x 0 - x 1)) z‖ ≤ Mv) :
    ∃ W : Set (Fin 4 → ℝ), IsOpen W ∧ x ∈ W ∧ ∃ U : (Fin 4 → ℝ) → ℝ,
      SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature fourEps (slabEps_ne_zero 2)).chart.dalembert
          (nullMultiLift (fun s t y => (V s t (realTube y)).re) 0) U W ∧
        (∀ y ∈ W, U y ≠ 0) ∧ U x = 1 :=
  hD.exists_clockProbe_nullMulti_at hVreal hT 0 x hmass

/-- **The two-species scale law in four dimensions.** Two species of the same conjugation weight and
different calibrated masses, probed on open regions, return the conformal scale of spacetime. -/
theorem TubeDatum.twoSpecies_scale_reconstruction_fourDim {V Vs Vt : ℝ → ℝ → (Fin 2 → ℂ) → ℂ}
    {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ} (hD : TubeDatum V Vs Vt ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T)
    (hVreal : ∀ (s t : ℝ) (y : Fin 2 → ℝ), (V s t (realTube y)).im = 0)
    (hbound : ∀ s t : ℝ, ∀ z ∈ tube 2 ρ₀, ‖V s t z‖ ≤ Mv) (hT : 0 < T) (a : ℝ)
    {massSq : ℝ} (hmass : massSq ≠ 0)
    {σ : (Fin 4 → ℝ) → ℝ} (hσ : ContDiff ℝ ∞ σ)
    (heff : (SmoothPseudoMetric.ofSignature fourEps (slabEps_ne_zero 2)).chart.conformalPotential
        a massSq σ
      = nullMultiLift (fun s t y => (V s t (realTube y)).re) 0)
    {other₁ other₂ : (Fin 4 → ℝ) → ℝ}
    (h₁ : ∀ (u : (Fin 4 → ℝ) → ℝ) (W : Set (Fin 4 → ℝ)), IsOpen W →
      SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature fourEps (slabEps_ne_zero 2)).chart.dalembert
          ((SmoothPseudoMetric.ofSignature fourEps
            (slabEps_ne_zero 2)).chart.conformalPotential a massSq σ) u W →
        SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature fourEps (slabEps_ne_zero 2)).chart.dalembert
          other₁ u W)
    (h₂ : ∀ (u : (Fin 4 → ℝ) → ℝ) (W : Set (Fin 4 → ℝ)), IsOpen W →
      SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature fourEps (slabEps_ne_zero 2)).chart.dalembert
          ((SmoothPseudoMetric.ofSignature fourEps
            (slabEps_ne_zero 2)).chart.conformalPotential a 0 σ) u W →
        SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature fourEps (slabEps_ne_zero 2)).chart.dalembert
          other₂ u W)
    (x : Fin 4 → ℝ) :
    (other₁ x - other₂ x) / massSq = Real.exp (2 * σ x) :=
  hD.twoSpecies_scale_reconstruction_nullMulti hVreal hbound hT 0 a hmass hσ heff h₁ h₂ x

/-- **The two-species scale law in four dimensions for an explicit coupled scale.**

For `σ(ξ,η,y) = ε sin(ξ + η + y¹ + y²)` on four-dimensional Minkowski space — a scale coupling both
null coordinates and both transverse ones — two species of the same conjugation weight and different
calibrated masses return the conformal scale. No hypothesis is left on the potential: its
admissibility, and the existence of the probes, are proved. -/
theorem twoSpecies_scale_reconstruction_coupledScale_fourDim (a ε : ℝ) {massSq : ℝ}
    (hmassSq : massSq ≠ 0) {other₁ other₂ : (Fin 4 → ℝ) → ℝ}
    (h₁ : ∀ (u : (Fin 4 → ℝ) → ℝ) (W : Set (Fin 4 → ℝ)), IsOpen W →
      SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature fourEps (slabEps_ne_zero 2)).chart.dalembert
          ((SmoothPseudoMetric.ofSignature fourEps
            (slabEps_ne_zero 2)).chart.conformalPotential a massSq
              (nullMultiLift (coupledScaleMulti (k := 2) ε) 0)) u W →
        SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature fourEps (slabEps_ne_zero 2)).chart.dalembert
          other₁ u W)
    (h₂ : ∀ (u : (Fin 4 → ℝ) → ℝ) (W : Set (Fin 4 → ℝ)), IsOpen W →
      SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature fourEps (slabEps_ne_zero 2)).chart.dalembert
          ((SmoothPseudoMetric.ofSignature fourEps
            (slabEps_ne_zero 2)).chart.conformalPotential a 0
              (nullMultiLift (coupledScaleMulti (k := 2) ε) 0)) u W →
        SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature fourEps (slabEps_ne_zero 2)).chart.dalembert
          other₂ u W)
    (x : Fin 4 → ℝ) :
    (other₁ x - other₂ x) / massSq
      = Real.exp (2 * nullMultiLift (coupledScaleMulti (k := 2) ε) 0 x) :=
  twoSpecies_scale_reconstruction_coupledScaleMulti 2 0 a ε hmassSq h₁ h₂ x

/-- **The four-dimensional class is inhabited.** -/
theorem exists_tubeDatum_coupled_fourDim :
    ∃ (V Vs Vt : ℝ → ℝ → (Fin 2 → ℂ) → ℂ) (ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ),
      TubeDatum V Vs Vt ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T ∧ 0 < T ∧
        (∀ s t : ℝ, ∀ z ∈ tube 2 ρ₀, ‖V s t z‖ ≤ Mv) ∧
        (∀ (s t : ℝ) (y : Fin 2 → ℝ), (V s t (realTube y)).im = 0) ∧
        (∀ i : Fin 2, ∃ (s t : ℝ) (z : Fin 2 → ℂ) (ζ : ℂ),
          V s t (Function.update z i ζ) ≠ V s t z) ∧
        (∃ (s s' t : ℝ) (z : Fin 2 → ℂ), V s t z ≠ V s' t z) :=
  exists_tubeDatum_coupled 2

end GaloisForLFunctions.HTGeometry
