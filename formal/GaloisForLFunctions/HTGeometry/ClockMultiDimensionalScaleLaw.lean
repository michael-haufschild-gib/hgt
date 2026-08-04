import GaloisForLFunctions.HTGeometry.ClockMultiDimensionalDetermination
import GaloisForLFunctions.HTGeometry.ClockNullMultiConformal

/-!
# The two-species scale law for a scale function coupling several transverse coordinates

The scale law of the previous file assumes the effective potential of the massive species to be of
the coupled class. This file states the same law with that assumption moved to the scale function,
where it is an explicit identity: the effective potential built from the scale's derivatives — by the
formula of the previous chapter — is the real part of a potential carrying a clock datum on a tube.

Nothing is added to the mathematics; the point is that the hypothesis becomes checkable in terms of
the scale itself, now for a scale depending on arbitrarily many transverse coordinates at once.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

open scoped ContDiff

variable {k : ℕ}

namespace TubeDatum

variable {V Vs Vt : ℝ → ℝ → (Fin k → ℂ) → ℂ} {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ}
  (hD : TubeDatum V Vs Vt ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T)

include hD

/-- **The two-species scale law in every dimension at least `k + 2`, stated on the scale
function.**

The scale depends on the two null coordinates and on `k` transverse coordinates, and is twice
continuously differentiable in all of them. Its effective potential — the mass term less the
geometric defect, both computed from its derivatives — is assumed to be the real part of a potential
carrying a clock datum on a tube. Then two species of the same weight and different calibrated masses
return the conformal scale. -/
theorem twoSpecies_scale_reconstruction_of_scale_multi
    (hVreal : ∀ (s t : ℝ) (y : Fin k → ℝ), (V s t (realTube y)).im = 0)
    (hbound : ∀ s t : ℝ, ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv) (hT : 0 < T) (n : ℕ) (a : ℝ)
    {massSq : ℝ} (hmassSq : massSq ≠ 0)
    {σ₀ A B Aa Ab Ba Bb : ℝ → ℝ → (Fin k → ℝ) → ℝ}
    {C Ac Bc Ca Cb : Fin k → ℝ → ℝ → (Fin k → ℝ) → ℝ}
    {Cc : Fin k → Fin k → ℝ → ℝ → (Fin k → ℝ) → ℝ}
    (h : IsC1OnMulti σ₀ A B C univ) (hA : IsC1OnMulti A Aa Ab Ac univ)
    (hB : IsC1OnMulti B Ba Bb Bc univ)
    (hC : ∀ i : Fin k, IsC1OnMulti (C i) (Ca i) (Cb i) (Cc i) univ)
    (hσ : ContDiff ℝ ∞ (nullMultiLift σ₀ n))
    (heff : conformalPotentialMulti a massSq σ₀ A B C Ab Ba Cc
      = fun s t y => (V s t (realTube y)).re)
    {other₁ other₂ : (Fin (k + n + 2) → ℝ) → ℝ}
    (h₁ : ∀ (u : (Fin (k + n + 2) → ℝ) → ℝ) (W : Set (Fin (k + n + 2) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps (k + n))
            (slabEps_ne_zero (k + n))).chart.dalembert
          ((SmoothPseudoMetric.ofSignature (slabEps (k + n))
            (slabEps_ne_zero (k + n))).chart.conformalPotential a massSq
              (nullMultiLift σ₀ n)) u W →
        SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps (k + n))
            (slabEps_ne_zero (k + n))).chart.dalembert other₁ u W)
    (h₂ : ∀ (u : (Fin (k + n + 2) → ℝ) → ℝ) (W : Set (Fin (k + n + 2) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps (k + n))
            (slabEps_ne_zero (k + n))).chart.dalembert
          ((SmoothPseudoMetric.ofSignature (slabEps (k + n))
            (slabEps_ne_zero (k + n))).chart.conformalPotential a 0 (nullMultiLift σ₀ n)) u W →
        SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps (k + n))
            (slabEps_ne_zero (k + n))).chart.dalembert other₂ u W)
    (x : Fin (k + n + 2) → ℝ) :
    (other₁ x - other₂ x) / massSq = Real.exp (2 * nullMultiLift σ₀ n x) := by
  have hlift : (SmoothPseudoMetric.ofSignature (slabEps (k + n))
        (slabEps_ne_zero (k + n))).chart.conformalPotential a massSq (nullMultiLift σ₀ n)
      = nullMultiLift (fun s t y => (V s t (realTube y)).re) n := by
    funext y
    rw [conformalPotential_nullMultiLift h hA hB hC a massSq (mem_univ _), heff]
  exact hD.twoSpecies_scale_reconstruction_nullMulti hVreal hbound hT n a hmassSq hσ
    hlift h₁ h₂ x

end TubeDatum

end GaloisForLFunctions.HTGeometry
