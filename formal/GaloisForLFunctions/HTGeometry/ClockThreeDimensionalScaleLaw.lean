import GaloisForLFunctions.HTGeometry.ClockThreeDimensionalDetermination
import GaloisForLFunctions.HTGeometry.ClockNullTransverseConformal

/-!
# The two-species scale law for a scale function with coupled transverse dependence

The scale law of the previous file assumes the effective potential of the massive species to be of
the coupled class. This file states the same law with that assumption moved to the scale function,
where it is an explicit identity: the effective potential built from the scale's derivatives — by the
formula of the previous chapter — is the real part of a potential carrying a clock datum.

Nothing is added to the mathematics; the point is that the hypothesis becomes checkable in terms of
the scale itself.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

open scoped ContDiff

namespace ClockDatum

variable {V Vs Vt : ℝ → ℝ → ℂ → ℂ} {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ}
  (hD : ClockDatum V Vs Vt ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T)

include hD

/-- **The two-species scale law in every dimension at least three, stated on the scale function.**

The scale depends on the two null coordinates and one transverse coordinate, and is twice
continuously differentiable in all three. Its effective potential — the mass term less the geometric
defect, both computed from its derivatives — is assumed to be the real part of a potential carrying a
clock datum. Then two species of the same weight and different calibrated masses return the conformal
scale. -/
theorem twoSpecies_scale_reconstruction_of_scale
    (hVreal : ∀ s t w : ℝ, (V s t ((w : ℝ) : ℂ)).im = 0)
    (hbound : ∀ s t : ℝ, ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv) (hT : 0 < T) (n : ℕ) (a : ℝ)
    {massSq : ℝ} (hmassSq : massSq ≠ 0)
    {σ₀ A B C Aa Ab Ac Ba Bb Bc Ca Cb Cc : ℝ → ℝ → ℝ → ℝ}
    (h : IsC1On3 σ₀ A B C univ) (hA : IsC1On3 A Aa Ab Ac univ) (hB : IsC1On3 B Ba Bb Bc univ)
    (hC : IsC1On3 C Ca Cb Cc univ) (hσ : ContDiff ℝ ∞ (nullTransLift σ₀ n))
    (heff : conformalPotentialTri a massSq σ₀ A B C Ab Ba Cc
      = fun s t w => (V s t ((w : ℝ) : ℂ)).re)
    {other₁ other₂ : (Fin (n + 3) → ℝ) → ℝ}
    (h₁ : ∀ (u : (Fin (n + 3) → ℝ) → ℝ) (W : Set (Fin (n + 3) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps (n + 1))
            (slabEps_ne_zero (n + 1))).chart.dalembert
          ((SmoothPseudoMetric.ofSignature (slabEps (n + 1))
            (slabEps_ne_zero (n + 1))).chart.conformalPotential a massSq
              (nullTransLift σ₀ n)) u W →
        SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps (n + 1))
            (slabEps_ne_zero (n + 1))).chart.dalembert other₁ u W)
    (h₂ : ∀ (u : (Fin (n + 3) → ℝ) → ℝ) (W : Set (Fin (n + 3) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps (n + 1))
            (slabEps_ne_zero (n + 1))).chart.dalembert
          ((SmoothPseudoMetric.ofSignature (slabEps (n + 1))
            (slabEps_ne_zero (n + 1))).chart.conformalPotential a 0 (nullTransLift σ₀ n)) u W →
        SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps (n + 1))
            (slabEps_ne_zero (n + 1))).chart.dalembert other₂ u W)
    (x : Fin (n + 3) → ℝ) :
    (other₁ x - other₂ x) / massSq = Real.exp (2 * nullTransLift σ₀ n x) := by
  have hlift : (SmoothPseudoMetric.ofSignature (slabEps (n + 1))
        (slabEps_ne_zero (n + 1))).chart.conformalPotential a massSq (nullTransLift σ₀ n)
      = nullTransLift (fun s t w => (V s t ((w : ℝ) : ℂ)).re) n := by
    funext y
    rw [conformalPotential_nullTransLift h hA hB hC a massSq (mem_univ _), heff]
  exact hD.twoSpecies_scale_reconstruction_nullTransverse hVreal hbound hT n a hmassSq hσ
    hlift h₁ h₂ x

end ClockDatum

end GaloisForLFunctions.HTGeometry
