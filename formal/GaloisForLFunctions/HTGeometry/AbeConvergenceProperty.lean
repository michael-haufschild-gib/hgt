import GaloisForLFunctions.HTGeometry.AbePoincareJetCoefficientSummability
import GaloisForLFunctions.HTGeometry.AbeRealCoordinatePhi2

/-!
# Abe's Section-7 convergence property

This is the exact source-side condition used in Abe's Section 7: a fixed entire seed has locally
normally summable Poincaré series after multiplication by every `Φ₂` source. The concrete
real-coordinate `Φ₂` closure then gives local normal convergence, and hence scalar ℓ¹ mixed-jet
coefficients, for every fixed literal damping time.

The construction of a seed with this property and its preservation through the all-order
subgroup-rank induction remain the card's open geometric core.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Abe's convergence property for an entire seed and a fixed automorphic factor. -/
def HasAbeConvergenceProperty {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ) (f : MultivariateEntire d) : Prop :=
  ∀ φ : MultivariateEntire d, IsAbePhi2 Γ φ →
    SummableLocallyUniformlyOn (fun γ => poincareTerm ψ (f * φ) γ) Set.univ

/-- The Section-7 convergence property proves local normal convergence for every fixed literal
real-coordinate damping time. -/
theorem HasAbeConvergenceProperty.normal_abeRealCoordinateDampedSource
    {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)} (ψ : AutomorphicFactor d Γ)
    (f φ : MultivariateEntire d) (hf : HasAbeConvergenceProperty ψ f)
    (hφ : IsAbePhi2 Γ φ) (k : Fin d) (t : ℂ)
    (hreal : ∀ γ : Γ, ∃ r : ℝ, γ.1 k = (r : ℂ)) :
    SummableLocallyUniformlyOn (fun γ =>
      poincareTerm ψ (f * (φ * abeExponentialDampingMultiplier t
        (abeRealCoordinateProfile d k))) γ) Set.univ :=
  hf _ (hφ.mul_abeExponentialDampingMultiplier_abeRealCoordinateProfile φ k t hreal)

/-- Consequently every fixed mixed jet of the literal damped coefficient source has a scalar
ℓ¹ Poincaré majorant. -/
theorem HasAbeConvergenceProperty.summable_norm_abeRealCoordinateDampedSource_jet
    {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)} (ψ : AutomorphicFactor d Γ)
    (f φ : MultivariateEntire d) (hf : HasAbeConvergenceProperty ψ f)
    (hφ : IsAbePhi2 Γ φ) (k : Fin d) (t : ℂ)
    (hreal : ∀ γ : Γ, ∃ r : ℝ, γ.1 k = (r : ℂ))
    (x : Fin d → ℂ) (a : Fin d →₀ ℕ) :
    Summable (fun γ => ‖multiIndexJetEvalCLM x a
      (poincareTermEntire ψ (f * (φ * abeExponentialDampingMultiplier t
        (abeRealCoordinateProfile d k))) γ)‖) := by
  apply summable_norm_multiIndexJetEvalCLM_poincareTermEntire
  exact HasAbeConvergenceProperty.normal_abeRealCoordinateDampedSource
    ψ f φ hf hφ k t hreal

end

end GaloisForLFunctions.HTGeometry
