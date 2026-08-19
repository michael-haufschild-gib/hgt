import GaloisForLFunctions.HTGeometry.DeltaStructureLinearOde

/-!
# Compatibility identities for a rank-two shift recurrence with a compatible derivation

If a solution `y` of `τ² y = y + ρb · τ y` satisfies `δ y = ρP · y + ρQ · τ y` with coefficients
from a shift- and derivation-stable base, then applying `τ` twice expresses `δ (τ² y)` in two ways.
Linear independence of `y` and `τ y` over the base turns the comparison into two identities among
the coefficients — exactly the compatibility identities a parameterized classification refutes.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The compatibility identities of a compatible derivation.** -/
theorem deltaStructure_compatibility
    {F M : Type*} [Field F] [Field M] [Differential F] [Differential M]
    (ρ : F →+* M) (σ : F →+* F) (τ : M ≃+* M)
    (hτδ : ∀ x : M, τ (Differential.deriv x) = Differential.deriv (τ x))
    (hτρ : ∀ r : F, τ (ρ r) = ρ (σ r))
    (hρδ : ∀ r : F, Differential.deriv (ρ r) = ρ (Differential.deriv r))
    {b P Q : F} {y : M}
    (hrec : τ (τ y) = y + ρ b * τ y)
    (hindep : ∀ α β : F, ρ α * y + ρ β * τ y = 0 → α = 0 ∧ β = 0)
    (hδ : Differential.deriv y = ρ P * y + ρ Q * τ y) :
    (σ (σ P) + σ b * σ (σ Q) = P + b * σ Q) ∧
    (σ (σ Q) + b * σ (σ P) + b * σ b * σ (σ Q)
      = Q + Differential.deriv b + b * σ P + b * b * σ Q) := by
  have hδv : Differential.deriv (τ y) = ρ (σ Q) * y + (ρ (σ P) + ρ b * ρ (σ Q)) * τ y := by
    have h := congrArg (τ : M → M) hδ
    rw [hτδ] at h
    simp only [map_add, map_mul, hτρ] at h
    rw [hrec] at h
    linear_combination h
  have hwayA : Differential.deriv (τ (τ y))
      = ρ (σ (σ Q)) * τ y + (ρ (σ (σ P)) + ρ (σ b) * ρ (σ (σ Q))) * τ (τ y) := by
    have h := congrArg (τ : M → M) hδv
    rw [hτδ] at h
    simp only [map_add, map_mul, hτρ] at h
    linear_combination h
  have hwayB : Differential.deriv (τ (τ y))
      = ρ P * y + ρ Q * τ y + ρ (Differential.deriv b) * τ y
        + ρ b * (ρ (σ Q) * y + (ρ (σ P) + ρ b * ρ (σ Q)) * τ y) := by
    rw [hrec, deriv_add', deriv_mul', hδ, hδv, hρδ]
    ring
  have hzero : ρ (σ (σ P) + σ b * σ (σ Q) - (P + b * σ Q)) * y
      + ρ (σ (σ Q) + b * σ (σ P) + b * σ b * σ (σ Q)
        - (Q + Differential.deriv b + b * σ P + b * b * σ Q)) * τ y = 0 := by
    simp only [map_sub, map_add, map_mul]
    linear_combination hwayB - hwayA
      - (ρ (σ (σ P)) + ρ (σ b) * ρ (σ (σ Q))) * hrec
  obtain ⟨h1, h2⟩ := hindep _ _ hzero
  exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2⟩

end

end GaloisForLFunctions.HTGeometry
