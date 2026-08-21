import GaloisForLFunctions.HTGeometry.MultivariateEntireJetVanishingProduct

/-!
# The growth of a Poincaré term's packet jets

The damping datum of the quasi-abelian jet-ampleness induction needs a bound
`C₀·B^r·exp(−σ₀·∑ z_k²)` on the packet jets of the complement Poincaré terms.  A Poincaré term is a
product of the inverse automorphy factor and a translate of the seed, so Cauchy's estimate turns
that bound into two sup bounds on a fixed polydisc: one for the automorphy factor, which is the
Riemann-form positivity of the lattice, and one for the seed, which is what the induction
hypothesis supplies.

* `norm_poincareTermEntire_le` — the sup bound for the term from the two factors;
* `norm_multiIndexJetEvalCLM_poincareTermEntire_le` — **Cauchy's estimate for a packet jet of a
  Poincaré term**;
* `norm_multiIndexJetEvalCLM_poincareTermEntire_le_gaussian` — **the damping bound itself**, from a
  Gaussian bound on the automorphy factor and a polynomial bound on the seed.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}

/-- The value of a Poincaré term is the product of the two factors. -/
theorem norm_poincareTermEntire_le (ψ : AutomorphicFactor d Γ) (seed : MultivariateEntire d)
    (γ : Γ) {y : Fin d → ℂ} {Mψ Ms : ℝ} (hψ : ‖((ψ.factor γ).1 y)⁻¹‖ ≤ Mψ)
    (hs : ‖seed.1 (y + γ.1)‖ ≤ Ms) (hMψ : 0 ≤ Mψ) :
    ‖(poincareTermEntire ψ seed γ).1 y‖ ≤ Mψ * Ms := by
  have hval : (poincareTermEntire ψ seed γ).1 y = ((ψ.factor γ).1 y)⁻¹ * seed.1 (y + γ.1) := rfl
  rw [hval, norm_mul]
  exact mul_le_mul hψ hs (norm_nonneg _) hMψ

/-- **Cauchy's estimate for a packet jet of a Poincaré term.** -/
theorem norm_multiIndexJetEvalCLM_poincareTermEntire_le (ψ : AutomorphicFactor d Γ)
    (seed : MultivariateEntire d) (γ : Γ) (p : Fin d → ℂ) (a : Fin d →₀ ℕ)
    {ρ Mψ Ms : ℝ} (hρ : 0 < ρ) (hMψ : 0 ≤ Mψ)
    (hψ : ∀ y : Fin d → ℂ,
      ‖y - p‖ ≤ ((Fintype.card (MultiIndexSlot a) : ℕ) : ℝ) * ρ →
        ‖((ψ.factor γ).1 y)⁻¹‖ ≤ Mψ)
    (hs : ∀ y : Fin d → ℂ,
      ‖y - p‖ ≤ ((Fintype.card (MultiIndexSlot a) : ℕ) : ℝ) * ρ →
        ‖seed.1 (y + γ.1)‖ ≤ Ms) :
    ‖multiIndexJetEvalCLM p a (poincareTermEntire ψ seed γ)‖
      ≤ Mψ * Ms / ρ ^ (Fintype.card (MultiIndexSlot a)) :=
  norm_multiIndexJetEvalCLM_le p a _ hρ fun y hy =>
    norm_poincareTermEntire_le ψ seed γ (hψ y hy) (hs y hy) hMψ

/-- **The damping bound.**  A Gaussian bound on the inverse automorphy factor and a polynomial
bound on the seed give the damping datum's growth estimate. -/
theorem norm_multiIndexJetEvalCLM_poincareTermEntire_le_gaussian (ψ : AutomorphicFactor d Γ)
    (seed : MultivariateEntire d) (γ : Γ) (p : Fin d → ℂ) (a : Fin d →₀ ℕ)
    {ρ Cψ Cs B sigma0 S : ℝ} {r : ℕ} (hρ : 0 < ρ) (hCψ : 0 ≤ Cψ)
    (hψ : ∀ y : Fin d → ℂ,
      ‖y - p‖ ≤ ((Fintype.card (MultiIndexSlot a) : ℕ) : ℝ) * ρ →
        ‖((ψ.factor γ).1 y)⁻¹‖ ≤ Cψ * Real.exp (-sigma0 * S))
    (hs : ∀ y : Fin d → ℂ,
      ‖y - p‖ ≤ ((Fintype.card (MultiIndexSlot a) : ℕ) : ℝ) * ρ →
        ‖seed.1 (y + γ.1)‖ ≤ Cs * B ^ r) :
    ‖multiIndexJetEvalCLM p a (poincareTermEntire ψ seed γ)‖
      ≤ (Cψ * Cs / ρ ^ (Fintype.card (MultiIndexSlot a))) * B ^ r * Real.exp (-sigma0 * S) := by
  have hMψ : (0 : ℝ) ≤ Cψ * Real.exp (-sigma0 * S) :=
    mul_nonneg hCψ (Real.exp_nonneg _)
  have h := norm_multiIndexJetEvalCLM_poincareTermEntire_le ψ seed γ p a hρ hMψ hψ hs
  refine le_trans h (le_of_eq ?_)
  field_simp

end

end GaloisForLFunctions.HTGeometry
