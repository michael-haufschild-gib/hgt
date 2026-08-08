import GaloisForLFunctions.RHTower.ProlateWronskian
import GaloisForLFunctions.RHTower.ProlateEndpointNonvanishing

/-!
# One-dimensionality of the prolate eigenspace

The conserved Wronskian of the prolate problem is killed by the vanishing weight `1−y²` at the
singular endpoint, which gives the first-order relation `ψ₁ψ₂' = ψ₂ψ₁'` at interior points.  That
relation by itself does not identify the two solutions.  Combining it with interior ODE uniqueness
does: matching value and derivative at one interior point where `ψ₁` is nonzero forces the two
solutions to be proportional throughout the aperture.

Consequently the space of prolate solutions for a fixed eigenvalue which stay bounded near the
endpoint is at most one-dimensional.  No boundary condition is imposed by hand: the degeneracy is
removed by the singularity of the equation at the band edges, the same vanishing weight that makes
the operator symmetric there.
-/

noncomputable section

open Set

namespace RHTower

theorem deriv_const_mul_eq {k : ℝ} {ψ : ℝ → ℝ} (h1 : Differentiable ℝ ψ) :
    deriv (fun t : ℝ => k * ψ t) = fun t : ℝ => k * deriv ψ t := by
  funext t
  exact deriv_const_mul k (h1 t)

/-- Scaling a prolate solution by a constant again solves the same eigenvalue problem. -/
theorem prolateSLAction_const_mul {c χ k : ℝ} {ψ : ℝ → ℝ}
    (h1 : Differentiable ℝ ψ) (h2 : Differentiable ℝ (deriv ψ))
    (he : ∀ x : ℝ, prolateSLAction c ψ x = χ * ψ x) (x : ℝ) :
    prolateSLAction c (fun t : ℝ => k * ψ t) x = χ * (k * ψ x) := by
  have hd2 : deriv (deriv fun t : ℝ => k * ψ t) x = k * deriv (deriv ψ) x := by
    rw [deriv_const_mul_eq h1]
    exact deriv_const_mul k (h2 x)
  have hx := he x
  simp only [prolateSLAction] at hx ⊢
  rw [hd2, deriv_const_mul_eq h1]
  show (1 - x ^ 2) * (k * deriv (deriv ψ) x) - 2 * x * (k * deriv ψ x)
      - c ^ 2 * x ^ 2 * (k * ψ x) = χ * (k * ψ x)
  linear_combination k * hx

/-- **The prolate eigenspace is one-dimensional.**  Two solutions of the same prolate eigenvalue
problem which stay bounded near the singular endpoint are proportional on the whole aperture, as
soon as one of them is nonzero at a single interior point. -/
theorem prolate_eqOn_const_mul {c χ C : ℝ} {ψ₁ ψ₂ : ℝ → ℝ}
    (h₁1 : Differentiable ℝ ψ₁) (h₁2 : Differentiable ℝ (deriv ψ₁))
    (h₂1 : Differentiable ℝ ψ₂) (h₂2 : Differentiable ℝ (deriv ψ₂))
    (he₁ : ∀ y, prolateSLAction c ψ₁ y = χ * ψ₁ y)
    (he₂ : ∀ y, prolateSLAction c ψ₂ y = χ * ψ₂ y)
    (hb₁ : ∀ y ∈ Ico (0 : ℝ) 1, |ψ₁ y| ≤ C ∧ |deriv ψ₁ y| ≤ C)
    (hb₂ : ∀ y ∈ Ico (0 : ℝ) 1, |ψ₂ y| ≤ C ∧ |deriv ψ₂ y| ≤ C)
    {y₀ : ℝ} (hy₀ : y₀ ∈ Ioo (-1 : ℝ) 1) (hne : ψ₁ y₀ ≠ 0) :
    EqOn ψ₂ (fun t : ℝ => (ψ₂ y₀ / ψ₁ y₀) * ψ₁ t) (Ioo (-1 : ℝ) 1) := by
  set k : ℝ := ψ₂ y₀ / ψ₁ y₀ with hk
  refine eqOn_Ioo_of_prolateSLAction_eq_of_value_deriv_eq_at hy₀ h₂1 h₂2
    (h₁1.const_mul k) ?_ he₂ (fun x => prolateSLAction_const_mul h₁1 h₁2 he₁ x) ?_ ?_
  · rw [deriv_const_mul_eq h₁1]
    exact h₁2.const_mul k
  · rw [hk]
    exact (div_mul_cancel₀ (ψ₂ y₀) hne).symm
  · have hrel := prolate_firstOrder_relation h₁1 h₁2 h₂1 h₂2 he₁ he₂ hb₁ hb₂ hy₀
    rw [deriv_const_mul_eq h₁1, hk]
    field_simp
    linarith [hrel]

/-- A prolate solution bounded near the endpoint which vanishes at one interior point at which a
companion solution is nonzero vanishes on the whole aperture. -/
theorem prolate_eq_zero_of_eq_zero {c χ C : ℝ} {ψ₁ ψ₂ : ℝ → ℝ}
    (h₁1 : Differentiable ℝ ψ₁) (h₁2 : Differentiable ℝ (deriv ψ₁))
    (h₂1 : Differentiable ℝ ψ₂) (h₂2 : Differentiable ℝ (deriv ψ₂))
    (he₁ : ∀ y, prolateSLAction c ψ₁ y = χ * ψ₁ y)
    (he₂ : ∀ y, prolateSLAction c ψ₂ y = χ * ψ₂ y)
    (hb₁ : ∀ y ∈ Ico (0 : ℝ) 1, |ψ₁ y| ≤ C ∧ |deriv ψ₁ y| ≤ C)
    (hb₂ : ∀ y ∈ Ico (0 : ℝ) 1, |ψ₂ y| ≤ C ∧ |deriv ψ₂ y| ≤ C)
    {y₀ : ℝ} (hy₀ : y₀ ∈ Ioo (-1 : ℝ) 1) (hne : ψ₁ y₀ ≠ 0) (hz : ψ₂ y₀ = 0) :
    EqOn ψ₂ 0 (Ioo (-1 : ℝ) 1) := by
  intro y hy
  have h := prolate_eqOn_const_mul h₁1 h₁2 h₂1 h₂2 he₁ he₂ hb₁ hb₂ hy₀ hne hy
  simp only [hz, zero_div, zero_mul] at h
  simpa using h


/-- **Prolate zeros are simple.**  A prolate mode which is not identically zero on the aperture has
nonvanishing derivative at each of its interior zeros: value and derivative cannot both vanish, or
interior uniqueness against the zero solution would annihilate the mode. -/
theorem prolate_deriv_ne_zero_of_eq_zero {c χ : ℝ} {ψ : ℝ → ℝ}
    (h1 : Differentiable ℝ ψ) (h2 : Differentiable ℝ (deriv ψ))
    (he : ∀ y, prolateSLAction c ψ y = χ * ψ y)
    (hnt : ∃ z ∈ Ioo (-1 : ℝ) 1, ψ z ≠ 0)
    {y₀ : ℝ} (hy₀ : y₀ ∈ Ioo (-1 : ℝ) 1) (hz : ψ y₀ = 0) :
    deriv ψ y₀ ≠ 0 := by
  intro hd
  obtain ⟨z, hzmem, hzne⟩ := hnt
  have hzero : Differentiable ℝ (deriv fun _ : ℝ => (0 : ℝ)) := by
    rw [deriv_const']
    exact differentiable_const 0
  have heq := eqOn_Ioo_of_prolateSLAction_eq_of_value_deriv_eq_at hy₀ h1 h2
    (differentiable_const (0 : ℝ)) hzero he
    (by intro x; simp [prolateSLAction, deriv_const']) (by simpa using hz)
    (by simp [hd, deriv_const'])
  exact hzne (heq hzmem)

end RHTower
