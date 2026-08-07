import GaloisForLFunctions.RHTower.RiemannTower
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence

/-!
# Exact theta-endpoint residual

The entire theta--Mellin completion `completedRiemannZeta₀` differs from the rational value forced
at a zero of `xi` by one exact residual.  The residual is a nonzero rational multiple of `xi`
itself.  Consequently finite inverse-height endpoint expansions cannot create a zero-location
condition: they must resolve this residual rather than only its algebraic asymptotic series.
-/

namespace RHTower

open Complex

/-- Difference between the entire theta--Mellin completion and the rational value forced by
`xi s = 0`. -/
noncomputable def xiThetaEndpointResidual (s : ℂ) : ℂ :=
  completedRiemannZeta₀ s + 1 / (s * (s - 1))

/-- **Exact endpoint-residual identity.** Away from the completion endpoints, the residual is
exactly `2 * xi s / (s * (s - 1))`. -/
theorem xiThetaEndpointResidual_eq (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    xiThetaEndpointResidual s = 2 * xi s / (s * (s - 1)) := by
  rw [xiThetaEndpointResidual, xi]
  field_simp [hs0, sub_ne_zero.mpr hs1]

/-- The rational endpoint anchor is attained exactly at an `xi` zero. -/
theorem completedRiemannZeta₀_eq_neg_inv_mul_iff_xi_eq_zero
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    completedRiemannZeta₀ s = -(1 / (s * (s - 1))) ↔ xi s = 0 := by
  have hres := xiThetaEndpointResidual_eq s hs0 hs1
  constructor
  · intro h
    rw [xiThetaEndpointResidual, h, neg_add_cancel] at hres
    have hden : s * (s - 1) ≠ 0 := mul_ne_zero hs0 (sub_ne_zero.mpr hs1)
    simpa [hden] using hres.symm
  · intro h
    simp [h] at hres
    rw [xiThetaEndpointResidual] at hres
    linear_combination hres

/-- **The Riemann hypothesis as a critical-line law for the endpoint anchor.**  The rational anchor
`Λ₀(s) = -1/(s(s-1))` is attained exactly on the `ξ` divisor, and every `ξ` zero lies in the open
critical strip, so RH is the statement that the anchor can only be attained on the critical line. -/
theorem riemannHypothesis_iff_completedRiemannZeta₀_eq_neg_inv_mul_criticalLine :
    RiemannHypothesis ↔
      ∀ s : ℂ, s ≠ 0 → s ≠ 1 →
        completedRiemannZeta₀ s = -(1 / (s * (s - 1))) → s.re = 1 / 2 := by
  rw [riemannHypothesis_iff_xi_zero_re_eq_half]
  constructor
  · intro h s hs0 hs1 hanchor
    exact h s ((completedRiemannZeta₀_eq_neg_inv_mul_iff_xi_eq_zero s hs0 hs1).mp hanchor)
  · intro h ρ hz
    obtain ⟨h0, h1⟩ := xi_zero_re_mem_open_unit hz
    have hs0 : ρ ≠ 0 := by
      intro hc
      rw [hc, Complex.zero_re] at h0
      exact absurd h0 (lt_irrefl 0)
    have hs1 : ρ ≠ 1 := by
      intro hc
      rw [hc, Complex.one_re] at h1
      exact absurd h1 (lt_irrefl 1)
    exact h ρ hs0 hs1 ((completedRiemannZeta₀_eq_neg_inv_mul_iff_xi_eq_zero ρ hs0 hs1).mpr hz)

end RHTower
