import GaloisForLFunctions.RHTower.RiemannTower

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

end RHTower
