import GaloisForLFunctions.HTGeometry.FiniteMonotonicityVariation
import GaloisForLFunctions.RHTower.ProlateBandSymmetric

/-!
# One-turning-point variation mechanism for prolate modes

The prolate eigen-equation has the exact Sturm-flux form

`((1-y²) ψ')' = (χ + c² y²) ψ`.

The quadratic factor has at most one zero on the positive half-band.  Once its turning point and
the nodal zeros of `ψ` are inserted into a partition, every open cell has a fixed sign on the
right.  The universal Sturm-flux theorem then allows at most one stationary point per cell, and
the finite-monotonicity theorem turns the resulting fixed cell count plus a sup bound into a total
variation bound.

This module formalizes the differential connector and the per-cell critical-point law.  It makes
no asymptotic, spectral-index, or RH assumption.
-/

open Set

namespace RHTower

open HTGeometry

/-- The prolate eigen-equation is exactly a first-order equation for the weighted derivative. -/
theorem deriv_sturmFlux_prolate_eq {c χ : ℝ} {ψ : ℝ → ℝ}
    (hψ2 : Differentiable ℝ (deriv ψ))
    (heig : ∀ y, prolateSLAction c ψ y = χ * ψ y) (y : ℝ) :
    deriv (sturmFlux (fun t : ℝ => 1 - t ^ (2 : ℕ)) ψ) y =
      (χ + c ^ (2 : ℕ) * y ^ (2 : ℕ)) * ψ y := by
  unfold sturmFlux
  rw [(hasDerivAt_bandFlux (hψ2 y)).deriv]
  have h := heig y
  simp only [prolateSLAction] at h
  linear_combination h

/-- The prolate Sturm flux is continuous for every twice differentiable mode. -/
theorem continuous_sturmFlux_prolate {ψ : ℝ → ℝ}
    (hψ2 : Differentiable ℝ (deriv ψ)) :
    Continuous (sturmFlux (fun t : ℝ => 1 - t ^ (2 : ℕ)) ψ) := by
  unfold sturmFlux
  exact (continuous_const.sub (continuous_pow 2)).mul hψ2.continuous

/-- **Positive prolate sign-cell law.** On a band cell where
`(χ+c²y²)ψ(y)>0`, the prolate mode has at most one stationary point. -/
theorem prolate_criticalSet_subsingleton_of_rhs_pos
    {a b c χ : ℝ} {ψ : ℝ → ℝ}
    (hψ2 : Differentiable ℝ (deriv ψ))
    (heig : ∀ y, prolateSLAction c ψ y = χ * ψ y)
    (hpos : ∀ y ∈ Ioo a b, 0 < (χ + c ^ (2 : ℕ) * y ^ (2 : ℕ)) * ψ y) :
    {y | y ∈ Icc a b ∧ deriv ψ y = 0}.Subsingleton := by
  apply criticalSet_subsingleton_of_sturm_rhs_pos
    (fun t : ℝ => 1 - t ^ (2 : ℕ)) (fun t => χ + c ^ (2 : ℕ) * t ^ (2 : ℕ)) ψ
  · exact (continuous_sturmFlux_prolate hψ2).continuousOn
  · intro y hy
    exact deriv_sturmFlux_prolate_eq hψ2 heig y
  · exact hpos

/-- **Negative prolate sign-cell law.** On a band cell where
`(χ+c²y²)ψ(y)<0`, the prolate mode has at most one stationary point. -/
theorem prolate_criticalSet_subsingleton_of_rhs_neg
    {a b c χ : ℝ} {ψ : ℝ → ℝ}
    (hψ2 : Differentiable ℝ (deriv ψ))
    (heig : ∀ y, prolateSLAction c ψ y = χ * ψ y)
    (hneg : ∀ y ∈ Ioo a b, (χ + c ^ (2 : ℕ) * y ^ (2 : ℕ)) * ψ y < 0) :
    {y | y ∈ Icc a b ∧ deriv ψ y = 0}.Subsingleton := by
  apply criticalSet_subsingleton_of_sturm_rhs_neg
    (fun t : ℝ => 1 - t ^ (2 : ℕ)) (fun t => χ + c ^ (2 : ℕ) * t ^ (2 : ℕ)) ψ
  · exact (continuous_sturmFlux_prolate hψ2).continuousOn
  · intro y hy
    exact deriv_sturmFlux_prolate_eq hψ2 heig y
  · exact hneg

end RHTower
