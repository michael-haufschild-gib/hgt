import GaloisForLFunctions.HTGeometry.RadialMomentFlux
import GaloisForLFunctions.HTGeometry.HausdorffDifferenceInertia
import GaloisForLFunctions.RHTower.SquaredXiCompleteMonotonicity
import GaloisForLFunctions.RHTower.LocallyUniformZeroTransfer

/-!
# The first Hausdorff difference of the literal shifted-Xi moment tower is a radial flux

The completed-Xi reciprocal moments obey the unconditional first-order law
`d/dy s_y(k) = -(k+1)·s_y(k+1)`.  Feeding it into the radial flux law turns the quadratic form of
the first Hausdorff-difference matrix of the literal Route-U moments into the derivative of the
explicit primitive

`Φ_c(y) = ∑_{i,j} (c_i c_j/(i+j+1))·y^{i+j+1}·s_y(i+j)`.

Endpoint admission at a selected mass is therefore monotonicity of this integrated flux, and by
the quadrature description of the same form it is exactly the absence of a quadrature node above
the moving apex `1/y`.
-/

open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- The literal Route-U shifted reciprocal moment tower. -/
def xiShiftedMomentTower (y : ℝ) (k : ℕ) : ℝ := (xiShiftedReciprocalMoment y k).re

/-- **(SAHI.21) The literal moment tower obeys the first-order law.** -/
theorem hasDerivAt_xiShiftedMomentTower {y : ℝ} (hy : 0 < y) (k : ℕ) :
    HasDerivAt (fun v : ℝ => xiShiftedMomentTower v k)
      (-((k : ℝ) + 1) * xiShiftedMomentTower y (k + 1)) y :=
  hasDerivAt_re_xiShiftedReciprocalMoment hy k

/-- **(SAHI.22)/(SAHI.23) The first Hausdorff difference of the literal Route-U moments is the
derivative of the explicit radial flux.** -/
theorem hasDerivAt_xiShiftedRadialFlux {y : ℝ} (hy : 0 < y) {n : ℕ} (c : Fin (n + 1) → ℝ) :
    HasDerivAt (radialFlux xiShiftedMomentTower c)
      (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), c i * c j *
        (y ^ ((i : ℕ) + (j : ℕ)) * xiShiftedMomentTower y ((i : ℕ) + (j : ℕ))
          - y ^ ((i : ℕ) + (j : ℕ) + 1) * xiShiftedMomentTower y ((i : ℕ) + (j : ℕ) + 1))) y :=
  hasDerivAt_radialFlux c fun k => hasDerivAt_xiShiftedMomentTower hy k

/-- **The radial flux is monotone exactly when no quadrature node passes the moving apex.**  The
derivative of the flux is nonnegative for every coefficient vector as soon as every Gauss node of
the moment sequence at that mass lies below `1/y`. -/
theorem hasDerivAt_xiShiftedRadialFlux_nonneg {y : ℝ} {n : ℕ}
    (h : HTGeometry.PositiveMomentForm (xiShiftedMomentTower y))
    (hall : ∀ x ∈ HTGeometry.gaussNodes (xiShiftedMomentTower y) n, y * x ≤ 1)
    (c : Fin (n + 1) → ℝ) :
    0 ≤ ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), c i * c j *
      (y ^ ((i : ℕ) + (j : ℕ)) * xiShiftedMomentTower y ((i : ℕ) + (j : ℕ))
        - y ^ ((i : ℕ) + (j : ℕ) + 1) * xiShiftedMomentTower y ((i : ℕ) + (j : ℕ) + 1)) :=
  HTGeometry.hausdorffDifferenceQuadratic_nonneg h n y hall c

/-- **A super-apex node makes the radial flux strictly decreasing in some direction.** -/
theorem exists_neg_xiShiftedRadialFlux_deriv {y : ℝ} (hy : 0 < y) {n : ℕ}
    (h : HTGeometry.PositiveMomentForm (xiShiftedMomentTower y))
    {x₀ : ℝ} (hx₀ : x₀ ∈ HTGeometry.gaussNodes (xiShiftedMomentTower y) n)
    (hsuper : 1 < y * x₀) :
    ∃ c : Fin (n + 1) → ℝ,
      (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), c i * c j *
        (y ^ ((i : ℕ) + (j : ℕ)) * xiShiftedMomentTower y ((i : ℕ) + (j : ℕ))
          - y ^ ((i : ℕ) + (j : ℕ) + 1) * xiShiftedMomentTower y ((i : ℕ) + (j : ℕ) + 1))) < 0 :=
  HTGeometry.exists_neg_hausdorffDifferenceQuadratic h n (ne_of_gt hy) hx₀ hsuper


/-! ## Hard-edge ancestry of a negative limit root -/

/-- **(SAHI §5) A negative isolated root of the hard-edge limit produces roots of the cleared hard
approximants nearby.**  This is the local Hurwitz existence step of the corpus applied to the
cleared hard polynomials. -/
theorem eventually_exists_hard_root_near
    {S : ℕ → ℂ → ℂ} {F : ℂ → ℂ}
    (hconv : TendstoLocallyUniformly S F Filter.atTop)
    (hF : Differentiable ℂ F)
    (hSn : ∀ᶠ n in Filter.atTop, Differentiable ℂ (S n))
    {r ρ : ℝ} (hρ : 0 < ρ) (hzero : F ((r : ℝ) : ℂ) = 0)
    (hsphere : ∀ w ∈ Metric.sphere (((r : ℝ) : ℂ)) ρ, F w ≠ 0) :
    ∀ᶠ n in Filter.atTop, ∃ w ∈ Metric.closedBall (((r : ℝ) : ℂ)) ρ, S n w = 0 :=
  eventually_exists_zero_closedBall_of_tendstoLocallyUniformly hconv hF hSn hρ hzero hsphere

/-- **(SAHI §5) A real approximant root near a negative limit root is a super-apex node.**  Its
hard coordinate is negative, so the attached finite quadrature node lies strictly above the moving
apex `1/y`. -/
theorem normalizedNode_gt_one_of_near_negative_root {r ρ u y : ℝ}
    (hρr : ρ < -r) (hu : |u - r| ≤ ρ) (hsum : 0 < y + u) :
    1 < HTGeometry.normalizedNode y (HTGeometry.hardNode y u) := by
  have hle := (abs_le.1 hu).2
  have hneg : u < 0 := by linarith
  exact HTGeometry.normalizedNode_hardNode_gt_one hneg hsum

/-- The hard coordinate of that node is the approximant root itself. -/
theorem hardCoordinate_of_hard_root (y u : ℝ) :
    HTGeometry.hardCoordinate y (HTGeometry.hardNode y u) = u :=
  HTGeometry.hardCoordinate_hardNode y u

end RHTower

end
