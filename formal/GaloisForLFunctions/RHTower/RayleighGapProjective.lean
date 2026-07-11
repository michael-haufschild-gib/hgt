import GaloisForLFunctions.RHTower.RayleighScalarShift

/-!
# Rayleigh excess controls projective ground-vector error

Let `v` be a unit eigenvector of a symmetric operator at energy `epsilon`.  If the shifted form is
coercive with constant `gap` on the component of a unit source `g` orthogonal to `v`, then the
squared projective angle from `g` to the eigenline of `v` is at most the Rayleigh excess divided by
`gap`.

This is the source-pure spectral transfer used in the CCM determinant route.  It contains no zeta
zero or RH predicate: an analytic estimate of one specified source vector feeds the theorem, and
the conclusion is quantitative convergence to a specified eigendirection.
-/

open scoped InnerProductSpace

namespace RHTower

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Subtracting the component of `g` on a unit vector `v` leaves a vector orthogonal to `v`. -/
theorem unitProjectiveRemainder_inner_eq_zero
    {v g : E} (hv : ‖v‖ = 1) :
    inner 𝕜 v (g - inner 𝕜 v g • v) = 0 := by
  rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hv]
  simp

/-- For unit vectors, the norm squared of the orthogonal projective remainder is the squared sine
of their projective angle. -/
theorem norm_projectiveRemainder_sq
    {v g : E} (hv : ‖v‖ = 1) (hg : ‖g‖ = 1) :
    ‖g - inner 𝕜 v g • v‖ ^ 2 = 1 - ‖inner 𝕜 v g‖ ^ 2 := by
  let a : 𝕜 := inner 𝕜 v g
  let w : E := g - a • v
  have hvw : inner 𝕜 (a • v) w = 0 := by
    rw [inner_smul_left]
    simp [w, a, unitProjectiveRemainder_inner_eq_zero hv]
  have hsum : a • v + w = g := by simp [w]
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (a • v) w hvw
  rw [hsum, norm_smul, hv, mul_one, hg] at hpyth
  change ‖w‖ ^ 2 = 1 - ‖a‖ ^ 2
  nlinarith

/-- A symmetric form shifted by an eigenvalue depends only on the component orthogonal to the
corresponding eigenvector. -/
theorem shiftedForm_projectiveDecomposition
    (T : E →L[𝕜] E) (hT : (T : E →ₗ[𝕜] E).IsSymmetric)
    {v g : E} {epsilon : ℝ}
    (hTv : T v = (epsilon : 𝕜) • v) :
    let w := g - inner 𝕜 v g • v
    (T - (epsilon : 𝕜) • ContinuousLinearMap.id 𝕜 E).reApplyInnerSelf g =
      (T - (epsilon : 𝕜) • ContinuousLinearMap.id 𝕜 E).reApplyInnerSelf w := by
  let S : E →L[𝕜] E := T - (epsilon : 𝕜) • ContinuousLinearMap.id 𝕜 E
  let a : 𝕜 := inner 𝕜 v g
  let w : E := g - a • v
  have hS : (S : E →ₗ[𝕜] E).IsSymmetric :=
    hT.sub (LinearMap.IsSymmetric.id.smul (RCLike.conj_ofReal epsilon))
  have hSv : S v = 0 := by
    simp [S, hTv]
  have hdecomp : g = a • v + w := by simp [w]
  change S.reApplyInnerSelf g = S.reApplyInnerSelf w
  rw [hdecomp]
  simp [ContinuousLinearMap.reApplyInnerSelf_apply, hSv, hS.apply_clm]

/-- A positive gap on the orthogonal component bounds its squared norm by the dimensionless
Rayleigh excess. -/
theorem projectiveRemainder_sq_le_rayleighExcess_div_gap
    (T : E →L[𝕜] E) (hT : (T : E →ₗ[𝕜] E).IsSymmetric)
    {v g : E} {epsilon gap : ℝ}
    (hg : ‖g‖ = 1)
    (hTv : T v = (epsilon : 𝕜) • v) (hgap : 0 < gap)
    (hcoercive : gap * ‖g - inner 𝕜 v g • v‖ ^ 2 ≤
      (T - (epsilon : 𝕜) • ContinuousLinearMap.id 𝕜 E).reApplyInnerSelf
        (g - inner 𝕜 v g • v)) :
    ‖g - inner 𝕜 v g • v‖ ^ 2 ≤
      (T.rayleighQuotient g - epsilon) / gap := by
  have hg0 : g ≠ 0 := by
    intro h
    simp [h] at hg
  have hform := shiftedForm_projectiveDecomposition T hT (g := g) hTv
  dsimp only at hform
  rw [← hform] at hcoercive
  have hshift := rayleighExcess_add_real_smul_id T (-epsilon) epsilon g hg0
  norm_num at hshift
  have hray :
      (T - (epsilon : 𝕜) • ContinuousLinearMap.id 𝕜 E).reApplyInnerSelf g =
        T.rayleighQuotient g - epsilon := by
    rw [ContinuousLinearMap.rayleighQuotient] at hshift
    rw [hg, one_pow, div_one] at hshift
    simpa [sub_eq_add_neg] using hshift
  rw [hray] at hcoercive
  exact (le_div_iff₀ hgap).2 (by simpa [mul_comm] using hcoercive)

/-- **Rayleigh-gap projective transfer.** For unit `v` and `g`, coercivity of the shifted form on
the projective remainder gives the squared-angle estimate
`1 - ‖inner v g‖² ≤ (Rayleigh(g) - epsilon) / gap`. -/
theorem one_sub_norm_inner_sq_le_rayleighExcess_div_gap
    (T : E →L[𝕜] E) (hT : (T : E →ₗ[𝕜] E).IsSymmetric)
    {v g : E} {epsilon gap : ℝ}
    (hv : ‖v‖ = 1) (hg : ‖g‖ = 1)
    (hTv : T v = (epsilon : 𝕜) • v) (hgap : 0 < gap)
    (hcoercive : gap * ‖g - inner 𝕜 v g • v‖ ^ 2 ≤
      (T - (epsilon : 𝕜) • ContinuousLinearMap.id 𝕜 E).reApplyInnerSelf
        (g - inner 𝕜 v g • v)) :
    1 - ‖inner 𝕜 v g‖ ^ 2 ≤
      (T.rayleighQuotient g - epsilon) / gap := by
  rw [← norm_projectiveRemainder_sq hv hg]
  exact projectiveRemainder_sq_le_rayleighExcess_div_gap T hT hg hTv hgap hcoercive

end RHTower
