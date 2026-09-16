import GaloisForLFunctions.RHTower.EulerPreScalarGammaReporterRigidity
import GaloisForLFunctions.RHTower.SoninCofinalGlobalEulerCarrier

/-!
# Cofinal-isometric transport cannot remove the Euler eight-unit cost

The literal full Euler prime--polar--Gamma source has squared norm tending to
eight.  This file closes a distinct apparent escape route: moving the complete
source through the canonical cofinal Sonin embeddings cannot change that
number.  Every such embedding is a linear isometry, including when its depth
is chosen as an arbitrary function of the critical parameter.

Thus a four-unit completion cannot be obtained by a cofinal change of Hilbert
carrier alone.  A surviving construction must change the signed incidence or
use a genuinely non-isometric relative channel before taking a positive Gram
energy.
-/

open Filter Set Topology
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RHTower

/-- Every linear isometry preserves the exact squared norm of the literal
positive Euler pre-scalar Gamma source. -/
theorem norm_linearIsometry_eulerPositivePreScalarGammaSource_sq
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (T : EulerPositiveL2 →ₗᵢ[ℂ] H) {sigma : ℝ} (hsigma : 1 < sigma) :
    ‖T (eulerPositivePreScalarGammaSource sigma hsigma)‖ ^ 2 =
      4 * (sigma - 1) ^ 2 * eulerPositiveLogMoment 2 sigma := by
  rw [T.norm_map]
  exact norm_eulerPositivePreScalarGammaSource_sq hsigma

/-- **Isometric-carrier no-go.**  For an arbitrary moving family of linear
isometries, the literal Euler source still has critical squared norm eight.
Thus an isometric change of carrier alone cannot reach a four-unit budget. -/
theorem tendsto_norm_linearIsometry_eulerPositivePreScalarGammaSource_sq
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (T : ℝ → EulerPositiveL2 →ₗᵢ[ℂ] H) :
    Tendsto
      (fun sigma : ℝ =>
        if hsigma : 1 < sigma then
          ‖T sigma (eulerPositivePreScalarGammaSource sigma hsigma)‖ ^ 2
        else 0)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 8) := by
  apply tendsto_norm_eulerPositivePreScalarGammaSource_sq.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  change 1 < sigma at hsigma
  simp only [dif_pos hsigma]
  rw [norm_linearIsometry_eulerPositivePreScalarGammaSource_sq]
  exact norm_eulerPositivePreScalarGammaSource_sq hsigma

/-- **Gram-faithful compression no-go.**  A bounded same-carrier map cannot
lower the source energy if it preserves the full source--damping Gram family
after acting on both entries.  Totality of that damping family forces
`T† T` to fix the source. -/
theorem norm_sq_map_eulerPositivePreScalarGammaSource_of_dampedGram
    {sigma : ℝ} (hsigma : 1 < sigma)
    (T : EulerPositiveL2 →L[ℂ] EulerPositiveL2)
    (hpair : ∀ (u : ℝ) (hu : 0 ≤ u),
      inner ℂ (T (eulerPositivePreScalarGammaSource sigma hsigma))
        (T (eulerPositiveCriticalDampedStateLp sigma u hsigma hu)) =
        inner ℂ (eulerPositivePreScalarGammaSource sigma hsigma)
          (eulerPositiveCriticalDampedStateLp sigma u hsigma hu)) :
    ‖T (eulerPositivePreScalarGammaSource sigma hsigma)‖ ^ 2 =
      ‖eulerPositivePreScalarGammaSource sigma hsigma‖ ^ 2 := by
  have hfixed : ContinuousLinearMap.adjoint T
      (T (eulerPositivePreScalarGammaSource sigma hsigma)) =
        eulerPositivePreScalarGammaSource sigma hsigma := by
    apply eq_of_inner_eulerPositiveCriticalDampedState_eq hsigma
    intro u hu
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact hpair u hu
  rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left]
  simp only [ContinuousLinearMap.comp_apply, hfixed, inner_self_eq_norm_sq]

/-- A canonical cofinal Sonin embedding preserves the exact squared norm of
the literal positive Euler pre-scalar Gamma source. -/
theorem norm_cofinalEulerPositiveSoninEmbedding_preScalarGammaSource_sq
    (c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r)
    (N : ℕ) {sigma : ℝ} (hsigma : 1 < sigma) :
    ‖cofinalEulerPositiveSoninEmbedding c d r hc hcd hr N
        (eulerPositivePreScalarGammaSource sigma hsigma)‖ ^ 2 =
      4 * (sigma - 1) ^ 2 * eulerPositiveLogMoment 2 sigma := by
  rw [(cofinalEulerPositiveSoninEmbedding c d r hc hcd hr N).norm_map]
  exact norm_eulerPositivePreScalarGammaSource_sq hsigma

/-- **Cofinal-isometric Euler no-go.**  No moving-depth schedule of canonical
Sonin isometries changes the critical eight-unit source cost. -/
theorem tendsto_norm_cofinalEulerPositiveSoninEmbedding_preScalarGammaSource_sq
    (c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r)
    (N : ℝ → ℕ) :
    Tendsto
      (fun sigma : ℝ =>
        if hsigma : 1 < sigma then
          ‖cofinalEulerPositiveSoninEmbedding c d r hc hcd hr (N sigma)
            (eulerPositivePreScalarGammaSource sigma hsigma)‖ ^ 2
        else 0)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 8) := by
  apply tendsto_norm_eulerPositivePreScalarGammaSource_sq.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  change 1 < sigma at hsigma
  simp only [dif_pos hsigma]
  rw [norm_cofinalEulerPositiveSoninEmbedding_preScalarGammaSource_sq]
  exact norm_eulerPositivePreScalarGammaSource_sq hsigma

end RHTower
