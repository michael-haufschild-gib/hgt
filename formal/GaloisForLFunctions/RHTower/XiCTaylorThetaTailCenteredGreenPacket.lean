import GaloisForLFunctions.RHTower.XiCTaylorThetaTailProuhetSeamInvariant
import GaloisForLFunctions.RHTower.ThetaWignerCenterMix

/-!
# Centered Green packets for the completed theta-tail potential

The completed potential satisfies the exact inhomogeneous equation

`-V'' + V / 4 = Phi`.

Applying its Green identity in the two opposite translation directions cancels the completed
survival slope.  The resulting centered translate difference is exactly a positive compact
average of the full canonical Xi source.  This is a source-specific value relation.  It is only
a bridge for the current problem: on the Fourier side it multiplies Xi by an elementary centered
translate factor and therefore does not by itself orient the surviving Xi current.
-/

open Real MeasureTheory Set

namespace RHTower

noncomputable section

/-- Wronskian form of the one-dimensional Green endpoint identity for
`-f'' + f / 4 = q`. -/
private theorem green_endpoint_identity
    (f fp q : ℝ → ℝ)
    (hf : ∀ u : ℝ, HasDerivAt f (fp u) u)
    (hfp : ∀ u : ℝ, HasDerivAt fp ((1 / 4 : ℝ) * f u - q u) u)
    (hq : Continuous q)
    (L : ℝ) :
    (∫ u : ℝ in 0..L,
        2 * Real.sinh ((L - u) / 2) * q u) =
      Real.cosh (L / 2) * f 0 +
        2 * Real.sinh (L / 2) * fp 0 - f L := by
  let k : ℝ → ℝ := fun u => 2 * Real.sinh ((L - u) / 2)
  let kp : ℝ → ℝ := fun u => -Real.cosh ((L - u) / 2)
  let F : ℝ → ℝ := fun u => -k u * fp u + kp u * f u
  have hk : ∀ u : ℝ, HasDerivAt k (kp u) u := by
    intro u
    dsimp [k, kp]
    have hraw := (((hasDerivAt_const u L).sub
      (hasDerivAt_id u)).div_const 2).sinh.const_mul 2
    have hraw' := hraw.congr_deriv
      (g' := -Real.cosh ((L - u) / 2)) (by
        simp only [Pi.sub_apply, id_eq]
        ring)
    exact hraw'.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  have hkp : ∀ u : ℝ, HasDerivAt kp ((1 / 4 : ℝ) * k u) u := by
    intro u
    dsimp [k, kp]
    have hraw := ((((hasDerivAt_const u L).sub
      (hasDerivAt_id u)).div_const 2).cosh).neg
    have hraw' := hraw.congr_deriv
      (g' := (1 / 4 : ℝ) * (2 * Real.sinh ((L - u) / 2))) (by
        simp only [Pi.sub_apply, id_eq]
        ring)
    exact hraw'.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  have hF : ∀ u : ℝ, HasDerivAt F (k u * q u) u := by
    intro u
    dsimp [F]
    have hraw := ((hk u).neg.mul (hfp u)).add ((hkp u).mul (hf u))
    have hraw' := hraw.congr_deriv (g' := k u * q u) (by
      simp only [Pi.neg_apply]
      ring)
    exact hraw'.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  have hderiv : deriv F = fun u => k u * q u := by
    funext u
    exact (hF u).deriv
  have hdiff : ∀ u ∈ Set.uIcc (0 : ℝ) L, DifferentiableAt ℝ F u := by
    intro u _hu
    exact (hF u).differentiableAt
  have hkcont : Continuous k := by
    dsimp [k]
    fun_prop
  have hcont : Continuous (fun u => k u * q u) := hkcont.mul hq
  have hfund := intervalIntegral.integral_deriv_eq_sub'
    F hderiv hdiff hcont.continuousOn
  rw [hfund]
  dsimp [F, k, kp]
  simp only [sub_self, zero_div, Real.sinh_zero, mul_zero, neg_zero,
    Real.cosh_zero]
  ring_nf

/-- The reflection-balanced translate packet of the completed potential. -/
def thetaCuspCompletedTailPotentialCenteredDifference (L x : ℝ) : ℝ :=
  2 * Real.cosh (L / 2) * thetaCuspCompletedTailPotential x -
    thetaCuspCompletedTailPotential (x + L) -
    thetaCuspCompletedTailPotential (x - L)

/-- Exact two-sided Green relation.  The two completed-survival slope terms cancel, so only the
full canonical source remains. -/
theorem thetaCuspCompletedTailPotential_centeredDifference_eq_integral
    (L x : ℝ) :
    thetaCuspCompletedTailPotentialCenteredDifference L x =
      ∫ u : ℝ in 0..L,
        2 * Real.sinh ((L - u) / 2) *
          (thetaCuspFullSource (x + u) + thetaCuspFullSource (x - u)) := by
  let V : ℝ → ℝ := thetaCuspCompletedTailPotential
  let S : ℝ → ℝ := thetaCuspCompletedSurvivalRemainder
  let Phi : ℝ → ℝ := thetaCuspFullSource
  have hplus := green_endpoint_identity
    (fun u : ℝ => V (x + u))
    (fun u : ℝ => -(1 / 4 : ℝ) * S (x + u))
    (fun u : ℝ => Phi (x + u))
    (fun u => by
      have hraw := (hasDerivAt_thetaCuspCompletedTailPotential (x + u)).comp u
        ((hasDerivAt_const u x).add (hasDerivAt_id u))
      have hraw' := hraw.congr_deriv
        (g' := -(1 / 4 : ℝ) * S (x + u)) (by ring)
      exact hraw'.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _ => rfl))
    (fun u => by
      have h := (hasDerivAt_thetaCuspCompletedSurvivalRemainder (x + u)).comp u
        ((hasDerivAt_const u x).add (hasDerivAt_id u))
      have hraw := h.const_mul (-(1 / 4 : ℝ))
      have hraw' := hraw.congr_deriv
        (g' := (1 / 4 : ℝ) * thetaCuspCompletedTailPotential (x + u) -
          thetaCuspFullSource (x + u)) (by
          linarith [
            thetaCuspTailSecondEvenRemainder_add_completedTailPotential (x + u)])
      exact hraw'.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _ => rfl))
    (contDiff_thetaCuspFullSource.continuous.comp
      (continuous_const.add continuous_id)) L
  have hminus := green_endpoint_identity
    (fun u : ℝ => V (x - u))
    (fun u : ℝ => (1 / 4 : ℝ) * S (x - u))
    (fun u : ℝ => Phi (x - u))
    (fun u => by
      have hraw := (hasDerivAt_thetaCuspCompletedTailPotential (x - u)).comp u
        ((hasDerivAt_const u x).sub (hasDerivAt_id u))
      have hraw' := hraw.congr_deriv
        (g' := (1 / 4 : ℝ) * S (x - u)) (by ring)
      exact hraw'.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _ => rfl))
    (fun u => by
      have h := (hasDerivAt_thetaCuspCompletedSurvivalRemainder (x - u)).comp u
        ((hasDerivAt_const u x).sub (hasDerivAt_id u))
      have hraw := h.const_mul (1 / 4 : ℝ)
      have hraw' := hraw.congr_deriv
        (g' := (1 / 4 : ℝ) * thetaCuspCompletedTailPotential (x - u) -
          thetaCuspFullSource (x - u)) (by
          linarith [
            thetaCuspTailSecondEvenRemainder_add_completedTailPotential (x - u)])
      exact hraw'.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _ => rfl))
    (contDiff_thetaCuspFullSource.continuous.comp
      (continuous_const.sub continuous_id)) L
  rw [show (fun u : ℝ => 2 * Real.sinh ((L - u) / 2) *
      (thetaCuspFullSource (x + u) + thetaCuspFullSource (x - u))) =
      fun u : ℝ =>
        2 * Real.sinh ((L - u) / 2) * thetaCuspFullSource (x + u) +
        2 * Real.sinh ((L - u) / 2) * thetaCuspFullSource (x - u) by
      funext u
      ring]
  rw [intervalIntegral.integral_add]
  · dsimp [thetaCuspCompletedTailPotentialCenteredDifference, V, S, Phi]
      at hplus hminus ⊢
    simp only [add_zero, sub_zero] at hplus hminus
    rw [hplus, hminus]
    ring
  · apply Continuous.intervalIntegrable
    exact (by fun_prop : Continuous fun u : ℝ =>
      2 * Real.sinh ((L - u) / 2)).mul
        (contDiff_thetaCuspFullSource.continuous.comp
          (continuous_const.add continuous_id))
  · apply Continuous.intervalIntegrable
    exact (by fun_prop : Continuous fun u : ℝ =>
      2 * Real.sinh ((L - u) / 2)).mul
        (contDiff_thetaCuspFullSource.continuous.comp
          (continuous_const.sub continuous_id))

/-- For a nonnegative translation length the centered potential packet is nonnegative.  This is
an exact consequence of the canonical source relation, not a separate positivity assumption. -/
theorem thetaCuspCompletedTailPotentialCenteredDifference_nonneg
    {L : ℝ} (hL : 0 ≤ L) (x : ℝ) :
    0 ≤ thetaCuspCompletedTailPotentialCenteredDifference L x := by
  rw [thetaCuspCompletedTailPotential_centeredDifference_eq_integral]
  apply intervalIntegral.integral_nonneg hL
  intro u hu
  apply mul_nonneg
  · exact mul_nonneg (by norm_num)
      (Real.sinh_nonneg_iff.mpr (by linarith [hu.2]))
  · exact add_nonneg
      (thetaCuspFullSource_nonneg _) (thetaCuspFullSource_nonneg _)

end

end RHTower
