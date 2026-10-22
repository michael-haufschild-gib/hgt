import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFifthRootCurvatureVelocityLikelihoodReserve

/-!
# Theta C5 center velocity: second-likelihood reserve

After the third likelihood jet has been removed, the remaining second likelihood curvature is also
strictly favorable.  The exact coefficient is positive because convexity puts center action below
terminal action velocity; an exponential-action dichotomy then handles both signs of the literal
C5 affine coefficient.  Thus center velocity reduces to one first-atom-curvature core retaining
only actual action and actual first jet from the full theta source.
-/

open Real Set

namespace RHTower

noncomputable section

/-- Universal exponential-action coefficient forced by the literal C5 constants. -/
theorem c5VelocitySecondLikelihoodCoefficient_pos
    {A v t : ℝ} (ht : 0 < t) (hA : 0 < A) (hv : 0 < v) (hAv : A ≤ v) :
    0 < (Real.exp A - 1) * (30 * t + 15 * v - 1) + 3 * v := by
  let c := 30 * t + 15 * v - 1
  have hR : 0 < Real.exp A - 1 := by
    rw [sub_pos, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hA
  by_cases hc : 0 ≤ c
  · have hRc : 0 ≤ (Real.exp A - 1) * c := mul_nonneg hR.le hc
    dsimp only [c] at hRc ⊢
    linarith
  · have hcneg : c < 0 := lt_of_not_ge hc
    have hvfifteen : v < 1 / 15 := by
      dsimp only [c] at hcneg
      nlinarith
    have hvone : v < 1 := by linarith
    have hexpV : Real.exp v < 1 / (1 - v) :=
      Real.exp_bound_div_one_sub_of_interval' hv hvone
    have hden : 0 < 1 - v := by linarith
    have hratio : 1 / (1 - v) - 1 < 3 * v := by
      rw [show 1 / (1 - v) - 1 = v / (1 - v) by
        field_simp [hden.ne']
        ring_nf]
      rw [div_lt_iff₀ hden]
      have hfactor : 0 < 2 - 3 * v := by linarith
      have hpositive : 0 < v * (2 - 3 * v) := mul_pos hv hfactor
      nlinarith
    have hRthree : Real.exp A - 1 < 3 * v := calc
      Real.exp A - 1 ≤ Real.exp v - 1 :=
        sub_le_sub_right (Real.exp_le_exp.mpr hAv) 1
      _ < 1 / (1 - v) - 1 := sub_lt_sub_right hexpV 1
      _ < 3 * v := hratio
    have hmul : 3 * v * c < (Real.exp A - 1) * c :=
      mul_lt_mul_of_neg_right hRthree hcneg
    have hcplus : 0 < c + 1 := by
      dsimp only [c]
      nlinarith
    have hbase : 0 < 3 * v * (c + 1) :=
      mul_pos (mul_pos (by norm_num) hv) hcplus
    dsimp only [c] at hmul hbase ⊢
    nlinarith

/-- Center reflected action lies below its terminal action velocity. -/
theorem thetaCuspReflectedLogAction_zero_le_t_mul_jetOne
    {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedLogAction 0 t ≤
      t * thetaCuspReflectedLogJetOne 0 t := by
  have hq₁mono : StrictMono (thetaCuspReflectedLogJetOne 0) := by
    apply strictMono_of_deriv_pos
    intro x
    rw [(hasDerivAt_thetaCuspReflectedLogJetOne 0 x).deriv]
    unfold thetaCuspReflectedLogJetTwo
    rw [zero_add, zero_sub, thetaCuspLogCurvature_neg]
    nlinarith [thetaCuspLogCurvature_pos x]
  have hconv : StrictConvexOn ℝ Set.univ (thetaCuspReflectedLogAction 0) := by
    refine StrictMonoOn.strictConvexOn_of_deriv convex_univ ?_ ?_
    · intro x hx
      exact (hasDerivAt_thetaCuspReflectedLogAction 0 x).continuousAt.continuousWithinAt
    · intro x hx y hy hxy
      rw [(hasDerivAt_thetaCuspReflectedLogAction 0 x).deriv,
        (hasDerivAt_thetaCuspReflectedLogAction 0 y).deriv]
      exact hq₁mono hxy
  have hslope := hconv.convexOn.slope_le_deriv
    (Set.mem_univ (0 : ℝ)) (Set.mem_univ t) ht
    (hasDerivAt_thetaCuspReflectedLogAction 0 t).differentiableAt
  rw [(hasDerivAt_thetaCuspReflectedLogAction 0 t).deriv] at hslope
  have hzero : thetaCuspReflectedLogAction 0 0 = 0 := by
    unfold thetaCuspReflectedLogAction
    ring_nf
  have hslope' :
      thetaCuspReflectedLogAction 0 t / t ≤
        thetaCuspReflectedLogJetOne 0 t := by
    simpa only [slope_def_field, hzero, sub_zero] using hslope
  exact (div_le_iff₀ ht).mp hslope' |>.trans_eq (mul_comm _ _)

/-- Center core after replacing actual second jet by first-atom curvature. -/
def thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore (t : ℝ) : ℝ :=
  thetaCuspReflectedActionFifthRootVelocityCore
    (Real.exp (thetaCuspReflectedLogAction 0 t) - 1) t
    (thetaCuspReflectedLogJetOne 0 t)
    (2 * thetaCuspBornWittenLogCurvature 1 t)
    (-2 * thetaCuspFirstAtomLogJetThree t)

/-- Exact second-likelihood-curvature decomposition of the master-reserved core. -/
theorem thetaCuspCenterFifthRootVelocityMasterReservedCore_eq_firstAtomCurvature_add
    {t : ℝ} (ht : 0 < t) :
    thetaCuspCenterFifthRootVelocityMasterReservedCore t =
      thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore t +
        2 * t * thetaCuspLikelihoodSourceLogPartitionJetTwo t *
          ((Real.exp (thetaCuspReflectedLogAction 0 t) - 1) *
              (30 * t + 15 * t * thetaCuspReflectedLogJetOne 0 t - 1) +
            3 * t * thetaCuspReflectedLogJetOne 0 t) := by
  unfold thetaCuspCenterFifthRootVelocityMasterReservedCore
    thetaCuspCenterFifthRootVelocityLowerJetCore
    thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore
    thetaCuspReflectedActionFifthRootVelocityCore
  rw [thetaCuspReflectedLogJetTwo_zero_eq_likelihood ht]
  ring

/-- The exact coefficient of second likelihood curvature is strictly positive. -/
theorem thetaCuspCenterFifthRootVelocitySecondLikelihoodCoefficient_pos
    {t : ℝ} (ht : 0 < t) :
    0 < (Real.exp (thetaCuspReflectedLogAction 0 t) - 1) *
          (30 * t + 15 * t * thetaCuspReflectedLogJetOne 0 t - 1) +
        3 * t * thetaCuspReflectedLogJetOne 0 t := by
  simpa only [mul_assoc] using
    c5VelocitySecondLikelihoodCoefficient_pos
      (A := thetaCuspReflectedLogAction 0 t)
      (v := t * thetaCuspReflectedLogJetOne 0 t) ht
      (thetaCuspReflectedLogAction_pos ht)
      (mul_pos ht (thetaCuspReflectedLogJetOne_pos 0 ht))
      (thetaCuspReflectedLogAction_zero_le_t_mul_jetOne ht)

/-- Second likelihood curvature is strictly favorable inside the master-reserved core. -/
theorem thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore_lt_masterReservedCore
    {t : ℝ} (ht : 0 < t) :
    thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore t <
      thetaCuspCenterFifthRootVelocityMasterReservedCore t := by
  rw [thetaCuspCenterFifthRootVelocityMasterReservedCore_eq_firstAtomCurvature_add ht]
  have hg₂ := thetaCuspLikelihoodSourceLogPartitionJetTwo_pos ht.le
  have hcoefficient :=
    thetaCuspCenterFifthRootVelocitySecondLikelihoodCoefficient_pos ht
  have hcorrection :
      0 < 2 * t * thetaCuspLikelihoodSourceLogPartitionJetTwo t *
        ((Real.exp (thetaCuspReflectedLogAction 0 t) - 1) *
            (30 * t + 15 * t * thetaCuspReflectedLogJetOne 0 t - 1) +
          3 * t * thetaCuspReflectedLogJetOne 0 t) := by
    positivity
  linarith

/-- Nonnegative first-atom-curvature core forces strict literal center velocity. -/
theorem thetaCuspReflectedSourceFifthRootCurvatureVelocity_zero_pos_of_firstAtomCurvatureCore_nonneg
    {t : ℝ} (ht : 0 < t)
    (hcore : 0 ≤ thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore t) :
    0 < thetaCuspReflectedSourceFifthRootCurvatureVelocity 0 t := by
  apply thetaCuspReflectedSourceFifthRootCurvatureVelocity_zero_pos_of_masterReservedCore_nonneg ht
  exact le_trans hcore
    (thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore_lt_masterReservedCore ht).le

end

end RHTower
