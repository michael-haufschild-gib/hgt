import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCoupledOddTransportSchur
/-!
# Exact normalized Schur-gap derivative along the actual source direction

The derivative separates the source quadratic from a nonnegative squared
transport gain. No sign of the source quadratic or global gap is assumed.
-/

namespace RHTower.ThetaCuspOddDirectionTransport
noncomputable section
open scoped ContDiff
local notation "Phi" => thetaCuspFullSource
local notation "D" => thetaCuspNativeOddHankelThreeDet

def normalizedBase (C x : ℝ) : ℝ :=
  (cofactorA x+C*thetaCuspCenterCompensationSource x*thetaCuspNativeOddHeadDet x)/Phi x^6

def normalizedB (x : ℝ) : ℝ := cofactorB x/Phi x^6

def normalizedD (x : ℝ) : ℝ := D x/Phi x^6

def normalizedGap (C x : ℝ) : ℝ := schurGap C x (direction x)/Phi x^6

private theorem differentiable_jet (n : ℕ) : Differentiable ℝ (thetaCuspNativeReflectionJet n) := by
  have hj (k : ℕ) : Differentiable ℝ (iteratedDeriv k Phi) :=
    contDiff_thetaCuspFullSource.differentiable_iteratedDeriv k
      (by exact_mod_cast ENat.coe_lt_top k)
  change Differentiable ℝ (fun x => thetaCuspNativeReflectionJet n x)
  simp_rw [thetaCuspNativeReflectionJet_eq]
  fun_prop

private theorem differentiable_moment (k : Fin 7) : Differentiable ℝ (moment k) :=
  (differentiable_jet _).const_mul _

private theorem differentiable_normalizedBase (C : ℝ) : Differentiable ℝ (normalizedBase C) := by
  have hj := differentiable_jet
  have hm := differentiable_moment
  have hp : Differentiable ℝ Phi := contDiff_thetaCuspFullSource.differentiable (by simp)
  have hp' : Differentiable ℝ (deriv Phi) := by
    simpa only [iteratedDeriv_one] using
      contDiff_thetaCuspFullSource.differentiable_iteratedDeriv 1 (by simp)
  have hn (x : ℝ) : Phi x^6 ≠ 0 := pow_ne_zero _ (thetaCuspFullSource_pos_all x).ne'
  unfold normalizedBase cofactorA thetaCuspCenterCompensationSource thetaCuspNativeOddHeadDet
  fun_prop

private theorem differentiable_normalizedB : Differentiable ℝ normalizedB := by
  have hm := differentiable_moment
  have hp : Differentiable ℝ Phi := contDiff_thetaCuspFullSource.differentiable (by simp)
  have hn (x : ℝ) : Phi x^6 ≠ 0 := pow_ne_zero _ (thetaCuspFullSource_pos_all x).ne'
  unfold normalizedB cofactorB
  fun_prop

private theorem differentiable_normalizedD : Differentiable ℝ normalizedD := by
  have hj := differentiable_jet
  have hp : Differentiable ℝ Phi := contDiff_thetaCuspFullSource.differentiable (by simp)
  have hn (x : ℝ) : Phi x^6 ≠ 0 := pow_ne_zero _ (thetaCuspFullSource_pos_all x).ne'
  unfold normalizedD thetaCuspNativeOddHankelThreeDet HilbertMetric.signedEvenHankelThreeDet
  fun_prop

private theorem normalizedGap_eq (C : ℝ) : normalizedGap C = fun x =>
    normalizedBase C x+normalizedD x*(direction x)^2+2*normalizedB x*direction x := by
  funext x
  unfold normalizedGap schurGap normalizedBase normalizedD normalizedB
  ring

/-- Exact gain along the literal residual-free transport, without any assumed source sign. -/
theorem normalizedGap_derivative (C : ℝ) {x : ℝ} (hx : x ≠ 0) :
    deriv (normalizedGap C) x =
      deriv (normalizedBase C) x+deriv normalizedD x*(direction x)^2+
        2*deriv normalizedB x*direction x+
        2*(D x*direction x+cofactorB x)^2/(x*transportWeight x*Phi x^6) := by
  have he := (differentiableAt_direction hx).hasDerivAt
  have h := ((differentiable_normalizedBase C x).hasDerivAt.add
    ((differentiable_normalizedD x).hasDerivAt.mul (he.pow 2))).add
    (((differentiable_normalizedB x).hasDerivAt.const_mul 2).mul he)
  change HasDerivAt (fun y => normalizedBase C y+normalizedD y*(direction y)^2+
    2*normalizedB y*direction y) _ x at h
  simp only [Pi.pow_apply] at h
  rw [← normalizedGap_eq] at h
  rw [h.deriv]
  have hr := direction_cancels_residual x
  have hd : deriv direction x = (D x*direction x+cofactorB x)/(transportWeight x*x) := by
    apply (eq_div_iff (mul_ne_zero (transportWeight_pos x).ne' hx)).mpr
    nlinarith only [hr]
  rw [hd]
  unfold normalizedD normalizedB
  field_simp [hx,(transportWeight_pos x).ne',(thetaCuspFullSource_pos_all x).ne']
  ring


/-- The complete source supplies a nonnegative squared gain on the positive center ray. -/
theorem normalizedGap_derivative_lower (C : ℝ) {x : ℝ} (hx : 0 < x) :
    deriv (normalizedBase C) x+deriv normalizedD x*(direction x)^2+
      2*deriv normalizedB x*direction x ≤ deriv (normalizedGap C) x := by
  rw [normalizedGap_derivative C hx.ne']
  have hw := transportWeight_pos x
  have hp := thetaCuspFullSource_pos_all x
  have hgain : 0 ≤ 2*(D x*direction x+cofactorB x)^2/
      (x*transportWeight x*Phi x^6) := by positivity
  linarith only [hgain]

end
end RHTower.ThetaCuspOddDirectionTransport
