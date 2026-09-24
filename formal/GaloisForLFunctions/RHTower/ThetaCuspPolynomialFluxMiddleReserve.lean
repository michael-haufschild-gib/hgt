import GaloisForLFunctions.RHTower.ThetaCuspMiddleCompensationReserve
import GaloisForLFunctions.RHTower.ThetaCuspCenterCompensationFlux
import GaloisForLFunctions.RHTower.ThetaCuspCompensationNeutralAnchor

/-!
# Degree-twelve center-flux reserve on the complete-source compact chamber

The polynomial correction has zero integrated mass by
`integral_deriv_thetaCuspPolynomialFlux`. Its derivative has a strict,
aperture-uniform positive reserve on the full source-scale chamber
`q(r/2) ≤ 8`. This is a pointwise statement, not a signed-tail
or integrated Hankel positivity theorem.
-/

namespace RHTower
noncomputable section

private theorem radius_lt_one_of_scale_le_eight {r : ℝ}
    (hq : thetaCuspSingleAtomReflectionScale 1 (r/2) ≤ 8) : r < 1 := by
  by_contra h
  have hr : 1 ≤ r := le_of_not_gt h
  have he : Real.exp 1 ≤ Real.exp r := Real.exp_le_exp.mpr hr
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have he1 : (8/3 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h3e : 8 < 3*Real.exp 1 := by linarith only [he1]
  have hpie : 3*Real.exp 1 < Real.pi*Real.exp 1 :=
    mul_lt_mul_of_pos_right hpi (Real.exp_pos 1)
  have hm : Real.pi*Real.exp 1 ≤ Real.pi*Real.exp r :=
    mul_le_mul_of_nonneg_left he Real.pi_pos.le
  have hq' : Real.pi*Real.exp r ≤ 8 := by
    simpa [thetaCuspSingleAtomReflectionScale, show 2 * (r / 2) = r by ring] using hq
  linarith only [h3e, hpie, hm, hq']

/-- Source slope and the neutral-center sign leave a strict degree-twelve compact reserve. -/
theorem thetaCuspDegreeTwelve_source_reserve_le_eight {r : ℝ}
    (hr : 0 < r)
    (hq1 : thetaCuspSingleAtomReflectionScale 1 (r/2) ≤ 8) :
    thetaCuspFullSource (r/2)^(2 : ℕ) <
      13*thetaCuspFullSource (r/2)^(2 : ℕ) +
        r*thetaCuspFullSource (r/2)*deriv thetaCuspFullSource (r/2) := by
  by_cases hq0 : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 (r/2)
  · let F := thetaCuspFullSource (r/2)
    let D := deriv thetaCuspFullSource (r/2)
    have hF : 0 < F := thetaCuspFullSource_pos_all (r/2)
    have hF2 : 0 < F^(2 : ℕ) := sq_pos_of_pos hF
    have hr1 := radius_lt_one_of_scale_le_eight hq1
    have hs := thetaCuspFullSource_slope_affine_lower_eight hq0 hq1
    have hcoef : -12 ≤ 4-2*thetaCuspSingleAtomReflectionScale 1 (r/2) := by
      linarith only [hq1]
    have hSlope : -12*F ≤ D :=
      (mul_le_mul_of_nonneg_right hcoef hF.le).trans hs
    have hm := mul_le_mul_of_nonneg_left hSlope (show 0 ≤ r*F by positivity)
    have hgap : 0 < (12-12*r)*F^(2 : ℕ) := by
      have hc : 0 < 12-12*r := by linarith only [hr1]
      exact mul_pos hc hF2
    change F^(2 : ℕ) < 13*F^(2 : ℕ)+r*F*D
    nlinarith only [hm, hgap]
  · obtain ⟨τ, hτ, hqτ5, _, hs⟩ := exists_thetaCuspCompensationNeutralAnchor
    have hqτ : thetaCuspSingleAtomReflectionScale 1 (r/2) <
        thetaCuspSingleAtomReflectionScale 1 τ := by linarith
    have hx : r/2 < τ := by
      by_contra h
      have hm : thetaCuspSingleAtomReflectionScale 1 τ ≤
          thetaCuspSingleAtomReflectionScale 1 (r/2) := by
        unfold thetaCuspSingleAtomReflectionScale
        have he := Real.exp_le_exp.mpr (show 2*τ ≤ 2*(r/2) by linarith)
        simpa using mul_le_mul_of_nonneg_left he Real.pi_pos.le
      linarith only [hqτ, hm]
    have hG : 0 < thetaCuspCenterCompensationSource (r/2) :=
      (hs (r/2) (by positivity)).1.mpr hx
    have hF : 0 < thetaCuspFullSource (r/2)^(2 : ℕ) :=
      sq_pos_of_pos (thetaCuspFullSource_pos_all (r/2))
    unfold thetaCuspCenterCompensationSource at hG
    nlinarith only [hG, hF]

/-- The degree-twelve flux derivative dominates a positive weight throughout `q ≤ 8`. -/
theorem thetaCuspDegreeTwelve_flux_deriv_pos_le_eight {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r)
    (hq1 : thetaCuspSingleAtomReflectionScale 1 (r/2) ≤ 8) :
    r^(10 : ℕ) * (r*Real.sinh (a*r)) * thetaCuspFullSource (r/2)^(2 : ℕ) <
      deriv (thetaCuspPolynomialFlux 10 a) r := by
  have hsinh : 0 < Real.sinh (a*r) := Real.sinh_pos_iff.mpr (mul_pos ha hr)
  have hw : 0 < r*Real.sinh (a*r) := mul_pos hr hsinh
  have hr10 : 0 < r^(10 : ℕ) := pow_pos hr _
  have hsource := thetaCuspDegreeTwelve_source_reserve_le_eight hr hq1
  have hstrict := mul_lt_mul_of_pos_left hsource (mul_pos hr10 hw)
  have hK := deriv_thetaCuspCenterCompensationFlux_lower ha.le hr.le
  have hKm := mul_le_mul_of_nonneg_left hK hr10.le
  have hder : deriv (thetaCuspPolynomialFlux 10 a) r =
      10*r^(9 : ℕ)*thetaCuspCenterCompensationFlux a r +
        r^(10 : ℕ)*deriv (thetaCuspCenterCompensationFlux a) r := by
    have h := (((hasDerivAt_id r).pow 10).mul
      (hasDerivAt_thetaCuspCenterCompensationFlux a r)).deriv
    have hfun : (id ^ (10 : ℕ) * thetaCuspCenterCompensationFlux a) =
        thetaCuspPolynomialFlux 10 a := by
      funext x
      rfl
    rw [hfun] at h
    simpa [(hasDerivAt_thetaCuspCenterCompensationFlux a r).deriv] using h
  calc
    _ < r^(10 : ℕ)*(r*Real.sinh (a*r)) *
        (13*thetaCuspFullSource (r/2)^(2 : ℕ) +
          r*thetaCuspFullSource (r/2)*deriv thetaCuspFullSource (r/2)) := by
          nlinarith only [hstrict]
    _ ≤ deriv (thetaCuspPolynomialFlux 10 a) r := by
          rw [hder]
          dsimp [thetaCuspCenterCompensationFlux] at *
          nlinarith only [hKm]

end
end RHTower
