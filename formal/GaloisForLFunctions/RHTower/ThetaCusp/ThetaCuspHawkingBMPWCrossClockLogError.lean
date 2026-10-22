import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPWCrossClockLogIdentity

/-! The native cross-error remains integrable after exact log-height normalization. -/

open Complex MeasureTheory Set Filter Topology
open RHTower RHTower.D4BMPWCrossClockMeanEquation
open RHTower.D4BMPWCrossClockMeanError RHTower.D4BMPWCrossClockActualError
open RHTower.D4BMPWCrossClockLogIdentity
noncomputable section
set_option autoImplicit false

namespace RHTower.D4BMPWCrossClockLogError

private def errorMul (q : XiZeroCopy) (y : ℝ) : ℂ :=
  ((y ^ (beta q + 1):ℝ):ℂ) * (y:ℂ)^(-rate q)

private theorem errorMul_continuousOn (q : XiZeroCopy) :
    ContinuousOn (errorMul q) (Ioi (3:ℝ)) := by
  intro y hy
  have hy0 : 0 < y := lt_trans (by norm_num : (0:ℝ) < 3) hy
  have hreal : ContinuousAt (fun z : ℝ => ((z ^ (beta q + 1):ℝ):ℂ)) y :=
    Complex.continuous_ofReal.continuousAt.comp
      (Real.continuousAt_rpow_const y _ (Or.inl hy0.ne'))
  have hcomplex : ContinuousAt (fun z : ℝ => (z:ℂ)^(-rate q)) y :=
    (continuousAt_cpow_const
      (Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using hy0)))).comp
      Complex.continuous_ofReal.continuousAt
  exact (hreal.mul hcomplex).continuousWithinAt

private theorem errorMul_bound (q : XiZeroCopy)
    (hleft : (q.1:ℂ).re < 1/2) {y : ℝ} (hy : 3 < y) :
    ‖errorMul q y‖ ≤ 1 := by
  have hy0 : 0 < y := by linarith
  have hy1 : 1 ≤ y := by linarith
  have hr : (rate q).re = 2 * beta q := by
    change (2*(2-2*(q.1:ℂ))).re = 2*(2-2*(q.1:ℂ)).re
    norm_num [Complex.mul_re,Complex.sub_re]
  have hb := beta_gt_one q hleft
  calc
    ‖errorMul q y‖ = y ^ (1-beta q) := by
      rw [errorMul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos hy0 _),
        Complex.norm_cpow_eq_rpow_re_of_pos hy0]
      rw [Complex.neg_re,hr,← Real.rpow_add hy0]
      congr 1
      ring
    _ ≤ y ^ (0:ℝ) := Real.rpow_le_rpow_of_exponent_le hy1 (by linarith)
    _ = 1 := Real.rpow_zero _

private theorem errorMul_identity (q : XiZeroCopy) {y : ℝ} (hy : 3 < y) :
    errorMul q y *
      (((y ^ (-beta q):ℝ):ℂ) * (crossMean q y - principalCross q y) /
        (y:ℂ)^(2:ℕ)) =
      (y:ℂ)^(-rate q) * (crossMean q y-principalCross q y)/(y:ℂ) := by
  have hy0 : 0 < y := by linarith
  have hyne : (y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy0.ne'
  have hp : ((y ^ (beta q + 1):ℝ):ℂ) * ((y ^ (-beta q):ℝ):ℂ) = (y:ℂ) := by
    rw [← Complex.ofReal_mul,← Real.rpow_add hy0,
      show beta q + 1 + -beta q = 1 by ring, Real.rpow_one]
  unfold errorMul
  calc
    _ = (((y ^ (beta q + 1):ℝ):ℂ) * ((y ^ (-beta q):ℝ):ℂ)) *
        (y:ℂ)^(-rate q) * (crossMean q y-principalCross q y) / (y:ℂ)^2 := by ring
    _ = _ := by rw [hp]; field_simp

private theorem weighted_error_log_input (q : XiZeroCopy)
    (hleft : (q.1:ℂ).re < 1/2) :
    IntegrableOn (fun y : ℝ =>
      (y:ℂ)^(-rate q) * (crossMean q y-principalCross q y)/(y:ℂ)) (Ioi (3:ℝ)) := by
  have hi := actual_cross_mean_error_density_integrable q hleft
  have hm : AEStronglyMeasurable (errorMul q) (volume.restrict (Ioi (3:ℝ))) :=
    (errorMul_continuousOn q).aestronglyMeasurable measurableSet_Ioi
  have hprod : IntegrableOn (fun y : ℝ =>
      (((y ^ (-beta q):ℝ):ℂ) * (crossMean q y - principalCross q y) /
        (y:ℂ)^(2:ℕ)) * errorMul q y) (Ioi (3:ℝ)) := by
    exact hi.mul_bdd (c := 1) hm
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun y hy => errorMul_bound q hleft hy))
  apply hprod.congr_fun
  · intro y hy
    change (((y ^ (-beta q):ℝ):ℂ) * (crossMean q y - principalCross q y) /
      (y:ℂ)^(2:ℕ)) * errorMul q y =
      (y:ℂ)^(-rate q) * (crossMean q y-principalCross q y)/(y:ℂ)
    rw [mul_comm]
    exact errorMul_identity q hy
  · exact measurableSet_Ioi

/-- The actual full-product correction is `L¹` after the double reflected
power is divided out in logarithmic cusp height. No pointwise remainder
bound or extra response regularity is assumed. -/
theorem actual_normalized_error_integrable (q : XiZeroCopy)
    (hleft : (q.1:ℂ).re < 1/2) :
    IntegrableOn (fun t : ℝ => Complex.exp (-rate q*(t:ℂ)) *
      (crossMean q (Real.exp t)-principalCross q (Real.exp t)))
      (Ioi (Real.log 3)) := by
  let f : ℝ → ℂ := fun y =>
    (y:ℂ)^(-rate q) * (crossMean q y-principalCross q y)/(y:ℂ)
  have hchange := integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi
    (fun t (_ : t ∈ Ioi (Real.log 3)) =>
      (Real.hasDerivAt_exp t).hasDerivWithinAt)
    Real.exp_injective.injOn f
  rw [Real.image_exp_Ioi,Real.exp_log (by norm_num : (0:ℝ)<3)] at hchange
  have hi : IntegrableOn (fun t : ℝ => Real.exp t • f (Real.exp t))
      (Ioi (Real.log 3)) := by
    simpa only [abs_of_pos (Real.exp_pos _)] using
      hchange.mp (weighted_error_log_input q hleft)
  apply hi.congr_fun
  · intro t _
    have hy : (Real.exp t:ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne'
    dsimp [f]
    have hc : (Real.exp t:ℂ)^(-rate q) =
        Complex.exp (-rate q*(t:ℂ)) := by
      rw [GaloisForLFunctions.HTGeometry.ofReal_cpow_eq_exp (Real.exp_pos t),
        Real.log_exp]
      congr 1
      ring
    rw [hc]
    field_simp
  · exact measurableSet_Ioi

end RHTower.D4BMPWCrossClockLogError
