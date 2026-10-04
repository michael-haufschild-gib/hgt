import GaloisForLFunctions.RHTower.ThetaCuspRatioZeroSpeedFaceSign
import GaloisForLFunctions.RHTower.ThetaCuspRatioIntegerIncidence
/-! # Positive third source slope on the entire zero-speed face

For positive drift and k ≥ 5/4, the source slope is strictly positive
where J=0 and J′=0. No kinetic upper bound is needed. Positivity in the
interior of the strengthened source cone remains open. -/

namespace HTGeometry.ThetaRatioSource
noncomputable section
open MvPolynomial

/-- The whole positive-drift, zero-defect, zero-speed face has positive source slope. -/
theorem thirdSlope_zeroSpeed_pos {u k : ℝ} (hu : 0<u) (hk : 5/4≤k)
    (hf : k^2*(9-u^2)-6*k-4=0) :
    0 < (eval (slicePoint (u:ℂ) (k:ℂ)) thirdSlope).re := by
  have hkp : 0<k := by linarith only [hk]
  have hkc : (k:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hkp.ne'
  have hkt : 0<k^2*(9-u^2) := by linarith only [hf,hkp]
  have ht : 0<9-u^2 :=
    (mul_pos_iff_of_pos_left (by positivity : (0:ℝ)<k^2)).mp hkt
  have huR : u^2=9-6/k-4/k^2 := by
    field_simp [hkp.ne']
    linear_combination -hf
  have huC : (u:ℂ)^2=9-6/(k:ℂ)-4/(k:ℂ)^2 := by exact_mod_cast huR
  have hfC : (k:ℂ)^2*(9-(u:ℂ)^2)-6*(k:ℂ)-4=0 := by exact_mod_cast hf
  have hpartial := zeroSpeedMinorPartial_eq (k:ℂ) hkc
  rw [← huC,← zeroSpeedFacePolynomial_eq k hkc] at hpartial
  have hi := thirdSlope_zeroSpeed_slice (u:ℂ) (k:ℂ) hfC
  have he : ((k^18*(6:ℝ)^26:ℝ):ℂ)*eval (slicePoint (u:ℂ) (k:ℂ)) thirdSlope =
      ((2*u*(6*k-1)*(6*k*(9-u^2))*zeroSpeedFacePolynomial k:ℝ):ℂ) := by
    calc
      _ = (k:ℂ)^18*eval (slicePoint (u:ℂ) (k:ℂ)) integerThirdSlope := by
        rw [integerThirdSlope_eq,map_mul,eval_C]
        push_cast
        ring
      _ = (2*(u:ℂ)*(6*(k:ℂ)-1)*(6*(k:ℂ)*(9-(u:ℂ)^2)))*
          ((k:ℂ)^18*eval (slicePoint ((u:ℂ)^2) (k:ℂ))
            (pderiv Coord.U zeroDefectMinor)) := by rw [hi]; ring
      _ = (2*(u:ℂ)*(6*(k:ℂ)-1)*(6*(k:ℂ)*(9-(u:ℂ)^2)))*
          (zeroSpeedFacePolynomial k:ℂ) := by rw [hpartial]
      _ = _ := by push_cast; ring
  have hr := congrArg Complex.re he
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hr
  have hs : 0<6*k-1 := by linarith only [hk]
  have hp := zeroSpeedFacePolynomial_pos hk
  have hpos : 0<2*u*(6*k-1)*(6*k*(9-u^2))*zeroSpeedFacePolynomial k := by positivity
  rw [← hr] at hpos
  exact (mul_pos_iff_of_pos_left (by positivity : (0:ℝ)<k^18*(6:ℝ)^26)).mp hpos

end
end HTGeometry.ThetaRatioSource
