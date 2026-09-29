import GaloisForLFunctions.RHTower.ThetaMovingShellBoundaryLayer

/-! # Exact rational profile and its sharp first-Laguerre sign boundary -/

open Real Complex

namespace RHTower
noncomputable section

def thetaMovingShellJetLimit (k : ℕ) (lambda : ℝ) : ℂ :=
  ((2 * Real.pi^2 : ℝ) : ℂ) * (Complex.I / 2)^k *
    ((k.factorial : ℂ) / ((Real.pi : ℂ) - Complex.I * (lambda : ℂ) / 2)^(k+1))

private theorem normSq_fourierDen (lambda : ℝ) :
    Complex.normSq ((Real.pi : ℂ)-Complex.I*(lambda : ℂ)/2) =
      (4*Real.pi^2+lambda^2)/4 := by
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem thetaMovingShellJetLimit_re_zero (lambda : ℝ) :
    (thetaMovingShellJetLimit 0 lambda).re = 8*Real.pi^3/(4*Real.pi^2+lambda^2) := by
  have hp := Real.pi_pos
  have hd : 4*Real.pi^2+lambda^2 ≠ 0 := ne_of_gt (by positivity)
  simp only [thetaMovingShellJetLimit, pow_zero, zero_add, pow_one, Nat.factorial_zero,
    Nat.cast_one, mul_one, mul_div_assoc]
  rw [Complex.div_re]
  rw [normSq_fourierDen]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero,
    one_mul, sub_zero, Complex.div_ofNat_re, Complex.div_ofNat_im]
  field_simp [hd]
  <;> ring

theorem thetaMovingShellJetLimit_re_one (lambda : ℝ) :
    (thetaMovingShellJetLimit 1 lambda).re =
      -16*Real.pi^3*lambda/(4*Real.pi^2+lambda^2)^2 := by
  have hp := Real.pi_pos
  have hd : 4*Real.pi^2+lambda^2 ≠ 0 := ne_of_gt (by positivity)
  simp only [thetaMovingShellJetLimit, pow_one, Nat.factorial_one, Nat.cast_one,
    mul_div_assoc, ← mul_assoc]
  rw [Complex.div_re]
  simp [map_pow, normSq_fourierDen, Complex.mul_re, Complex.mul_im, pow_succ,
    Complex.div_ofNat_re, Complex.div_ofNat_im]
  field_simp [hd]
  <;> ring

theorem thetaMovingShellJetLimit_re_two (lambda : ℝ) :
    (thetaMovingShellJetLimit 2 lambda).re =
      16*Real.pi^3*(3*lambda^2-4*Real.pi^2)/(4*Real.pi^2+lambda^2)^3 := by
  have hp := Real.pi_pos
  have hd : 4*Real.pi^2+lambda^2 ≠ 0 := ne_of_gt (by positivity)
  simp only [thetaMovingShellJetLimit, Nat.factorial_succ, Nat.factorial_one,
    Nat.cast_mul, Nat.cast_one, mul_one, mul_div_assoc, ← mul_assoc]
  rw [Complex.div_re]
  simp [map_pow, normSq_fourierDen, Complex.mul_re, Complex.mul_im, pow_succ,
    Complex.div_ofNat_re, Complex.div_ofNat_im]
  field_simp [hd]
  <;> ring

theorem thetaMovingShellJetLimit_firstLaguerre (lambda : ℝ) :
    (thetaMovingShellJetLimit 1 lambda).re^2 -
      (thetaMovingShellJetLimit 0 lambda).re * (thetaMovingShellJetLimit 2 lambda).re =
        128*Real.pi^6*(4*Real.pi^2-lambda^2)/(4*Real.pi^2+lambda^2)^4 := by
  rw [thetaMovingShellJetLimit_re_zero, thetaMovingShellJetLimit_re_one,
    thetaMovingShellJetLimit_re_two]
  have hp := Real.pi_pos
  have hd : 4*Real.pi^2+lambda^2 ≠ 0 := ne_of_gt (by positivity)
  field_simp [hd]
  <;> ring

end
end RHTower
