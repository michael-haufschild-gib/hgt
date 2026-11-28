import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.CoherentRay.Powers
import GaloisForLFunctions.HTGeometry.FirstOrderConnectionIntervalClassification
import GaloisForLFunctions.RHTower.XiSquaredSeamPowerSixtyFourMassCriterion

/-! # Phases of positive shares at a common logarithmic period -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.CoherentRay.TwoShells

theorem modulus (z : ℂ) (c : ℝ) : ‖power z c‖=Real.exp (z.re*Real.log c) := by
  simp only [power,Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]

theorem real_part {z : ℂ} (two : power z 2=2) : z.re=1 := by
  have H := congrArg norm two
  rw [modulus] at H
  have norm2 : ‖(2:ℂ)‖=(2:ℝ) := by norm_num
  rw [norm2] at H
  have same : Real.exp (z.re*Real.log 2)=Real.exp (1*Real.log 2) := by
    rw [H,one_mul,Real.exp_log (by norm_num : 0<(2:ℝ))]
  exact mul_right_cancel₀ (Real.log_pos (by norm_num : 1<(2:ℝ))).ne' (Real.exp_injective same)

/-- Saturation of the triangle inequality aligns each elementary branch
with its positive classical probability. -/
theorem aligned_shares {z : ℂ} {x y : ℝ} (hre : z.re=1) (hx : 0<x) (hy : 0<y)
    (sum : x+y=1) (read : power z x+power z y=1) :
    power z x=(x:ℂ) ∧ power z y=(y:ℂ) := by
  have size (c : ℝ) (hc : 0<c) : ‖power z c‖=c := by rw [modulus,hre,one_mul,Real.exp_log hc]
  have rx := Complex.re_le_norm (power z x)
  have ry := Complex.re_le_norm (power z y)
  rw [size x hx] at rx
  rw [size y hy] at ry
  have h := congrArg Complex.re read
  simp only [Complex.add_re,Complex.one_re] at h
  have eqn {c : ℝ} (hc : 0<c) (r : (power z c).re=c) : power z c=(c:ℂ) := by
    have zero : ‖power z c‖-(power z c).re=0 := by rw [size c hc,r,sub_self]
    exact Complex.ext r (RHTower.complex_nonnegativeReal_of_norm_sub_re_eq_zero zero).1
  exact ⟨eqn hx (by linarith only [h,rx,ry,sum]),eqn hy (by linarith only [h,rx,ry,sum])⟩

private theorem split_phase {z : ℂ} (hre : z.re=1) {c : ℝ} (hc : 0<c) :
    power z c=(c:ℂ)*Complex.exp (((z.im*Real.log c:ℝ):ℂ)*Complex.I) := by
  have form : z=(1:ℂ)+(z.im:ℂ)*Complex.I := by apply Complex.ext <;> simp [hre]
  calc
    power z c = power (1+(z.im:ℂ)*Complex.I) c := congrArg (fun w => power w c) form
    _ = _ := by
      rw [power_add,power_at_one hc,power,Complex.ofReal_mul]
      congr 2
      ring

/-- A positive value has trivial phase exactly when its log times the
imaginary parameter is an integral number of turns. -/
theorem locked_iff {z : ℂ} (hre : z.re=1) {c : ℝ} (hc : 0<c) :
    power z c=(c:ℂ) ↔ ∃ k : ℤ, z.im*Real.log c=2*Real.pi*(k:ℝ) := by
  have rotation := HTGeometry.exp_real_mul_I_eq_exp_real_mul_I_iff (z.im*Real.log c) 0
  simp only [Complex.ofReal_zero,zero_mul,Complex.exp_zero,zero_add] at rotation
  rw [split_phase hre hc]
  constructor
  · intro h
    exact rotation.mp (mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hc.ne') (h.trans (mul_one _).symm))
  · intro h
    rw [rotation.mpr h,mul_one]

def radius (z : ℂ) := Real.exp (2*Real.pi/|z.im|)

theorem locked_is_power {z : ℂ} (hre : z.re=1) (ht : z.im≠0) {c : ℝ} (hc : 1<c)
    (fixed : power z c=(c:ℂ)) : ∃ j : ℕ, 0<j ∧ radius z^j=c := by
  obtain ⟨k,hk⟩ := (locked_iff hre (lt_trans zero_lt_one hc)).mp fixed
  have cast : (k.natAbs:ℝ)=|(k:ℝ)| := by
    simpa only [Int.cast_natCast,Int.cast_abs] using congrArg (fun a : ℤ => (a:ℝ)) (Int.natCast_natAbs k)
  have length : |z.im| * Real.log c=(2*Real.pi)*(k.natAbs:ℝ) := by
    calc
      _ = |z.im*Real.log c| := by rw [abs_mul,abs_of_pos (Real.log_pos hc)]
      _ = |2*Real.pi*(k:ℝ)| := congrArg abs hk
      _ = _ := by rw [abs_mul,abs_of_pos (mul_pos (by norm_num) Real.pi_pos),cast]
  have dist : (k.natAbs:ℝ)*(2*Real.pi/|z.im|)=Real.log c := by
    rw [←mul_div_assoc]
    apply (div_eq_iff (abs_ne_zero.mpr ht)).mpr
    linarith only [length]
  have H : radius z^k.natAbs=c := by
    rw [radius,←Real.exp_nat_mul,dist,Real.exp_log (lt_trans zero_lt_one hc)]
  refine ⟨k.natAbs,Nat.pos_of_ne_zero (fun zero => ?_),H⟩
  rw [zero,pow_zero] at H
  exact hc.ne H

#print axioms real_part
#print axioms aligned_shares
#print axioms locked_iff
#print axioms locked_is_power

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.CoherentRay.TwoShells
