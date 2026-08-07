import GaloisForLFunctions.RHTower.FractionalPartZeta
import GaloisForLFunctions.RHTower.BurnolCoPoissonBerezinFaithful
import Mathlib.Analysis.Fourier.Inversion

/-!
# The fractional-part carrier of the critical line

The function `phi y = frac (exp y) * exp (-y/2)` is the logarithmic carrier of the fractional-part
Mellin identity: after the substitution `x = exp y` its Fourier transform along the critical line
is `-zeta w / w`.  This module builds the carrier, records the substitution identity that turns a
Mellin integrand on the ray into the carrier on the line, and proves that the carrier is both
integrable and square integrable.
-/

open Complex Real MeasureTheory Set Filter Topology FourierTransform FourierTransformInv

noncomputable section

namespace RHTower

/-- Logarithmic carrier of the fractional part. -/
def fractLogCarrier (y : ℝ) : ℂ :=
  ((Int.fract (Real.exp y) : ℝ) : ℂ) * ((Real.exp (-(y / 2)) : ℝ) : ℂ)

theorem exp_mul_rpow_neg_three_halves (y : ℝ) :
    Real.exp y * Real.exp y ^ (-(3 / 2 : ℝ)) = Real.exp (-(y / 2)) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos y), Real.log_exp, ← Real.exp_add]
  congr 1
  ring

/-- The carrier is the logarithmic substitution of the Mellin integrand at the critical abscissa
`3/2` of the fractional part. -/
theorem fractLogCarrier_eq_exp_smul (y : ℝ) :
    fractLogCarrier y =
      Real.exp y • (((Int.fract (Real.exp y) : ℝ) : ℂ) *
        ((Real.exp y ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)) := by
  rw [fractLogCarrier, Complex.real_smul, ← exp_mul_rpow_neg_three_halves y]
  push_cast
  ring

/-- Square modulus of the carrier is the logarithmic substitution of the squared Mellin
integrand. -/
theorem norm_sq_fractLogCarrier_eq_exp_smul (y : ℝ) :
    ‖fractLogCarrier y‖ ^ 2 =
      Real.exp y • (Int.fract (Real.exp y) ^ 2 * Real.exp y ^ (-(2 : ℝ))) := by
  have hpos : (0 : ℝ) < Real.exp y := Real.exp_pos y
  have hfr : 0 ≤ Int.fract (Real.exp y) := Int.fract_nonneg _
  have hreal : Real.exp y * Real.exp y ^ (-(2 : ℝ)) = Real.exp (-(y / 2)) ^ 2 := by
    rw [Real.rpow_def_of_pos hpos, Real.log_exp, ← Real.exp_add, ← Real.exp_nat_mul]
    congr 1
    ring
  rw [fractLogCarrier, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg hfr, abs_of_nonneg (Real.exp_pos _).le, mul_pow,
    smul_eq_mul, ← mul_assoc, mul_comm (Real.exp y), mul_assoc, hreal]


/-- **The carrier is integrable.**  Its logarithmic substitution is the Mellin integrand of the
fractional part at abscissa `1/2`, which the corpus already knows to be integrable on the ray. -/
theorem integrable_fractLogCarrier : Integrable fractLogCarrier volume := by
  have hbase : IntegrableOn
      (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(((1 : ℂ) / 2) + 1))) (Ioi 0) :=
    integrableOn_Ioi_zero_fract_cpow (by norm_num) (by norm_num)
  rw [integrableOn_Ioi_iff_integrable_exp_smul] at hbase
  refine (integrable_congr ?_).mp hbase
  filter_upwards with t
  rw [fractLogCarrier_eq_exp_smul]
  congr 2
  rw [show (-(((1 : ℂ) / 2) + 1)) = (((-(3 / 2 : ℝ)) : ℝ) : ℂ) by norm_num,
    ← Complex.ofReal_cpow (Real.exp_pos t).le]


/-! ## The Fourier transform of the carrier -/

/-- The critical abscissa attached to a Fourier frequency. -/
def criticalAbscissa (xi : ℝ) : ℂ := 1 / 2 + ((2 * Real.pi * xi : ℝ) : ℂ) * Complex.I

@[simp] theorem criticalAbscissa_re (xi : ℝ) : (criticalAbscissa xi).re = 1 / 2 := by
  simp [criticalAbscissa]

@[simp] theorem criticalAbscissa_im (xi : ℝ) : (criticalAbscissa xi).im = 2 * Real.pi * xi := by
  simp [criticalAbscissa]

theorem criticalAbscissa_ne_zero (xi : ℝ) : criticalAbscissa xi ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [criticalAbscissa_re] at this
  norm_num at this

theorem continuous_criticalAbscissa : Continuous criticalAbscissa := by
  unfold criticalAbscissa
  fun_prop

/-- **The Fourier transform of the fractional-part carrier.**  It is the completed Mellin quotient
`- zeta w / w` read along the critical line. -/
theorem fourier_fractLogCarrier (xi : ℝ) :
    𝓕 fractLogCarrier xi = -(riemannZeta (criticalAbscissa xi) / criticalAbscissa xi) := by
  have hw0 : 0 < (criticalAbscissa xi).re := by rw [criticalAbscissa_re]; norm_num
  have hw1 : (criticalAbscissa xi).re < 1 := by rw [criticalAbscissa_re]; norm_num
  rw [Real.fourier_eq, ← integral_Ioi_zero_fract_cpow hw0 hw1,
    integral_Ioi_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with t
  have hpos : (0 : ℝ) < Real.exp t := Real.exp_pos t
  have hne : ((Real.exp t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hpos
  have hlog : Complex.log ((Real.exp t : ℝ) : ℂ) = (t : ℂ) := by
    rw [Complex.log_ofReal_of_pos hpos, Real.log_exp]
  have hcpow : ((Real.exp t : ℝ) : ℂ) ^ (-(criticalAbscissa xi + 1)) =
      Complex.exp ((t : ℂ) * (-(criticalAbscissa xi + 1))) := by
    rw [Complex.cpow_def_of_ne_zero hne, hlog]
  rw [hcpow, Circle.smul_def, Real.fourierChar_apply, fractLogCarrier, Complex.real_smul]
  have hsplit : Complex.exp ((t : ℂ) * (-(criticalAbscissa xi + 1))) =
      Complex.exp (-(t : ℂ)) * (((Real.exp (-(t / 2)) : ℝ) : ℂ) *
        Complex.exp (((2 * Real.pi * -(t * xi) : ℝ) : ℂ) * Complex.I)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [criticalAbscissa]
    push_cast
    ring
  rw [hsplit]
  have hexpt : ((Real.exp t : ℝ) : ℂ) = Complex.exp (t : ℂ) := by
    rw [Complex.ofReal_exp]
  rw [hexpt, ← mul_assoc, ← mul_assoc]
  rw [show Complex.exp (t : ℂ) * (((Int.fract (Real.exp t) : ℝ) : ℂ) * Complex.exp (-(t : ℂ))) *
      (((Real.exp (-(t / 2)) : ℝ) : ℂ) *
        Complex.exp (((2 * Real.pi * -(t * xi) : ℝ) : ℂ) * Complex.I)) =
      (Complex.exp (t : ℂ) * Complex.exp (-(t : ℂ))) *
        (Complex.exp (((2 * Real.pi * -(t * xi) : ℝ) : ℂ) * Complex.I) *
          (((Int.fract (Real.exp t) : ℝ) : ℂ) * ((Real.exp (-(t / 2)) : ℝ) : ℂ))) by ring]
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
  congr 2
  norm_num

/-! ## The reciprocal abscissa is square integrable -/

theorem memLp_inv_criticalAbscissa :
    MemLp (fun xi : ℝ => (criticalAbscissa xi)⁻¹) 2 volume := by
  have hmeas : AEStronglyMeasurable (fun xi : ℝ => (criticalAbscissa xi)⁻¹) volume := by
    refine (Continuous.aestronglyMeasurable ?_)
    exact continuous_criticalAbscissa.inv₀ criticalAbscissa_ne_zero
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hbound : Integrable (fun xi : ℝ => 4 * (1 + xi ^ 2)⁻¹) volume :=
    (integrable_inv_one_add_sq).const_mul 4
  refine Integrable.mono' hbound (hmeas.norm.pow 2) ?_
  filter_upwards with xi
  have hnormsq : ‖criticalAbscissa xi‖ ^ 2 = 1 / 4 + (2 * Real.pi * xi) ^ 2 := by
    rw [Complex.sq_abs] at *
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, criticalAbscissa_re,
      criticalAbscissa_im]
    ring
  have hpos : (0 : ℝ) < ‖criticalAbscissa xi‖ :=
    norm_pos_iff.mpr (criticalAbscissa_ne_zero xi)
  have hpi : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := by
    nlinarith [Real.pi_gt_three]
  have hlower : (1 / 4) * (1 + xi ^ 2) ≤ ‖criticalAbscissa xi‖ ^ 2 := by
    rw [hnormsq]
    nlinarith [sq_nonneg xi, hpi]
  have hinvsq : ‖(criticalAbscissa xi)⁻¹‖ ^ 2 = (‖criticalAbscissa xi‖ ^ 2)⁻¹ := by
    rw [norm_inv, inv_pow]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hinvsq]
  have hposadd : (0 : ℝ) < 1 + xi ^ 2 := by positivity
  rw [inv_le_iff_one_le_mul₀ (by positivity)]
  have : (0:ℝ) < ‖criticalAbscissa xi‖ ^ 2 := by positivity
  rw [ge_iff_le, ← div_le_iff₀ this] at *
  nlinarith [hlower, hposadd]

end RHTower
