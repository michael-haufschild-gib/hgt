import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Envelope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! # Real reciprocal amplitudes of a character and its square -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature

open Real Filter
open scoped Topology

def amplitude (w : ℂ) := (w-w⁻¹).re

def joint (w : ℂ) := max |amplitude w| (|amplitude (w^2)|/2)

/-- A single real quadrature loses the radial displacement at every
quarter period. -/
theorem first (z : ℂ) : amplitude (Complex.exp z)=2*sinh z.re*cos z.im := by
  rw [amplitude,←Complex.exp_neg,Complex.sub_re,Complex.exp_re,Complex.exp_re,
    Complex.neg_re,Complex.neg_im,cos_neg,sinh_eq]
  ring

/-- Squaring the character doubles both displacement and phase. Its
real quadrature supplies the second cosine of the phase envelope. -/
theorem joint_factor (z : ℂ) :
    joint (Complex.exp z)=2*|sinh z.re| * phaseGain (cosh z.re) z.im := by
  have twice : (Complex.exp z)^2=Complex.exp (z+z) := by rw [sq,Complex.exp_add]
  have cp := cosh_pos z.re
  have a : |2*sinh z.re*cos z.im|=2*|sinh z.re| * |cos z.im| := by
    simp only [abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2)]
  have b : |2*sinh (2*z.re)*cos (2*z.im)|/2=
      (2*|sinh z.re|)*(cosh z.re*|cos (2*z.im)|) := by
    rw [sinh_two_mul]
    simp only [abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2),abs_of_pos cp]
    ring
  rw [joint,first,twice,first,Complex.add_re,Complex.add_im,←two_mul,←two_mul,a,b,
    phaseGain,mul_max_of_nonneg _ _ (mul_nonneg (by norm_num) (abs_nonneg _))]

theorem joint_lower (z : ℂ) : |sinh z.re|≤joint (Complex.exp z) := by
  rw [joint_factor]
  have low := (radius_bounds (one_le_cosh z.re)).1.trans ((sharp_phase (one_le_cosh z.re) z.im).1)
  nlinarith only [mul_le_mul_of_nonneg_left low (abs_nonneg (sinh z.re))]

/-- The joint real reading vanishes exactly on the imaginary axis of
the centered energy parameter. -/
theorem joint_zero (z : ℂ) : joint (Complex.exp z)=0 ↔ z.re=0 := by
  constructor
  · intro hz
    have h := joint_lower z
    rw [hz] at h
    exact sinh_eq_zero.mp (abs_nonpos_iff.mp h)
  · intro hz
    simp only [joint_factor,hz,sinh_zero,abs_zero,mul_zero,zero_mul]

/-- At fixed nonzero radial displacement the crossing of the two
quadratures gives every minimizing phase. -/
theorem joint_equality (z : ℂ) (hx : z.re≠0) :
    joint (Complex.exp z)=2*|sinh z.re| * radius (cosh z.re) ↔
      |cos z.im|=radius (cosh z.re) := by
  rw [joint_factor,mul_right_inj' (mul_ne_zero (by norm_num) (abs_ne_zero.mpr (fun h => hx (sinh_eq_zero.mp h))))]
  exact (sharp_phase (one_le_cosh _) _).2

/-- The universal envelope constant one half stays optimal when damping
zero is excluded. The phase pi/3 approaches equality as damping vanishes. -/
theorem uniform_constant (K : ℝ) :
    (∀ x y : ℝ, x≠0 → K≤phaseGain (cosh x) y) ↔ K≤1/2 := by
  constructor
  · intro h
    have third (x : ℝ) : phaseGain (cosh x) (π/3)=cosh x/2 := by
      rw [phaseGain,cos_two_mul,cos_pi_div_three]
      norm_num
      ring
    have bound : ∀ᶠ x : ℝ in 𝓝[≠] 0, K≤cosh x/2 := by
      filter_upwards [show ∀ᶠ x : ℝ in 𝓝[≠] 0, x≠0 from self_mem_nhdsWithin] with x hx
      simpa only [third] using h x (π/3) hx
    have lim : Tendsto (fun x : ℝ => cosh x/2) (𝓝[≠] 0) (𝓝 (1/2)) := by
      simpa only [cosh_zero] using
        (show Tendsto cosh (𝓝[≠] 0) (𝓝 (cosh 0)) from continuous_cosh.continuousAt.continuousWithinAt.tendsto).div_const 2
    exact le_of_tendsto_of_tendsto tendsto_const_nhds lim bound
  · exact fun h x y _ => h.trans ((radius_bounds (one_le_cosh x)).1.trans (sharp_phase (one_le_cosh x) y).1)

#print axioms first
#print axioms joint_factor
#print axioms joint_lower
#print axioms joint_zero
#print axioms joint_equality
#print axioms uniform_constant

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature
