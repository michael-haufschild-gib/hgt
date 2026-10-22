import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCausalRiemannKernel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The original complex-degree Riemann kernel has an exact spin-two double primitive.
No spectral factor is divided out. These kernel identities do not replace the full angular
source by an eigenfunction or assert cancellation of the physical Einstein current. -/
namespace RHTower.D4BMSpinTwoKernel
open D4BMCausalKernel Complex Set MeasureTheory
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

def degree (nu : ℂ) : ℂ := nu*(nu+1)
def primitive (nu : ℂ) (z : ℝ) : ℂ :=
  ((z:ℂ)^(2 : ℕ)-1)*(degree nu*legendreKernel nu z-2*z*legendreKernelFirst nu z)
def primitiveFirst (nu : ℂ) (z : ℝ) : ℂ :=
  ((z:ℂ)^(2 : ℕ)-1)*(degree nu-2)*legendreKernelFirst nu z

/-- The displayed primitive and its first jet are actual derivatives of the original kernel. -/
theorem primitive_derivatives (nu : ℂ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (primitive nu) (primitiveFirst nu z) z ∧
    HasDerivAt (primitiveFirst nu)
      (degree nu*(degree nu-2)*legendreKernel nu z) z := by
  obtain ⟨h0,h1⟩ := legendreKernel_derivatives nu hz
  have hx := (hasDerivAt_id z).ofReal_comp
  have hp := (hx.pow 2).sub_const (1:ℂ)
  have he := legendreKernel_equation nu hz
  change ((z:ℂ)^(2 : ℕ)-1)*legendreKernelSecond nu z+2*z*legendreKernelFirst nu z-
    degree nu*legendreKernel nu z=0 at he
  constructor
  · apply (hp.mul ((h0.const_mul (degree nu)).sub
      (((hx.const_mul (2:ℂ)).mul h1)))).congr_deriv
    dsimp [primitiveFirst]
    linear_combination -2*(z:ℂ)*he
  · apply ((hp.mul_const (degree nu-2)).mul h1).congr_deriv
    simp only [Pi.pow_apply,id_eq,Complex.ofReal_one]
    linear_combination (degree nu-2)*he

/-- The same primitive is the second kernel derivative times a double characteristic zero. -/
theorem primitive_eq_weighted_second (nu : ℂ) {z : ℝ} (hz : 0 < z) :
    primitive nu z=((z:ℂ)^(2 : ℕ)-1)^(2 : ℕ)*legendreKernelSecond nu z := by
  have he := legendreKernel_equation nu hz
  dsimp [primitive,degree]
  linear_combination -((z:ℂ)^(2 : ℕ)-1)*he

/-- Both boundary jets vanish for every complex degree, including the exceptional degrees. -/
theorem primitive_characteristic (nu : ℂ) :
    primitive nu 1=0 ∧ primitiveFirst nu 1=0 := by
  simp [primitive,primitiveFirst]

/-- The first primitive jet is the integral of the complete spin-two kernel weight. -/
theorem primitiveFirst_integral (nu : ℂ) {z : ℝ} (hz : 1 ≤ z) :
    primitiveFirst nu z=degree nu*(degree nu-2)*
      ∫ r in (1:ℝ)..z, legendreKernel nu r := by
  have hcont : ContinuousOn (legendreKernel nu) (uIcc (1:ℝ) z) := by
    rw [uIcc_of_le hz]
    intro r hr
    exact (legendreKernel_derivatives nu (by linarith [hr.1])).1.continuousAt.continuousWithinAt
  have hi := hcont.intervalIntegrable (μ := volume)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r hr => (primitive_derivatives nu (show 0 < r by
      rw [uIcc_of_le hz] at hr
      linarith [hr.1])).2)
    (hi.const_mul (degree nu*(degree nu-2)))
  rw [intervalIntegral.integral_const_mul,(primitive_characteristic nu).2,sub_zero] at he
  exact he.symm

/-- An exact Volterra formula retains the kernel on the full interval and both zero boundary jets. -/
theorem primitive_volterra (nu : ℂ) {z : ℝ} (hz : 1 ≤ z) :
    primitive nu z=degree nu*(degree nu-2)*
      ∫ r in (1:ℝ)..z, ((z:ℂ)-(r:ℂ))*legendreKernel nu r := by
  let f : ℝ → ℂ := fun r => primitive nu r+((z:ℂ)-(r:ℂ))*primitiveFirst nu r
  have hd (r : ℝ) (hr : r ∈ uIcc (1:ℝ) z) :
      HasDerivAt f (degree nu*(degree nu-2)*(((z:ℂ)-(r:ℂ))*legendreKernel nu r)) r := by
    have hr0 : 0 < r := by
      rw [uIcc_of_le hz] at hr
      linarith [hr.1]
    obtain ⟨h0,h1⟩ := primitive_derivatives nu hr0
    apply (h0.add ((((hasDerivAt_id r).ofReal_comp).const_sub (z:ℂ)).mul h1)).congr_deriv
    simp only [id_eq,Complex.ofReal_one]
    ring
  have hc : ContinuousOn (fun r : ℝ => ((z:ℂ)-(r:ℂ))*legendreKernel nu r)
      (uIcc (1:ℝ) z) := by
    rw [uIcc_of_le hz]
    intro r hr
    have h0 := (legendreKernel_derivatives nu (show 0 < r by linarith [hr.1])).1
    exact ((((hasDerivAt_id r).ofReal_comp).const_sub (z:ℂ)).mul h0).continuousAt.continuousWithinAt
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((hc.intervalIntegrable (μ := volume)).const_mul (degree nu*(degree nu-2)))
  rw [intervalIntegral.integral_const_mul] at he
  simpa only [f,sub_self,zero_mul,add_zero,(primitive_characteristic nu).1,
    (primitive_characteristic nu).2,mul_zero,zero_add,sub_zero] using he.symm

end
end RHTower.D4BMSpinTwoKernel
