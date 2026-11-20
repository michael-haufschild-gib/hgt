import GaloisForLFunctions.ExceptionalLayerTheory.ThePolynomialWeightsOfTheXiDivisor
import GaloisForLFunctions.ConjugateDiagonalGeometry.NewtonDifferencePolynomial

/-!
# Complex moments from four real area measurements

Opposite constant offsets polarize a squared polynomial reading.
Real and imaginary offsets recover the two components of every complex
power sum of the actual divisor using the same observation disk.
-/
noncomputable section
open Complex Filter MeasureTheory Metric Set Topology RHTower Polynomial
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Polarization of the planar norm in a chosen complex direction. -/
private theorem polarized_norm (x y : ℂ) :
    ‖x+y‖^2-‖x-y‖^2 = 4*(x.re*y.re+x.im*y.im) := by
  simp only [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.sub_re,Complex.sub_im]
  ring

/-- Opposite offsets in the polynomial threshold yield a signed spatial
moment even though each individual area is nonnegative. -/
theorem xi_spatial_moment_by_polarization (c : ℂ) {R : ℝ} (hR : 0<R)
    (hb : ∀ z, ‖z-c‖=R → xi z≠0) :
    ∃ S : Finset ℂ, (∀ z, z∈S ↔ ‖z-c‖<R ∧ xi z=0) ∧ ∀ (q : ℂ[X]) (v : ℂ),
      Tendsto (fun u => (polynomialXiArea (q+C v) c R u - polynomialXiArea (q-C v) c R u)/(4*Real.pi))
        atTop (𝓝 (∑ z ∈ S, ((q.eval z).re*v.re+(q.eval z).im*v.im)*(hadamardOrder z:ℝ))) := by
  obtain ⟨S,hS,ha⟩ := xi_polynomial_area_form c hR hb
  refine ⟨S,hS,fun q v => ?_⟩
  have hl := ((ha (q+C v)).sub (ha (q-C v))).div_const (4*Real.pi)
  convert hl using 2
  rw [←mul_sub,←Finset.sum_sub_distrib]
  have hsum : ∑ z ∈ S, (‖eval z (q + C v)‖^2*(hadamardOrder z:ℝ) - ‖eval z (q - C v)‖^2*(hadamardOrder z:ℝ)) =
      4 * ∑ z ∈ S, ((q.eval z).re*v.re+(q.eval z).im*v.im)*(hadamardOrder z:ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [←sub_mul, eval_add, eval_sub, eval_C, polarized_norm]
    ring
  rw [hsum, eq_div_iff (by positivity)]
  ring

/-- A fixed four-probe scheme recovers the real and imaginary power
sums at each degree, including the winding at degree zero. -/
theorem xi_power_sums_from_four_areas (c : ℂ) {R : ℝ} (hR : 0<R)
    (hb : ∀ z, ‖z-c‖=R → xi z≠0) :
    ∃ S : Finset ℂ, (∀ z, z∈S ↔ ‖z-c‖<R ∧ xi z=0) ∧ ∀ k : ℕ,
      (Tendsto (fun u => (polynomialXiArea (X^k+C 1) c R u - polynomialXiArea (X^k-C 1) c R u)/(4*Real.pi))
        atTop (𝓝 (∑ z ∈ S, (z^k).re*(hadamardOrder z:ℝ)))) ∧
      (Tendsto (fun u => (polynomialXiArea (X^k+C I) c R u - polynomialXiArea (X^k-C I) c R u)/(4*Real.pi))
        atTop (𝓝 (∑ z ∈ S, (z^k).im*(hadamardOrder z:ℝ)))) := by
  obtain ⟨S,hS,h⟩ := xi_spatial_moment_by_polarization c hR hb
  refine ⟨S,hS,fun k => ⟨?_,?_⟩⟩
  · simpa only [eval_pow,eval_X,one_re,one_im,mul_one,mul_zero,add_zero] using h (X^k) 1
  · simpa only [eval_pow,eval_X,I_re,I_im,mul_one,mul_zero,zero_add] using h (X^k) I

/-- One directional power moment obtained from a pair of opposite offsets. -/
def directionalXiAreaMoment (c : ℂ) (R : ℝ) (k : ℕ) (v : ℂ) : ℝ :=
  limUnder atTop (fun u => (polynomialXiArea (X^k+C v) c R u -
    polynomialXiArea (X^k-C v) c R u)/(4*Real.pi))

/-- Two directions supply both coordinates of the complex moment. -/
def measuredXiPowerSum (c : ℂ) (R : ℝ) (k : ℕ) : ℂ :=
  ⟨directionalXiAreaMoment c R k 1, directionalXiAreaMoment c R k I⟩

/-- Newton reconstruction using only area readings. Degree zero supplies
the total multiplicity W. The first W complex moments then recover the
monic polynomial of the enclosed zeros, with their exact multiplicities. -/
theorem xi_divisor_polynomial_from_area_limits (c : ℂ) {R : ℝ} (hR : 0<R)
    (hb : ∀ z, ‖z-c‖=R → xi z≠0) :
    ∃ S : Finset ℂ, (∀ z, z∈S ↔ ‖z-c‖<R ∧ xi z=0) ∧
      ConjugateDiagonalGeometry.newtonPoly ⌊(measuredXiPowerSum c R 0).re⌋₊
        (measuredXiPowerSum c R) = ∏ z ∈ S, (X-C z)^(hadamardOrder z) := by
  obtain ⟨S,hS,h⟩ := xi_power_sums_from_four_areas c hR hb
  refine ⟨S,hS,?_⟩
  have hsum (k : ℕ) : measuredXiPowerSum c R k =
      ∑ z ∈ S, (hadamardOrder z:ℂ)*z^k := by
    apply Complex.ext
    · change directionalXiAreaMoment c R k 1 = _
      rw [Complex.re_sum]
      simpa only [directionalXiAreaMoment,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,
        zero_mul,mul_zero,sub_zero,mul_comm] using (h k).1.limUnder_eq
    · change directionalXiAreaMoment c R k I = _
      rw [Complex.im_sum]
      simpa only [directionalXiAreaMoment,Complex.mul_im,Complex.natCast_re,Complex.natCast_im,
        zero_mul,mul_zero,add_zero,zero_add,mul_comm] using (h k).2.limUnder_eq
  apply ConjugateDiagonalGeometry.newtonPoly_eq_finset_prod S id hadamardOrder
  · rw [hsum,Complex.re_sum]
    simp only [pow_zero,mul_one,Complex.natCast_re,← Nat.cast_sum,Nat.floor_natCast]
  · exact fun k _ _ => hsum k

#print axioms xi_divisor_polynomial_from_area_limits
#print axioms xi_spatial_moment_by_polarization
#print axioms xi_power_sums_from_four_areas
end GaloisForLFunctions.ExceptionalLayerTheory
