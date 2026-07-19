import GaloisForLFunctions.HTGeometry.ChamberLowerBound
import GaloisForLFunctions.HTGeometry.ComplexIntegralGram

/-!
# Integrability of the scaled Cauchy kernel products

The entries of the measure Gram are integrals of products of two scaled Cauchy kernels.  Such a
product is integrable as soon as both atom kernels are: its modulus is the product of the two
moduli, which the arithmetic-geometric mean inequality bounds by the average of the two squared
moduli, and those are the atom kernels.

At a nonzero height the kernels are continuous, since the node lies off the real line, so no
measurability hypothesis is needed.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

noncomputable section

/-- At a nonzero height the scaled Cauchy kernel is continuous: its node is off the real line. -/
theorem continuous_scaledCauchy {a y : ℝ} (hy : y ≠ 0) :
    Continuous fun t : ℝ => (y : ℂ) * ((t : ℂ) - upperNode a y)⁻¹ :=
  continuous_const.mul
    (Continuous.inv₀ (Complex.continuous_ofReal.sub continuous_const) (sub_upperNode_ne_zero hy))

/-- **The product of two scaled Cauchy kernels is integrable.**  Its modulus is bounded by the
average of the two atom kernels. -/
theorem integrable_scaledCauchy_product {ν : Measure ℝ} {a b y : ℝ} (hy : y ≠ 0)
    (hfi : Integrable (fun t : ℝ => atomKernel a y t) ν)
    (hgi : Integrable (fun t : ℝ => atomKernel b y t) ν) :
    Integrable (fun t : ℝ => ((y : ℂ) * ((t : ℂ) - upperNode a y)⁻¹) *
      (starRingEnd ℂ) ((y : ℂ) * ((t : ℂ) - upperNode b y)⁻¹)) ν := by
  have hfsq : Integrable (fun t : ℝ => ‖(y : ℂ) * ((t : ℂ) - upperNode a y)⁻¹‖ ^ 2) ν :=
    (integrable_normSq_scaled_cauchy_iff ν a y).2 hfi
  have hgsq : Integrable (fun t : ℝ => ‖(y : ℂ) * ((t : ℂ) - upperNode b y)⁻¹‖ ^ 2) ν :=
    (integrable_normSq_scaled_cauchy_iff ν b y).2 hgi
  have hbound : Integrable (fun t : ℝ =>
      (‖(y : ℂ) * ((t : ℂ) - upperNode a y)⁻¹‖ ^ 2
        + ‖(y : ℂ) * ((t : ℂ) - upperNode b y)⁻¹‖ ^ 2) / 2) ν :=
    (hfsq.add hgsq).div_const 2
  refine hbound.mono' ?_ ?_
  · exact ((continuous_scaledCauchy hy).mul
      (Complex.continuous_conj.comp (continuous_scaledCauchy hy))).aestronglyMeasurable
  · filter_upwards with t
    rw [norm_mul, Complex.norm_conj]
    nlinarith [sq_nonneg (‖(y : ℂ) * ((t : ℂ) - upperNode a y)⁻¹‖
      - ‖(y : ℂ) * ((t : ℂ) - upperNode b y)⁻¹‖),
      norm_nonneg ((y : ℂ) * ((t : ℂ) - upperNode a y)⁻¹),
      norm_nonneg ((y : ℂ) * ((t : ℂ) - upperNode b y)⁻¹)]

end

end GaloisForLFunctions.HTGeometry
