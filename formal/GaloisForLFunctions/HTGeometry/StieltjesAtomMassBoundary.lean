import GaloisForLFunctions.HTGeometry.AtomMassLimit
import GaloisForLFunctions.HTGeometry.StieltjesTransformPick
import GaloisForLFunctions.HTGeometry.LeafCauchyTransform

/-!
# Atom mass from the boundary growth of a Stieltjes transform

Multiplying the imaginary part of the Cauchy transform at `a + iy` by `y` produces the corpus's
scaled atom kernel exactly. Dominated convergence therefore recovers the mass at `a`. This is the
measure-theoretic bridge between a real pole of an algebraic Cauchy transform and a spectral atom.
-/

open Filter Topology MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The scaled imaginary Cauchy kernel is literally the atom-selection kernel under the integral. -/
theorem mul_im_stieltjes_eq_integral_atomKernel
    (μ : Measure ℝ) [IsFiniteMeasure μ] (a y : ℝ) (hy : y ≠ 0) :
    y * (∫ t : ℝ, ((t : ℂ) - ((a : ℂ) + (y : ℂ) * Complex.I))⁻¹ ∂μ).im =
      ∫ t : ℝ, atomKernel a y t ∂μ := by
  have hz : (((a : ℂ) + (y : ℂ) * Complex.I).im) ≠ 0 := by simpa using hy
  rw [HTGeometry.im_integral (HTGeometry.integrable_cauchy_kernel μ hz),
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  change y * (((t : ℂ) - ((a : ℂ) + (y : ℂ) * Complex.I))⁻¹).im = atomKernel a y t
  rw [HTGeometry.cauchyKernel_im]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, mul_one, zero_add, mul_zero, add_zero]
  rw [atomKernel]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.ofReal_re, Complex.add_re,
    Complex.mul_re, Complex.I_re, Complex.I_im, Complex.sub_im, Complex.ofReal_im,
    Complex.add_im, Complex.mul_im, mul_one, mul_zero, add_zero, zero_add]
  ring

/-- **Stieltjes atom formula.** The nontangential boundary growth `y Im Sμ(a+iy)` converges to the
exact atom mass `μ({a})`. -/
theorem tendsto_mul_im_stieltjes_atomMass
    (μ : Measure ℝ) [IsFiniteMeasure μ] (a : ℝ) :
    Tendsto (fun y : ℝ =>
      y * (∫ t : ℝ, ((t : ℂ) - ((a : ℂ) + (y : ℂ) * Complex.I))⁻¹ ∂μ).im)
      (𝓝[≠] 0) (𝓝 (μ {a}).toReal) := by
  refine (tendsto_integral_atomKernel μ a).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (mul_im_stieltjes_eq_integral_atomKernel μ a y hy).symm

end

end GaloisForLFunctions.HTGeometry
