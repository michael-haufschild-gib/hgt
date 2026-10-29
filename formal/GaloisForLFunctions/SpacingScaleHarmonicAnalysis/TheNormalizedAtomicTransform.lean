import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.OverlapCoordinates
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheAtomicFamilyIsADirichletPolynomial
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheRobinConstantOfAnAtom
import GaloisForLFunctions.ArithmeticOrientationGeometry.TheOrientationOfACycle
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheCriticalExponent
import GaloisForLFunctions.HTGeometry.CompactFourierEntire

/-!
# The normalized atomic transform

At width `w = c/N = 1/T`, the unnormalized atom contributes the factor
`w h_φ(wz)`. The unit-mass dilation contributes `h_φ(z/T)`. Both multiply the same
Dirichlet polynomial, at every complex spectral argument, including off-line zeros and poles.
The Fourier window has no hard height cutoff when the compact profile has nonzero mass.
-/

noncomputable section

set_option autoImplicit false

open MeasureTheory Finset Zeta23
open scoped Real ComplexConjugate

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis

open ArithmeticElectrostatics ArithmeticCastelnuovoSeveri ArithmeticOrientationGeometry

/-- Conventional Dirichlet polynomial, written with the real logarithm at positive integers. -/
def mellinPolynomial (N : ℕ) (a : ℕ → ℝ) (s : ℂ) : ℂ :=
  ∑ n ∈ Icc 1 N, (a n : ℂ) * Complex.exp (-s * (Real.log n : ℂ))

/-- The positive Fourier convention reads the critical line at `1/2 - iz`, with weights `√n x_n`. -/
theorem dirichletPoly_eq_mellinPolynomial (N : ℕ) (x : ℕ → ℝ) (z : ℂ) :
    dirichletPoly N x z =
      mellinPolynomial N (fun n => Real.sqrt n * x n) (1 / 2 - Complex.I * z) := by
  unfold dirichletPoly mellinPolynomial
  refine sum_congr rfl fun n hn => ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hsqrt : (Real.sqrt n : ℂ) = Complex.exp ((Real.log n : ℂ) / 2) := by
    have hs : Real.sqrt n = Real.exp (Real.log n / 2) := by
      rw [Real.exp_half, Real.exp_log hn0]
    rw [hs, Complex.ofReal_exp]
    push_cast
    rfl
  rw [Complex.ofReal_mul, hsqrt]
  calc
    (x n : ℂ) * Complex.exp (Complex.I * z * (Real.log n : ℂ)) =
        (x n : ℂ) * Complex.exp
          ((Real.log n : ℂ) / 2 + -(1 / 2 - Complex.I * z) * (Real.log n : ℂ)) := by
      congr 2
      ring
    _ = _ := by rw [Complex.exp_add]; ring

theorem atomDilate_eq_dilateTest (φ : ℝ → ℝ) (w : ℝ) :
    atomDilate φ w = dilateTest w φ := by
  funext u
  simp only [atomDilate, dilateTest, div_eq_mul_inv, mul_comm]

/-- The dilation Jacobian is present for unnormalized atoms. -/
theorem paperFT_atomDilate {w : ℝ} (hw : 0 < w) (φ : ℝ → ℝ) (z : ℂ) :
    paperFT (cx (atomDilate φ w)) z = (w : ℂ) * paperFT (cx φ) ((w : ℂ) * z) := by
  rw [atomDilate_eq_dilateTest, paperFT_dilateTest hw.ne', abs_of_pos hw]

theorem hasCompactSupport_atomDilate {w : ℝ} (hw : w ≠ 0) {φ : ℝ → ℝ}
    (hφ : HasCompactSupport φ) : HasCompactSupport (atomDilate φ w) := by
  have hc := hφ.comp_homeomorph (Homeomorph.mulRight₀ w⁻¹ (inv_ne_zero hw))
  change HasCompactSupport (fun u => φ (u * w⁻¹)) at hc
  change HasCompactSupport (fun u => φ (u / w))
  simpa only [div_eq_mul_inv] using hc

/-- Exact raw atomic transform; no restriction to the critical line is used. -/
theorem paperFT_atomicTest_atomDilate {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) {w : ℝ} (hw : 0 < w) (N : ℕ) (x : ℕ → ℝ) (z : ℂ) :
    paperFT (cx (atomicTest N x (atomDilate φ w))) z =
      (w : ℂ) * paperFT (cx φ) ((w : ℂ) * z) * dirichletPoly N x z := by
  have hg : Continuous (atomDilate φ w) := by
    unfold atomDilate
    fun_prop
  rw [paperFT_atomicTest hg
    (hasCompactSupport_atomDilate hw.ne' hφc), paperFT_atomDilate hw]

/-- Unit-mass dilation removes precisely the dilation Jacobian. -/
theorem paperFT_massPreservingDilate {T : ℝ} (hT : 0 < T) (φ : ℝ → ℝ) (z : ℂ) :
    paperFT (cx (dilate T φ)) z = paperFT (cx φ) (z / (T : ℂ)) := by
  have heq : cx (dilate T φ) = fun u => (T : ℂ) * cx (atomDilate φ T⁻¹) u := by
    funext u
    simp only [cx, dilate, atomDilate, div_inv_eq_mul, mul_comm u T, Complex.ofReal_mul]
  have hlin : paperFT (cx (dilate T φ)) z =
      (T : ℂ) * paperFT (cx (atomDilate φ T⁻¹)) z := by
    rw [heq]
    simp only [paperFT, mul_assoc, integral_const_mul]
  rw [hlin, paperFT_atomDilate (inv_pos.mpr hT)]
  have hTc : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  push_cast
  rw [← mul_assoc, mul_inv_cancel₀ hTc, one_mul]
  congr 1
  ring

/-- Spectral height is the inverse physical width, for the corpus's unit-mass convention. -/
theorem paperFT_atomicTest_at_height {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) {T : ℝ} (hT : 0 < T) (N : ℕ) (x : ℕ → ℝ) (z : ℂ) :
    paperFT (cx (atomicTest N x (dilate T φ))) z =
      paperFT (cx φ) (z / (T : ℂ)) * dirichletPoly N x z := by
  have hc : HasCompactSupport (dilate T φ) :=
    (hφc.comp_homeomorph (Homeomorph.mulLeft₀ T hT.ne')).mul_left
  have hg : Continuous (dilate T φ) := by
    unfold dilate
    fun_prop
  rw [paperFT_atomicTest hg hc,
    paperFT_massPreservingDilate hT]

/-- A compact profile of nonzero mass has nonzero Fourier values at arbitrarily large heights. -/
theorem exists_paperFT_ne_zero_above {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hmass : (∫ u, φ u) ≠ 0) (B : ℝ) :
    ∃ t : ℝ, B < t ∧ paperFT (cx φ) (t : ℂ) ≠ 0 := by
  by_contra h
  push Not at h
  have hd : Differentiable ℂ (paperFT (cx φ)) :=
    _root_.RHTower.EvenSector.differentiable_paperFT_of_compact
      (Complex.continuous_ofReal.comp hφ) (hφc.comp_left Complex.ofReal_zero)
  have hz := HTGeometry.entire_eq_zero_of_vanishing_on_real_interval
    (t₀ := B + 2) hd (show (0 : ℝ) < 1 by norm_num)
    (fun t ht => h t (by linarith only [(abs_lt.mp ht).1])) (0 : ℂ)
  have hzero : paperFT (cx φ) 0 = ((∫ u, φ u : ℝ) : ℂ) := by
    simp only [paperFT, cx, mul_zero, zero_mul, Complex.exp_zero, mul_one]
    exact integral_ofReal
  rw [hzero] at hz
  exact hmass (Complex.ofReal_eq_zero.mp hz)

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis

#print axioms GaloisForLFunctions.SpacingScaleHarmonicAnalysis.paperFT_atomicTest_atomDilate
#print axioms GaloisForLFunctions.SpacingScaleHarmonicAnalysis.dirichletPoly_eq_mellinPolynomial
#print axioms GaloisForLFunctions.SpacingScaleHarmonicAnalysis.paperFT_atomicTest_at_height
#print axioms GaloisForLFunctions.SpacingScaleHarmonicAnalysis.exists_paperFT_ne_zero_above
