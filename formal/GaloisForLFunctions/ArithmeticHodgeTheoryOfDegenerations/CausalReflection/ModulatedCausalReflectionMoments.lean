import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ComplexCausalLaplaceBoundary
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.PairedCausalReflectionIsReal

/-!
# Complex reflection moments and preservation of the conjugate zero

The exact resolvent law gives the linear Laplace factor of a reflection.
For real data, a nonreal zero has a conjugate zero; the first reflection
preserves that second zero, so the conjugate pair retains half-line support.
-/

noncomputable section
open MeasureTheory Filter
open scoped Convolution

namespace GaloisForLFunctions.HTGeometry

/-- The linear Laplace factor of the actual complex-rate reflection. -/
theorem negativeHalfLineLaplace_modulatedReflection_mul {a : ℝ} (ha : 0 < a)
    (b : ℝ) {f : ℝ → ℂ} (hf : Integrable f)
    (hs : ∀ u, 0 ≤ u → f u = 0)
    (hz : negativeHalfLineLaplace f (modulatedLaplaceRate a b) = 0)
    {q : ℂ} (hq : Integrable (complexLaplaceWeighted q f))
    (hKq : Integrable (complexLaplaceWeighted q (modulatedCausalConvolution a b f))) :
    (modulatedLaplaceRate a b - q) *
        negativeHalfLineLaplace (modulatedCausalReflection a b f) q =
      (modulatedLaplaceRate a (-b) + q) * negativeHalfLineLaplace f q := by
  have hpos : 0 < (modulatedLaplaceRate a b).re := by
    simpa [modulatedLaplaceRate] using mul_pos Real.pi_pos ha
  have hk : modulatedCausalConvolution a b f =
      complexRateCausalKernel (modulatedLaplaceRate a b) ⋆[ContinuousLinearMap.mul ℂ ℂ] f := by
    rw [modulatedCausalConvolution, modulatedCausalExponential_eq_complexRate]
  have hm := negativeHalfLineLaplace_causalConvolution_mul hpos hf hs hz hq
  rw [← hk] at hm
  have hsplit : complexLaplaceWeighted q (modulatedCausalReflection a b f) =
      fun u => -complexLaplaceWeighted q f u +
        (2 * a : ℂ) * complexLaplaceWeighted q (modulatedCausalConvolution a b f) u := by
    funext u
    unfold complexLaplaceWeighted modulatedCausalReflection
    ring
  have hmoment : negativeHalfLineLaplace (modulatedCausalReflection a b f) q =
      -negativeHalfLineLaplace f q +
        (2 * a : ℂ) * negativeHalfLineLaplace (modulatedCausalConvolution a b f) q := by
    change (∫ u, complexLaplaceWeighted q (modulatedCausalReflection a b f) u) = _
    rw [hsplit, integral_add hq.neg (hKq.const_mul (2 * a : ℂ)), integral_neg, integral_const_mul]
    rfl
  have hfactor : (2 * a : ℂ) * (Real.pi : ℂ) - (modulatedLaplaceRate a b - q) =
      modulatedLaplaceRate a (-b) + q := by
    unfold modulatedLaplaceRate
    push_cast
    ring
  rw [hmoment]
  calc
    _ = -(modulatedLaplaceRate a b - q) * negativeHalfLineLaplace f q +
        (2 * a : ℂ) * ((modulatedLaplaceRate a b - q) *
          negativeHalfLineLaplace (modulatedCausalConvolution a b f) q) := by ring
    _ = ((2 * a : ℂ) * (Real.pi : ℂ) - (modulatedLaplaceRate a b - q)) *
        negativeHalfLineLaplace f q := by rw [hm]; ring
    _ = _ := by rw [hfactor]

/-- Conjugate Laplace arguments have conjugate values on actual real data. -/
theorem negativeHalfLineLaplace_real_conj (F : ℝ → ℝ) (z : ℂ) :
    negativeHalfLineLaplace (fun u => (F u : ℂ)) ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (negativeHalfLineLaplace (fun u => (F u : ℂ)) z) := by
  unfold negativeHalfLineLaplace
  rw [← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal]

/-- Reflection at one nonreal zero preserves the conjugate zero of real data. -/
theorem modulatedCausalReflection_has_conjugateLaplaceZero {a : ℝ} (ha : 0 < a)
    {b : ℝ} (hb : b ≠ 0) {F : ℝ → ℝ} (hF : Integrable F)
    (hFs : ∀ u, 0 ≤ u → F u = 0)
    (hz : negativeHalfLineLaplace (fun u => (F u : ℂ)) (modulatedLaplaceRate a b) = 0) :
    negativeHalfLineLaplace
      (modulatedCausalReflection a b (fun u => (F u : ℂ))) (modulatedLaplaceRate a (-b)) = 0 := by
  let f : ℝ → ℂ := fun u => (F u : ℂ)
  have hf : Integrable f := hF.ofReal (𝕜 := ℂ)
  have hs : ∀ u, 0 ≤ u → f u = 0 := by
    intro u hu
    change (F u : ℂ) = 0
    rw [hFs u hu, Complex.ofReal_zero]
  have hbar : negativeHalfLineLaplace f (modulatedLaplaceRate a (-b)) = 0 := by
    change negativeHalfLineLaplace (fun u => (F u : ℂ)) (modulatedLaplaceRate a (-b)) = 0
    rw [← conj_modulatedLaplaceRate, negativeHalfLineLaplace_real_conj, hz, map_zero]
  have hpos : 0 < (modulatedLaplaceRate a (-b)).re := by
    simpa [modulatedLaplaceRate] using mul_pos Real.pi_pos ha
  have hK := integrable_modulatedCausalConvolution ha b hf
  have hKs := modulatedCausalConvolution_support_of_laplace_zero a b hs hz
  have hm := negativeHalfLineLaplace_modulatedReflection_mul ha b hf hs hz
    (integrable_negativeHalfLineLaplace hf hs hpos.le)
    (integrable_negativeHalfLineLaplace hK hKs hpos.le)
  have hn : modulatedLaplaceRate a b - modulatedLaplaceRate a (-b) ≠ 0 := by
    have hi : (modulatedLaplaceRate a b - modulatedLaplaceRate a (-b)).im =
        4 * Real.pi * b := by simp [modulatedLaplaceRate] <;> ring
    intro h
    have hh := congrArg Complex.im h
    rw [hi, Complex.zero_im] at hh
    exact (mul_ne_zero (by positivity : 4 * Real.pi ≠ 0) hb) hh
  rw [hbar, mul_zero] at hm
  exact (mul_eq_zero.mp hm).resolve_left hn

/-- Both reflections retain support when the input zero is nonreal. -/
theorem pairedCausalReflection_support_of_nonreal_zero {a : ℝ} (ha : 0 < a)
    {b : ℝ} (hb : b ≠ 0) {F : ℝ → ℝ} (hF : Integrable F)
    (hFs : ∀ u, 0 ≤ u → F u = 0)
    (hz : negativeHalfLineLaplace (fun u => (F u : ℂ)) (modulatedLaplaceRate a b) = 0) :
    ∀ u, 0 ≤ u → pairedCausalReflection a b (fun t => (F t : ℂ)) u = 0 := by
  have hs : ∀ u, 0 ≤ u → (F u : ℂ) = 0 := by
    intro u hu
    rw [hFs u hu, Complex.ofReal_zero]
  exact modulatedCausalReflection_support_of_laplace_zero a (-b)
    (modulatedCausalReflection_support_of_laplace_zero a b hs hz)
    (modulatedCausalReflection_has_conjugateLaplaceZero ha hb hF hFs hz)

end GaloisForLFunctions.HTGeometry
