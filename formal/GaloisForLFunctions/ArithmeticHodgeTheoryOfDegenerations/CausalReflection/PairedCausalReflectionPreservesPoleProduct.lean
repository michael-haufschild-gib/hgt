import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ModulatedCausalReflectionMoments
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ComplexHalfLinePoleDomain

/-!
# Opposite pole moments survive a conjugate pair of reflections

All moments of both intermediate profiles follow from the actual weighted
square domain. The paired Laplace factor at a real argument is reciprocal
to its factor at the opposite argument, so their product is unchanged.
-/

noncomputable section
open MeasureTheory Filter

namespace GaloisForLFunctions.HTGeometry
open _root_.RHTower

/-- The weighted square domain discharges both admissions in the reflection law. -/
theorem negativeHalfLineLaplace_modulatedReflection_mul_of_halfLine_memLp
    {a : ℝ} (ha : 0 < a) (b : ℝ) {f : ℝ → ℂ}
    (hf : Integrable f) (hf2 : MemLp f 2 volume)
    (hf8 : MemLp (causalLaplaceWeighted (4 / Real.pi) f) 2 volume)
    (hs : ∀ u, 0 ≤ u → f u = 0)
    (hz : negativeHalfLineLaplace f (modulatedLaplaceRate a b) = 0)
    {q : ℂ} (hq : |q.re| ≤ 1 / 2) :
    (modulatedLaplaceRate a b - q) *
        negativeHalfLineLaplace (modulatedCausalReflection a b f) q =
      (modulatedLaplaceRate a (-b) + q) * negativeHalfLineLaplace f q := by
  apply negativeHalfLineLaplace_modulatedReflection_mul ha b hf hs hz
  · exact integrable_complexLaplaceWeighted_of_halfLine_memLp hq hf2 hf8 hs
  · exact integrable_complexLaplaceWeighted_of_halfLine_memLp hq
      (memLp_modulatedCausalConvolution ha b hf2)
      (memLp_weighted_modulatedCausalConvolution (add_pos ha (by positivity)) b hf8)
      (modulatedCausalConvolution_support_of_laplace_zero a b hs hz)

/-- The paired reflection has the quadratic Laplace factor on the half-pole strip. -/
theorem pairedCausalReflection_laplace_linear {a : ℝ} (ha : 0 < a)
    {b : ℝ} (hb : b ≠ 0) {F : ℝ → ℝ} (hF : Integrable F)
    (hF2 : MemLp (fun u => (F u : ℂ)) 2 volume)
    (hF8 : MemLp (causalLaplaceWeighted (4 / Real.pi) (fun u => (F u : ℂ))) 2 volume)
    (hFs : ∀ u, 0 ≤ u → F u = 0)
    (hz : negativeHalfLineLaplace (fun u => (F u : ℂ)) (modulatedLaplaceRate a b) = 0)
    {q : ℂ} (hq : |q.re| ≤ 1 / 2) :
    (modulatedLaplaceRate a b - q) * (modulatedLaplaceRate a (-b) - q) *
        negativeHalfLineLaplace (pairedCausalReflection a b (fun u => (F u : ℂ))) q =
      (modulatedLaplaceRate a b + q) * (modulatedLaplaceRate a (-b) + q) *
        negativeHalfLineLaplace (fun u => (F u : ℂ)) q := by
  let f : ℝ → ℂ := fun u => (F u : ℂ)
  let G := modulatedCausalReflection a b f
  have hf : Integrable f := hF.ofReal (𝕜 := ℂ)
  have hs : ∀ u, 0 ≤ u → f u = 0 := by
    intro u hu
    change (F u : ℂ) = 0
    rw [hFs u hu, Complex.ofReal_zero]
  have hG := integrable_modulatedCausalReflection ha b hf
  have hG2 := memLp_modulatedCausalReflection ha b hF2
  have hG8 := memLp_weighted_modulatedCausalReflection (add_pos ha (by positivity)) b hF8
  have hGs := modulatedCausalReflection_support_of_laplace_zero a b hs hz
  have hzG := modulatedCausalReflection_has_conjugateLaplaceZero ha hb hF hFs hz
  have hfirst := negativeHalfLineLaplace_modulatedReflection_mul_of_halfLine_memLp
    ha b hf hF2 hF8 hs hz hq
  have hsecond := negativeHalfLineLaplace_modulatedReflection_mul_of_halfLine_memLp
    ha (-b) hG hG2 hG8 hGs hzG hq
  simp only [neg_neg] at hsecond
  calc
    _ = (modulatedLaplaceRate a b - q) *
        ((modulatedLaplaceRate a (-b) - q) *
          negativeHalfLineLaplace (modulatedCausalReflection a (-b) G) q) := by
      change _ = (modulatedLaplaceRate a b - q) *
        ((modulatedLaplaceRate a (-b) - q) *
          negativeHalfLineLaplace (pairedCausalReflection a b f) q)
      ring
    _ = (modulatedLaplaceRate a b + q) *
        ((modulatedLaplaceRate a b - q) * negativeHalfLineLaplace G q) := by
      rw [hsecond]
      ring
    _ = _ := by rw [hfirst]; ring

/-- A genuinely complex rate cannot meet a real pole argument. -/
theorem modulatedLaplaceRate_sub_real_ne_zero (a : ℝ) {b : ℝ} (hb : b ≠ 0) (s : ℝ) :
    modulatedLaplaceRate a b - (s : ℂ) ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  have he : (modulatedLaplaceRate a b - (s : ℂ)).im = 2 * Real.pi * b := by
    simp [modulatedLaplaceRate]
  rw [he, Complex.zero_im] at hi
  exact (mul_ne_zero (by positivity : 2 * Real.pi ≠ 0) hb) hi

/-- Every opposite real moment pair in the half-pole strip is preserved exactly. -/
theorem pairedCausalReflection_laplace_pair {a : ℝ} (ha : 0 < a)
    {b : ℝ} (hb : b ≠ 0) {F : ℝ → ℝ} (hF : Integrable F)
    (hF2 : MemLp (fun u => (F u : ℂ)) 2 volume)
    (hF8 : MemLp (causalLaplaceWeighted (4 / Real.pi) (fun u => (F u : ℂ))) 2 volume)
    (hFs : ∀ u, 0 ≤ u → F u = 0)
    (hz : negativeHalfLineLaplace (fun u => (F u : ℂ)) (modulatedLaplaceRate a b) = 0)
    {s : ℝ} (hs : |s| ≤ 1 / 2) :
    negativeHalfLineLaplace (pairedCausalReflection a b (fun u => (F u : ℂ))) (s : ℂ) *
        negativeHalfLineLaplace (pairedCausalReflection a b (fun u => (F u : ℂ))) (-(s : ℂ)) =
      negativeHalfLineLaplace (fun u => (F u : ℂ)) (s : ℂ) *
        negativeHalfLineLaplace (fun u => (F u : ℂ)) (-(s : ℂ)) := by
  let f : ℝ → ℂ := fun u => (F u : ℂ)
  let P := pairedCausalReflection a b f
  let D := (modulatedLaplaceRate a b - (s : ℂ)) *
    (modulatedLaplaceRate a (-b) - (s : ℂ))
  let N := (modulatedLaplaceRate a b + (s : ℂ)) *
    (modulatedLaplaceRate a (-b) + (s : ℂ))
  have hplus := pairedCausalReflection_laplace_linear ha hb hF hF2 hF8 hFs hz
    (q := (s : ℂ)) (by simpa only [Complex.ofReal_re] using hs)
  have hminus := pairedCausalReflection_laplace_linear ha hb hF hF2 hF8 hFs hz
    (q := -(s : ℂ)) (by simpa only [Complex.neg_re, Complex.ofReal_re, abs_neg] using hs)
  simp only [sub_neg_eq_add, add_neg_eq_sub] at hminus
  change D * negativeHalfLineLaplace P (s : ℂ) = N * negativeHalfLineLaplace f (s : ℂ) at hplus
  change N * negativeHalfLineLaplace P (-(s : ℂ)) = D * negativeHalfLineLaplace f (-(s : ℂ)) at hminus
  have hzplus : modulatedLaplaceRate a b + (s : ℂ) ≠ 0 := by
    simpa only [Complex.ofReal_neg, sub_neg_eq_add] using modulatedLaplaceRate_sub_real_ne_zero a hb (-s)
  have hwplus : modulatedLaplaceRate a (-b) + (s : ℂ) ≠ 0 := by
    simpa only [Complex.ofReal_neg, sub_neg_eq_add] using
      modulatedLaplaceRate_sub_real_ne_zero a (neg_ne_zero.mpr hb) (-s)
  have hDN : D * N ≠ 0 := mul_ne_zero
    (mul_ne_zero (modulatedLaplaceRate_sub_real_ne_zero a hb s)
      (modulatedLaplaceRate_sub_real_ne_zero a (neg_ne_zero.mpr hb) s))
    (mul_ne_zero hzplus hwplus)
  apply mul_left_cancel₀ hDN
  change (D * N) * (negativeHalfLineLaplace P (s : ℂ) * negativeHalfLineLaplace P (-(s : ℂ))) =
    (D * N) * (negativeHalfLineLaplace f (s : ℂ) * negativeHalfLineLaplace f (-(s : ℂ)))
  calc
    _ = (D * negativeHalfLineLaplace P (s : ℂ)) *
        (N * negativeHalfLineLaplace P (-(s : ℂ))) := by ring
    _ = (N * negativeHalfLineLaplace f (s : ℂ)) *
        (D * negativeHalfLineLaplace f (-(s : ℂ))) := by rw [hplus, hminus]
    _ = _ := by ring

end GaloisForLFunctions.HTGeometry
