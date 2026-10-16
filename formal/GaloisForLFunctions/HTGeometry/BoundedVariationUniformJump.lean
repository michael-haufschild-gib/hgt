import GaloisForLFunctions.HTGeometry.BoundedVariationTranslationIntegral

/-! # Uniform error controls BV jump energy

Keep the actual uniform bound separate from total variation. This permits
uniformly small errors with bounded variation to converge in a jump norm
whose Levy measure has a finite first moment.
-/

noncomputable section
open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

theorem boundedVariation_translation_sq_le_of_bound {f : ℝ → ℝ}
    (hf : BoundedVariationOn f univ) {M h : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x, |f x| ≤ M) (hh : 0 ≤ h) :
    (∫ x, (f x - f (x + h)) ^ 2) ≤
      4 * M * (eVariationOn f univ).toReal * h := by
  let V := (eVariationOn f univ).toReal
  let w := variationOnFromTo f univ 0
  have hw : Monotone w := monotoneOn_univ.mp
    (variationOnFromTo.monotoneOn hf.locallyBoundedVariationOn (mem_univ 0))
  have hV : ∀ x, |w x| ≤ V := fun _ => variationOnFromTo.abs_le_eVariationOn hf
  have hi := integrable_monotone_translate_sub hw hV hh
  have hdom (x : ℝ) : (f x - f (x + h)) ^ 2 ≤
      (2 * M) * (w (x + h) - w x) := by
    have hd := variationOnFromTo.abs_sub_le_sub_of_le hf.locallyBoundedVariationOn
      (mem_univ 0) (mem_univ x) (mem_univ (x + h)) (show x ≤ x + h by linarith)
    rw [abs_sub_comm] at hd
    have hn : |f x - f (x + h)| ≤ 2 * M := by
      have ht := (abs_sub (f x) (f (x + h))).trans (add_le_add (hb x) (hb (x + h)))
      linarith
    have hp := mul_le_mul hn hd (abs_nonneg _) (mul_nonneg (by positivity) hM)
    nlinarith [sq_abs (f x - f (x + h))]
  calc
    _ ≤ ∫ x, (2 * M) * (w (x + h) - w x) :=
      integral_mono (boundedVariation_translation_sq hf hh).1 (hi.const_mul _) hdom
    _ = (2 * M) * ∫ x, w (x + h) - w x := integral_const_mul _ _
    _ ≤ (2 * M) * ((2 * V) * h) := mul_le_mul_of_nonneg_left
      (integral_monotone_translate_sub_le hw hV hh) (mul_nonneg (by positivity) hM)
    _ = _ := by dsimp [V]; ring

end GaloisForLFunctions.HTGeometry
