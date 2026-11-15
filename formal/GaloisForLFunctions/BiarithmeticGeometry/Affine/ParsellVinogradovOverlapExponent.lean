import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovQuadraticOverlap
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The exact quadratic-frame overlap exponent

For zero vertical translation, the overlap volume is comparable to
`(1+|θ|)⁻³`. Consequently the weighted overlap is uniformly bounded exactly
for real exponents at most three. The supercritical direction uses positive
real-power growth, not a discrete sampling argument.
-/

open Filter MeasureTheory
open GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov.Quadratic

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- The cubic exponent is the exact threshold for uniformly bounded weighted overlap. -/
theorem bounded_quadratic_overlap_iff (p : ℝ) :
    (∃ C : ℝ, ∀ θ : ℝ,
      (1 + |θ|) ^ p * (volume (Quadratic.overlap θ 0)).toReal ≤ C) ↔ p ≤ 3 := by
  constructor
  · rintro ⟨C, hC⟩
    by_contra hp
    have hd : 0 < p - 3 := sub_pos.mpr (lt_of_not_ge hp)
    have hg : ∀ᶠ x : ℝ in atTop, 32 * (|C| + 1) < x ^ (p - 3) :=
      (tendsto_rpow_atTop hd).eventually (eventually_gt_atTop (32 * (|C| + 1)))
    obtain ⟨x, hxg, hx⟩ := (hg.and (eventually_ge_atTop (1 : ℝ))).exists
    have hx0 : 0 < x := zero_lt_one.trans_le hx
    have hb : 1 + |x - 1| = x := by
      rw [abs_of_nonneg (sub_nonneg.mpr hx)]
      ring
    have hlo := regularized_cubic_mul_real_volume_ge (x - 1)
    have hhi := hC (x - 1)
    rw [hb] at hlo hhi
    have hmul := mul_le_mul_of_nonneg_left hlo (Real.rpow_nonneg hx0.le (p - 3))
    have he : x ^ (p - 3) * x ^ (3 : ℕ) = x ^ p := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hx0]
      congr 1
      ring
    have hbound : x ^ (p - 3) * (1 / 32) ≤ C := by
      calc
        _ ≤ x ^ (p - 3) * (x ^ (3 : ℕ) * (volume (Quadratic.overlap (x - 1) 0)).toReal) := hmul
        _ = x ^ p * (volume (Quadratic.overlap (x - 1) 0)).toReal := by rw [← mul_assoc, he]
        _ ≤ C := hhi
    linarith only [hbound, hxg, le_abs_self C]
  · intro hp
    refine ⟨256, fun θ => ?_⟩
    have hb : 1 ≤ 1 + |θ| := by linarith only [abs_nonneg θ]
    have hpow : (1 + |θ|) ^ p ≤ (1 + |θ|) ^ (3 : ℕ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hb hp
    exact (mul_le_mul_of_nonneg_right hpow ENNReal.toReal_nonneg).trans
      (regularized_cubic_mul_real_volume_le θ 0)

/-- The same threshold holds uniformly over all vertical translations. -/
theorem bounded_quadratic_overlap_uniform_translation_iff (p : ℝ) :
    (∃ C : ℝ, ∀ θ t : ℝ,
      (1 + |θ|) ^ p * (volume (Quadratic.overlap θ t)).toReal ≤ C) ↔ p ≤ 3 := by
  constructor
  · rintro ⟨C, hC⟩
    exact (bounded_quadratic_overlap_iff p).mp ⟨C, fun θ => hC θ 0⟩
  · intro hp
    refine ⟨256, fun θ t => ?_⟩
    have hb : 1 ≤ 1 + |θ| := by linarith only [abs_nonneg θ]
    have hpow : (1 + |θ|) ^ p ≤ (1 + |θ|) ^ (3 : ℕ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hb hp
    exact (mul_le_mul_of_nonneg_right hpow ENNReal.toReal_nonneg).trans
      (regularized_cubic_mul_real_volume_le θ t)

#print axioms bounded_quadratic_overlap_iff
#print axioms bounded_quadratic_overlap_uniform_translation_iff

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
