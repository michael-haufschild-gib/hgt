import GaloisForLFunctions.HTGeometry.MonotoneTranslationModulus
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Whole-line jump admission from finite variation

Signed variation dominates every translation increment. Finite-interval
telescoping and exhaustion pay the whole-line integral, including jumps and
singular continuous variation. No differentiability of the profile is used.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

theorem measurable_of_boundedVariation_univ {f : ℝ → ℝ}
    (hf : BoundedVariationOn f univ) : Measurable f := by
  obtain ⟨p, q, hp, hq, rfl⟩ :=
    hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  exact (monotoneOn_univ.mp hp).measurable.sub (monotoneOn_univ.mp hq).measurable

theorem norm_le_of_boundedVariation_univ {f : ℝ → ℝ}
    (hf : BoundedVariationOn f univ) (x : ℝ) :
    ‖f x‖ ≤ ‖f 0‖ + (eVariationOn f univ).toReal := by
  have hd := hf.dist_le (mem_univ x) (mem_univ 0)
  have ht := norm_add_le (f x - f 0) (f 0)
  rw [sub_add_cancel] at ht
  rw [dist_eq_norm] at hd
  linarith

private theorem monotone_translate_interval_bound {w : ℝ → ℝ}
    (hw : Monotone w) {M h : ℝ} (hb : ∀ x, |w x| ≤ M) (hh : 0 ≤ h)
    (a b : ℝ) :
    (∫ x in a..b, |w (x+h)-w x|) ≤ (2*M)*h := by
  apply integral_abs_translate_sub_le_variation hw hh
  have ha := (abs_le.mp (hb a)).1
  have hb' := (abs_le.mp (hb (b+h))).2
  linarith

theorem integrable_monotone_translate_sub {w : ℝ → ℝ} (hw : Monotone w)
    {M h : ℝ} (hb : ∀ x, |w x| ≤ M) (hh : 0 ≤ h) :
    Integrable (fun x => w (x+h)-w x) := by
  apply integrable_of_intervalIntegral_norm_bounded ((2*M)*h)
    (a := fun n : ℕ => -(n : ℝ)) (b := fun n : ℕ => (n : ℝ))
    (fun n => (MonotoneTranslation.intervalIntegrable_translate_sub hw h _ _).1)
    (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
    tendsto_natCast_atTop_atTop
  exact Eventually.of_forall fun n => by
    simpa only [Real.norm_eq_abs] using monotone_translate_interval_bound hw hb hh
      (-(n : ℝ)) (n : ℝ)

theorem integral_monotone_translate_sub_le {w : ℝ → ℝ} (hw : Monotone w)
    {M h : ℝ} (hb : ∀ x, |w x| ≤ M) (hh : 0 ≤ h) :
    (∫ x, w (x+h)-w x) ≤ (2*M)*h := by
  have hi := integrable_monotone_translate_sub hw hb hh
  have hc := aecover_Icc (μ := (volume : Measure ℝ))
    (tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply le_of_tendsto (hc.integral_tendsto_of_countably_generated hi)
  refine Eventually.of_forall fun n => ?_
  dsimp only [Function.comp_def]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le
    (show -(n : ℝ) ≤ n by have := Nat.cast_nonneg (α := ℝ) n; linarith)]
  have he : (fun x => w (x+h)-w x) = fun x => |w (x+h)-w x| := by
    funext x
    exact (abs_of_nonneg (sub_nonneg.mpr (hw (by linarith)))).symm
  rw [he]
  exact monotone_translate_interval_bound hw hb hh _ _

theorem boundedVariation_translation_sq {f : ℝ → ℝ}
    (hf : BoundedVariationOn f univ) {h : ℝ} (hh : 0 ≤ h) :
    Integrable (fun x => (f x-f (x+h))^2) ∧
      (∫ x, (f x-f (x+h))^2) ≤
        4 * (‖f 0‖ + (eVariationOn f univ).toReal) *
          (eVariationOn f univ).toReal * h := by
  let V := (eVariationOn f univ).toReal
  let B := ‖f 0‖ + V
  let w := variationOnFromTo f univ 0
  have hw : Monotone w := monotoneOn_univ.mp
    (variationOnFromTo.monotoneOn hf.locallyBoundedVariationOn (mem_univ 0))
  have hb : ∀ x, |w x| ≤ V := fun _ => variationOnFromTo.abs_le_eVariationOn hf
  have hi := integrable_monotone_translate_sub hw hb hh
  have hm := measurable_of_boundedVariation_univ hf
  have hB : 0 ≤ B := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hdom (x : ℝ) : (f x-f (x+h))^2 ≤ (2*B)*(w (x+h)-w x) := by
    have hd := variationOnFromTo.abs_sub_le_sub_of_le hf.locallyBoundedVariationOn
      (mem_univ 0) (mem_univ x) (mem_univ (x+h)) (show x ≤ x+h by linarith)
    have hnorm : |f x-f (x+h)| ≤ 2*B := by
      have hx := norm_le_of_boundedVariation_univ hf x
      have hy := norm_le_of_boundedVariation_univ hf (x+h)
      have ht := norm_sub_le (f x) (f (x+h))
      simpa only [Real.norm_eq_abs] using ht.trans (by dsimp [B, V] at *; linarith)
    rw [abs_sub_comm] at hd
    have hp := mul_le_mul hnorm hd (abs_nonneg _) (mul_nonneg (by positivity) hB)
    nlinarith [sq_abs (f x-f (x+h))]
  have hisq : Integrable (fun x => (f x-f (x+h))^2) := by
    apply (hi.const_mul (2*B)).mono'
      ((hm.sub (hm.comp (measurable_id.add_const h))).pow_const 2).aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hdom x
  refine ⟨hisq, ?_⟩
  calc
    _ ≤ ∫ x, (2*B)*(w (x+h)-w x) := integral_mono hisq (hi.const_mul _) hdom
    _ = (2*B)*∫ x, w (x+h)-w x := integral_const_mul _ _
    _ ≤ (2*B)*((2*V)*h) := mul_le_mul_of_nonneg_left
      (integral_monotone_translate_sub_le hw hb hh) (mul_nonneg (by positivity) hB)
    _ = _ := by dsimp [B, V]; ring

end GaloisForLFunctions.HTGeometry
