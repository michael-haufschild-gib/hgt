import GaloisForLFunctions.RHTower.Sieve.HarmonicCauchySchwarz
import GaloisForLFunctions.RHTower.Sieve.ExceptionalSplitGen

/-!
# Splitting a product of polynomials over a measurable set

The exceptional case of exposé §4 works over a measurable subset `E` of the window, not over the
window itself: the whole point is that `E` is small.  The two operations the argument performs
there — the harmonic Cauchy–Schwarz over a family of products, and the replacement of one factor by
a pointwise bound — are recorded here in `∫_E` form.

Both are `setIntegral_mono_on` applied to a pointwise inequality; integrability is free because the
integrands are continuous and `E` sits inside a compact interval.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- **The harmonic split of a family of products, over a measurable set.** -/
theorem setIntegral_normSq_sum_mul_le_weighted {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (v : ι → ℝ) (hv : ∀ i ∈ I, 0 < v i) (F G : ι → ℝ → ℂ)
    (hF : ∀ i, Continuous (F i)) (hG : ∀ i, Continuous (G i))
    {E : Set ℝ} (hEm : MeasurableSet E) {W : ℝ} (hEs : E ⊆ Set.Icc (-W) W) :
    (∫ w in E, ‖∑ i ∈ I, F i w * G i w‖ ^ 2)
      ≤ (∑ i ∈ I, 1 / v i)
        * ∑ i ∈ I, v i * ∫ w in E, ‖F i w‖ ^ 2 * ‖G i w‖ ^ 2 := by
  classical
  set H : ι → ℝ → ℝ := fun i w => ‖F i w‖ ^ 2 * ‖G i w‖ ^ 2 with hH
  have hcontH : ∀ i : ι, Continuous (H i) := fun i =>
    (((hF i).norm).pow 2).mul (((hG i).norm).pow 2)
  have hcontZ : Continuous fun w : ℝ => ‖∑ i ∈ I, F i w * G i w‖ ^ 2 :=
    ((continuous_finsetSum _ fun i _ => (hF i).mul (hG i)).norm).pow 2
  have hcontR : Continuous fun w : ℝ => (∑ i ∈ I, 1 / v i) * ∑ i ∈ I, v i * H i w :=
    (continuous_finsetSum _ fun i _ => (hcontH i).const_mul _).const_mul _
  have hintZ : IntegrableOn (fun w : ℝ => ‖∑ i ∈ I, F i w * G i w‖ ^ 2) E volume :=
    (hcontZ.integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hintR : IntegrableOn
      (fun w : ℝ => (∑ i ∈ I, 1 / v i) * ∑ i ∈ I, v i * H i w) E volume :=
    (hcontR.integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hmono := setIntegral_mono_on hintZ hintR hEm
    (fun w _ => normSq_sum_mul_le_weighted I v hv (fun i => F i w) (fun i => G i w))
  refine hmono.trans (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul]
  congr 1
  rw [integral_finsetSum _ fun i _ =>
    (((hcontH i).const_mul (v i)).integrableOn_Icc (a := -W) (b := W)).mono_set hEs]
  exact Finset.sum_congr rfl fun i _ => MeasureTheory.integral_const_mul _ _

/-- **Replacing the first factor by a pointwise bound, over a measurable set.** -/
theorem setIntegral_normSq_mul_le_of_bound {F G : ℝ → ℂ} (hF : Continuous F) (hG : Continuous G)
    {E : Set ℝ} (hEm : MeasurableSet E) {W V : ℝ} (hEs : E ⊆ Set.Icc (-W) W)
    (hV : ∀ w ∈ E, ‖F w‖ ≤ V) :
    (∫ w in E, ‖F w‖ ^ 2 * ‖G w‖ ^ 2) ≤ V ^ 2 * ∫ w in E, ‖G w‖ ^ 2 := by
  classical
  have hcontZ : Continuous fun w : ℝ => ‖F w‖ ^ 2 * ‖G w‖ ^ 2 :=
    ((hF.norm).pow 2).mul ((hG.norm).pow 2)
  have hcontR : Continuous fun w : ℝ => V ^ 2 * ‖G w‖ ^ 2 := ((hG.norm).pow 2).const_mul _
  have hintZ : IntegrableOn (fun w : ℝ => ‖F w‖ ^ 2 * ‖G w‖ ^ 2) E volume :=
    (hcontZ.integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hintR : IntegrableOn (fun w : ℝ => V ^ 2 * ‖G w‖ ^ 2) E volume :=
    (hcontR.integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hmono := setIntegral_mono_on hintZ hintR hEm (fun w hw => by
    have h1 : ‖F w‖ ^ 2 ≤ V ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hV w hw) 2
    have h2 : (0 : ℝ) ≤ ‖G w‖ ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_right h1 h2)
  rwa [MeasureTheory.integral_const_mul] at hmono

/-- **Splitting a sum into two pieces, over a measurable set.** -/
theorem setIntegral_normSq_add_le {F G : ℝ → ℂ} (hF : Continuous F) (hG : Continuous G)
    {E : Set ℝ} (hEm : MeasurableSet E) {W : ℝ} (hEs : E ⊆ Set.Icc (-W) W) :
    (∫ w in E, ‖F w + G w‖ ^ 2)
      ≤ 2 * (∫ w in E, ‖F w‖ ^ 2) + 2 * ∫ w in E, ‖G w‖ ^ 2 := by
  classical
  have hcontZ : Continuous fun w : ℝ => ‖F w + G w‖ ^ 2 := ((hF.add hG).norm).pow 2
  have hcontF : Continuous fun w : ℝ => ‖F w‖ ^ 2 := ((hF.norm).pow 2)
  have hcontG : Continuous fun w : ℝ => ‖G w‖ ^ 2 := ((hG.norm).pow 2)
  have hintZ : IntegrableOn (fun w : ℝ => ‖F w + G w‖ ^ 2) E volume :=
    (hcontZ.integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hintF : IntegrableOn (fun w : ℝ => ‖F w‖ ^ 2) E volume :=
    (hcontF.integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hintG : IntegrableOn (fun w : ℝ => ‖G w‖ ^ 2) E volume :=
    (hcontG.integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hintR : IntegrableOn (fun w : ℝ => 2 * ‖F w‖ ^ 2 + 2 * ‖G w‖ ^ 2) E volume :=
    ((hintF.const_mul 2).add (hintG.const_mul 2))
  have hmono := setIntegral_mono_on hintZ hintR hEm (fun w _ => by
    have h := norm_add_le (F w) (G w)
    have h0 : (0 : ℝ) ≤ ‖F w + G w‖ := norm_nonneg _
    have hsq : ‖F w + G w‖ ^ 2 ≤ (‖F w‖ + ‖G w‖) ^ 2 := by nlinarith [h, h0]
    nlinarith [hsq, sq_nonneg (‖F w‖ - ‖G w‖)])
  rw [MeasureTheory.integral_add (hintF.const_mul 2) (hintG.const_mul 2),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hmono
  exact hmono

end

end RHTower.Sieve
