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

/-- **The exceptional-set split over an arbitrary measurable outer set.**  The window version of
`Sieve/ExceptionalSplitGen` is the case `S = Icc (-W) W`; §4 also needs it on the annulus, because
the Route-T bound for the long prime blocks is only available away from the origin. -/
theorem setIntegral_normSq_mul_split_exceptional_set {F G : ℝ → ℂ} (hF : Continuous F)
    (hG : Continuous G) {S : Set ℝ} (hSm : MeasurableSet S) {W V Bf : ℝ}
    (hSs : S ⊆ Set.Icc (-W) W) (hBf : ∀ w : ℝ, ‖F w‖ ≤ Bf) :
    (∫ w in S, ‖F w‖ ^ 2 * ‖G w‖ ^ 2)
      ≤ V ^ 2 * (∫ w in S, ‖G w‖ ^ 2)
        + Bf ^ 2 * ∫ w in S ∩ {w : ℝ | V ≤ ‖F w‖}, ‖G w‖ ^ 2 := by
  classical
  set E : Set ℝ := {w : ℝ | V ≤ ‖F w‖} with hE
  set f : ℝ → ℝ := fun w => ‖G w‖ ^ 2 with hf
  set g : ℝ → ℝ := fun w => ‖F w‖ ^ 2 * ‖G w‖ ^ 2 with hg
  have hcF : Continuous fun w : ℝ => ‖F w‖ := hF.norm
  have hcf : Continuous f := (hG.norm).pow 2
  have hcg : Continuous g := (hcF.pow 2).mul hcf
  have hEmeas : MeasurableSet E := measurableSet_le measurable_const hcF.measurable
  have hgS : IntegrableOn g S := (hcg.integrableOn_Icc (a := -W) (b := W)).mono_set hSs
  have hfS : IntegrableOn (fun w => V ^ 2 * f w) S :=
    (((hcf.const_mul (V ^ 2)).integrableOn_Icc (a := -W) (b := W))).mono_set hSs
  have hbfS : IntegrableOn (fun w => Bf ^ 2 * f w) S :=
    (((hcf.const_mul (Bf ^ 2)).integrableOn_Icc (a := -W) (b := W))).mono_set hSs
  have hsplit : (∫ w in S ∩ E, g w) + (∫ w in S \ E, g w) = ∫ w in S, g w :=
    MeasureTheory.integral_inter_add_sdiff hEmeas hgS
  have hsplit2 : (∫ w in S ∩ E, V ^ 2 * f w) + (∫ w in S \ E, V ^ 2 * f w)
      = ∫ w in S, V ^ 2 * f w :=
    MeasureTheory.integral_inter_add_sdiff hEmeas hfS
  have hbig : (∫ w in S ∩ E, g w) ≤ Bf ^ 2 * ∫ w in S ∩ E, f w := by
    have hmeas : MeasurableSet (S ∩ E) := hSm.inter hEmeas
    have hint : IntegrableOn g (S ∩ E) := hgS.mono_set Set.inter_subset_left
    have hint2 : IntegrableOn (fun w => Bf ^ 2 * f w) (S ∩ E) :=
      hbfS.mono_set Set.inter_subset_left
    have hle : ∀ w ∈ S ∩ E, g w ≤ Bf ^ 2 * f w := by
      intro w _
      have h1 : ‖F w‖ ^ 2 ≤ Bf ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hBf w) 2
      have h2n : (0 : ℝ) ≤ f w := by rw [hf]; positivity
      calc g w = ‖F w‖ ^ 2 * f w := rfl
        _ ≤ Bf ^ 2 * f w := by nlinarith
    have hmono := MeasureTheory.setIntegral_mono_on hint hint2 hmeas hle
    rwa [MeasureTheory.integral_const_mul] at hmono
  have hsmall : (∫ w in S \ E, g w) ≤ ∫ w in S \ E, V ^ 2 * f w := by
    have hmeas : MeasurableSet (S \ E) := hSm.diff hEmeas
    have hint : IntegrableOn g (S \ E) := hgS.mono_set Set.sdiff_subset
    have hint2 : IntegrableOn (fun w => V ^ 2 * f w) (S \ E) := hfS.mono_set Set.sdiff_subset
    refine MeasureTheory.setIntegral_mono_on hint hint2 hmeas ?_
    intro w hw
    have hlt : ‖F w‖ < V := by
      by_contra hcon
      exact hw.2 (not_lt.1 hcon)
    have h1 : ‖F w‖ ^ 2 ≤ V ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hlt.le 2
    have h2n : (0 : ℝ) ≤ f w := by rw [hf]; positivity
    calc g w = ‖F w‖ ^ 2 * f w := rfl
      _ ≤ V ^ 2 * f w := by nlinarith
  have hdrop : (0 : ℝ) ≤ ∫ w in S ∩ E, V ^ 2 * f w := by
    refine MeasureTheory.setIntegral_nonneg (hSm.inter hEmeas) fun w _ => ?_
    have hfn : (0 : ℝ) ≤ f w := by rw [hf]; positivity
    nlinarith [sq_nonneg V]
  have hVf : (∫ w in S, V ^ 2 * f w) = V ^ 2 * ∫ w in S, f w :=
    MeasureTheory.integral_const_mul _ _
  linarith [hsplit, hbig, hsmall, hdrop, hsplit2, hVf]

end

end RHTower.Sieve
