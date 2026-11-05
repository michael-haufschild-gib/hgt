import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheReciprocalLogarithmicFactorHasItsPositiveMeasure

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The positive logarithmic causal kernel

The reciprocal factor's positive Stieltjes measure gives an exponential mixture.
Fubini identifies its Laplace transform; the unit factor limit fixes its total mass.
-/

open MeasureTheory Set Filter Topology
noncomputable section

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower

/-- The positive causal kernel whose Laplace transform is the reciprocal logarithmic factor. -/
def logarithmicCausalKernel (x : ℝ) : ℝ :=
  if 0 < x then logarithmicFactorReciprocalResidue * Real.exp (-logarithmicFactorZeroRadius * x) +
    ∫ t in Ioi (1 : ℝ), logarithmicFactorCutDensity t * Real.exp (-t * x)
  else 0

/-- The renewal mass fixes the normalization of logarithmic boundary traces. -/
def logarithmicRenewalMass (x : ℝ) : ℝ :=
  ∫ y in Ioc (0 : ℝ) x, logarithmicCausalKernel y

theorem logarithmicCausalKernel_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    logarithmicCausalKernel x = 0 := if_neg (not_lt.mpr hx)

theorem logarithmicCausalKernel_pos {x : ℝ} (hx : 0 < x) : 0 < logarithmicCausalKernel x := by
  rw [logarithmicCausalKernel, if_pos hx]
  apply add_pos_of_pos_of_nonneg
  · exact mul_pos logarithmicFactorReciprocalResidue_pos (Real.exp_pos _)
  · exact integral_nonneg fun t => mul_nonneg (logarithmicFactorCutDensity_pos t).le (Real.exp_pos _).le

theorem logarithmicCausalKernel_nonneg (x : ℝ) : 0 ≤ logarithmicCausalKernel x := by
  rcases lt_or_ge 0 x with hx | hx
  · exact (logarithmicCausalKernel_pos hx).le
  · rw [logarithmicCausalKernel_of_nonpos hx]

/-- Bounded cut density gives a finite exponential mixture at every positive point. -/
theorem integrableOn_logarithmicCausalMixture {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => logarithmicFactorCutDensity t * Real.exp (-t * x)) (Ioi (1 : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := logarithmicFactorCutDensity_bounded
  have hM := (exp_neg_integrableOn_Ioi (1 : ℝ) hx).const_mul C
  have hc : ContinuousOn (fun t : ℝ => logarithmicFactorCutDensity t * Real.exp (-t * x))
      (Ioi (1 : ℝ)) := continuousOn_logarithmicFactorCutDensity.mul (by fun_prop)
  apply hM.mono' (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_of_nonneg (mul_nonneg (logarithmicFactorCutDensity_pos t).le (Real.exp_pos _).le)]
  have he : -t * x = -x * t := by ring
  rw [he]
  exact mul_le_mul_of_nonneg_right (hb t ht) (Real.exp_pos _).le

private theorem integral_logarithmic_exponential {r : ℝ} (hr : 0 < r) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-r * x)) = 1 / r := by
  simpa only [mul_zero, Real.exp_zero, neg_div_neg_eq] using
    integral_exp_mul_Ioi (neg_neg_of_pos hr) (0 : ℝ)

private theorem integral_logarithmicLaplaceMixture_section {s t : ℝ} (hst : 0 < s + t) :
    (∫ x in Ioi (0 : ℝ), logarithmicFactorCutDensity t * Real.exp (-(s + t) * x)) =
      logarithmicFactorCutDensity t / (s + t) := by
  rw [integral_const_mul, integral_logarithmic_exponential hst]
  ring

/-- The Stieltjes formula supplies precisely the joint integrability needed for Fubini. -/
theorem integrable_logarithmicLaplaceMixture {s : ℝ} (hs : 0 < s) :
    Integrable (fun p : ℝ × ℝ => logarithmicFactorCutDensity p.1 * Real.exp (-(s + p.1) * p.2))
      ((volume.restrict (Ioi (1 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hm : AEStronglyMeasurable logarithmicFactorCutDensity (volume.restrict (Ioi (1 : ℝ))) :=
    continuousOn_logarithmicFactorCutDensity.aestronglyMeasurable measurableSet_Ioi
  have he : Continuous (fun p : ℝ × ℝ => Real.exp (-(s + p.1) * p.2)) := by fun_prop
  apply (integrable_prod_iff (hm.comp_fst.mul he.aestronglyMeasurable)).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change (1 : ℝ) < t at ht
    exact (exp_neg_integrableOn_Ioi (0 : ℝ) (show 0 < s + t by linarith only [hs, ht])).const_mul
      (logarithmicFactorCutDensity t)
  · apply (logarithmic_stieltjes_integral hs).1.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change (1 : ℝ) < t at ht
    have hst : 0 < s + t := by linarith only [hs, ht]
    have hn (x : ℝ) : ‖logarithmicFactorCutDensity t * Real.exp (-(s + t) * x)‖ =
        logarithmicFactorCutDensity t * Real.exp (-(s + t) * x) :=
      Real.norm_of_nonneg (mul_nonneg (logarithmicFactorCutDensity_pos t).le (Real.exp_pos _).le)
    change logarithmicFactorCutDensity t / (t + s) =
      ∫ x in Ioi (0 : ℝ), ‖logarithmicFactorCutDensity t * Real.exp (-(s + t) * x)‖
    simp_rw [hn]
    rw [integral_logarithmicLaplaceMixture_section hst, add_comm s]

/-- The positive causal kernel has the actual reciprocal factor as its Laplace transform. -/
theorem logarithmicCausalKernel_laplace {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun x : ℝ => Real.exp (-s * x) * logarithmicCausalKernel x) (Ioi (0 : ℝ)) ∧
    (∫ x in Ioi (0 : ℝ), Real.exp (-s * x) * logarithmicCausalKernel x) = (logReferenceFactor s)⁻¹ := by
  let f : ℝ → ℝ → ℝ := fun t x => logarithmicFactorCutDensity t * Real.exp (-(s + t) * x)
  have hf : Integrable (Function.uncurry f)
      ((volume.restrict (Ioi (1 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    integrable_logarithmicLaplaceMixture hs
  have hmix : IntegrableOn (fun x : ℝ => ∫ t in Ioi (1 : ℝ), f t x) (Ioi (0 : ℝ)) :=
    hf.integral_prod_right
  have hsb : 0 < s + logarithmicFactorZeroRadius := add_pos hs logarithmicFactorZeroRadius_pos
  have hatom : IntegrableOn (fun x : ℝ => logarithmicFactorReciprocalResidue *
      Real.exp (-(s + logarithmicFactorZeroRadius) * x)) (Ioi (0 : ℝ)) :=
    (exp_neg_integrableOn_Ioi (0 : ℝ) hsb).const_mul logarithmicFactorReciprocalResidue
  have he (x : ℝ) (hx : 0 < x) : Real.exp (-s * x) * logarithmicCausalKernel x =
      logarithmicFactorReciprocalResidue * Real.exp (-(s + logarithmicFactorZeroRadius) * x) +
        ∫ t in Ioi (1 : ℝ), f t x := by
    rw [logarithmicCausalKernel, if_pos hx, mul_add]
    congr 1
    · rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    · rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      dsimp only [f]
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
  have hint : IntegrableOn (fun x : ℝ => Real.exp (-s * x) * logarithmicCausalKernel x) (Ioi (0 : ℝ)) :=
    (hatom.add hmix).congr (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact (he x hx).symm)
  refine ⟨hint, ?_⟩
  calc
    _ = ∫ x in Ioi (0 : ℝ), logarithmicFactorReciprocalResidue *
        Real.exp (-(s + logarithmicFactorZeroRadius) * x) + ∫ t in Ioi (1 : ℝ), f t x := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact he x hx
    _ = (∫ x in Ioi (0 : ℝ), logarithmicFactorReciprocalResidue *
        Real.exp (-(s + logarithmicFactorZeroRadius) * x)) +
          ∫ x in Ioi (0 : ℝ), ∫ t in Ioi (1 : ℝ), f t x := integral_add hatom hmix
    _ = logarithmicFactorReciprocalResidue / (s + logarithmicFactorZeroRadius) +
        ∫ t in Ioi (1 : ℝ), ∫ x in Ioi (0 : ℝ), f t x := by
      rw [integral_const_mul, integral_logarithmic_exponential hsb,
        ← integral_integral_swap hf]
      ring
    _ = logarithmicFactorReciprocalResidue / (s + logarithmicFactorZeroRadius) +
        ∫ t in Ioi (1 : ℝ), logarithmicFactorCutDensity t / (s + t) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      change (1 : ℝ) < t at ht
      exact integral_logarithmicLaplaceMixture_section (by linarith only [hs, ht])
    _ = _ := (logReferenceFactor_reciprocal_stieltjes hs).symm

/-- The causal kernel has total mass one; the unit factor limit fixes the normalization. -/
theorem logarithmicCausalKernel_mass_one :
    Integrable logarithmicCausalKernel ∧ (∫ x : ℝ, logarithmicCausalKernel x) = 1 := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let q : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let f : ℕ → ℝ → ℝ := fun n x => Real.exp (-q n * x) * logarithmicCausalKernel x
  have hqpos (n : ℕ) : 0 < q n := by dsimp only [q]; positivity
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have hqzero : Tendsto q atTop (nhds (0 : ℝ)) := by
    simpa only [q, one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hnat
  have hqwithin : Tendsto q atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hqzero, Eventually.of_forall hqpos⟩
  have hSint : ∀ n, Integrable (f n) μ := fun n => (logarithmicCausalKernel_laplace (hqpos n)).1
  have hnonneg (n : ℕ) (x : ℝ) : 0 ≤ f n x :=
    mul_nonneg (Real.exp_pos _).le (logarithmicCausalKernel_nonneg x)
  have hmono : ∀ᵐ x ∂μ, Monotone (fun n => f n x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change (0 : ℝ) < x at hx
    intro n m hnm
    apply mul_le_mul_of_nonneg_right _ (logarithmicCausalKernel_nonneg x)
    apply Real.exp_le_exp.mpr
    have hq : q m ≤ q n := by
      apply one_div_le_one_div_of_le (by positivity)
      have hnm' : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
      linarith only [hnm']
    have hm := mul_le_mul_of_nonneg_right hq hx.le
    linarith only [hm]
  have hpoint : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (nhds (logarithmicCausalKernel x)) := by
    filter_upwards with x
    have he := Real.continuous_exp.continuousAt.tendsto.comp (hqzero.neg.mul_const x)
    simpa only [f, neg_zero, zero_mul, Real.exp_zero, one_mul] using!
      he.mul (tendsto_const_nhds (x := logarithmicCausalKernel x))
  have hK := tendsto_logReferenceFactor_at_zero.comp hqwithin
  have hInv := hK.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  rw [inv_one] at hInv
  have hint : Tendsto (fun n => ∫ x, f n x ∂μ) atTop (nhds 1) := by
    apply hInv.congr'
    exact Eventually.of_forall fun n => (logarithmicCausalKernel_laplace (hqpos n)).2.symm
  have hnormeq (n : ℕ) : (∫⁻ x, ‖f n x‖ₑ ∂μ) = ENNReal.ofReal (∫ x, f n x ∂μ) := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hSint n)]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun x => Real.norm_of_nonneg (hnonneg n x))
  have hlin : Tendsto (fun n => ∫⁻ x, ‖f n x‖ₑ ∂μ) atTop (nhds (ENNReal.ofReal 1)) := by
    simp_rw [hnormeq]
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hint
  have hfinite : liminf (fun n => ∫⁻ x, ‖f n x‖ₑ ∂μ) atTop ≠ ⊤ := by
    rw [hlin.liminf_eq]
    exact ENNReal.ofReal_ne_top
  have hF : Integrable logarithmicCausalKernel μ :=
    integrable_of_tendsto hpoint (fun n => (hSint n).aestronglyMeasurable) hfinite
  have hmass : (∫ x, logarithmicCausalKernel x ∂μ) = 1 :=
    tendsto_nhds_unique (integral_tendsto_of_tendsto_of_monotone hSint hF hmono hpoint) hint
  have heq : (Ioi (0 : ℝ)).indicator logarithmicCausalKernel = logarithmicCausalKernel := by
    funext x
    by_cases hx : 0 < x
    · exact indicator_of_mem (s := Ioi (0 : ℝ)) hx _
    · rw [indicator_of_notMem (s := Ioi (0 : ℝ)) hx, logarithmicCausalKernel_of_nonpos (le_of_not_gt hx)]
  have hfull : Integrable logarithmicCausalKernel := by
    have h := (integrable_indicator_iff measurableSet_Ioi).mpr hF
    rwa [heq] at h
  refine ⟨hfull, ?_⟩
  rw [← heq, integral_indicator measurableSet_Ioi]
  exact hmass

/-- The causal kernel is continuous at every positive point. -/
theorem continuousOn_logarithmicCausalKernel : ContinuousOn logarithmicCausalKernel (Ioi (0 : ℝ)) := by
  intro x hx
  change (0 : ℝ) < x at hx
  obtain ⟨C, hC, hb⟩ := logarithmicFactorCutDensity_bounded
  have hmix : ContinuousAt (fun y : ℝ => ∫ t in Ioi (1 : ℝ),
      logarithmicFactorCutDensity t * Real.exp (-t * y)) x := by
    apply tendsto_integral_filter_of_dominated_convergence (fun t : ℝ => C * Real.exp (-(x / 2) * t))
    · exact Eventually.of_forall fun y =>
        (continuousOn_logarithmicFactorCutDensity.mul (by fun_prop)).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [eventually_gt_nhds (show x / 2 < x by linarith only [hx])] with y hy
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      change (1 : ℝ) < t at ht
      rw [Real.norm_of_nonneg (mul_nonneg (logarithmicFactorCutDensity_pos t).le (Real.exp_pos _).le)]
      have he : Real.exp (-t * y) ≤ Real.exp (-(x / 2) * t) := by
        apply Real.exp_le_exp.mpr
        have hp := mul_le_mul_of_nonneg_left hy.le (show 0 ≤ t by linarith only [ht])
        linarith only [hp]
      exact mul_le_mul (hb t ht) he (Real.exp_pos _).le hC.le
    · exact (exp_neg_integrableOn_Ioi (1 : ℝ) (by linarith only [hx] : 0 < x / 2)).const_mul C
    · filter_upwards with t
      have hc : Continuous (fun y : ℝ => logarithmicFactorCutDensity t * Real.exp (-t * y)) := by fun_prop
      exact hc.continuousAt.tendsto
  have hatom : ContinuousAt (fun y : ℝ => logarithmicFactorReciprocalResidue *
      Real.exp (-logarithmicFactorZeroRadius * y)) x := by fun_prop
  have hfull : ContinuousAt logarithmicCausalKernel x := by
    change Tendsto logarithmicCausalKernel (nhds x) (nhds (logarithmicCausalKernel x))
    rw [logarithmicCausalKernel, if_pos hx]
    apply (hatom.tendsto.add hmix.tendsto).congr'
    filter_upwards [eventually_gt_nhds hx] with y hy
    simp only [logarithmicCausalKernel, if_pos hy]
  exact hfull.continuousWithinAt

/-- Positivity of the representing measure makes the causal kernel decreasing. -/
theorem antitoneOn_logarithmicCausalKernel : AntitoneOn logarithmicCausalKernel (Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  change (0 : ℝ) < x at hx
  change (0 : ℝ) < y at hy
  simp only [logarithmicCausalKernel, if_pos hx, if_pos hy]
  have hatom : logarithmicFactorReciprocalResidue * Real.exp (-logarithmicFactorZeroRadius * y) ≤
      logarithmicFactorReciprocalResidue * Real.exp (-logarithmicFactorZeroRadius * x) := by
    apply mul_le_mul_of_nonneg_left _ logarithmicFactorReciprocalResidue_pos.le
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hxy logarithmicFactorZeroRadius_pos.le
    linarith only [h]
  have hmix : (∫ t in Ioi (1 : ℝ), logarithmicFactorCutDensity t * Real.exp (-t * y)) ≤
      ∫ t in Ioi (1 : ℝ), logarithmicFactorCutDensity t * Real.exp (-t * x) := by
    apply integral_mono_ae (integrableOn_logarithmicCausalMixture hy) (integrableOn_logarithmicCausalMixture hx)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change (1 : ℝ) < t at ht
    apply mul_le_mul_of_nonneg_left _ (logarithmicFactorCutDensity_pos t).le
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hxy (show 0 ≤ t by linarith only [ht])
    linarith only [h]
  linarith only [hatom, hmix]

#print axioms continuousOn_logarithmicCausalKernel
#print axioms antitoneOn_logarithmicCausalKernel
#print axioms logarithmicCausalKernel_mass_one
#print axioms logarithmicCausalKernel_laplace

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
