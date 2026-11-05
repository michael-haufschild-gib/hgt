import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.ArchimedeanTailsHaveBoundedOffDiagonalAction

/-!
The cutoff archimedean kernel has row mass tending uniformly to infinity on
compact intervals. The explicit Lévy primitive gives the logarithmic divergence;
positivity of the theta kernel makes the lower bound uniform in the source point.
-/

open MeasureTheory Set
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower

open _root_.RHTower _root_.RHTower.CHMDDoobGraph _root_.RHTower.CHMDPolar
open _root_.RHTower.WeilLevyPoleGauss

/-- The archimedean Lévy density has infinite mass at the origin. -/
theorem archimedean_tail_integral_unbounded (C : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ C < ∫ t in δ..1, archLevyDensity t := by
  let L := 2 * (|C| + |archLevyAntideriv 1|) + 2
  let δ := Real.exp (-L)
  have hL : 0 < L := by dsimp only [L]; positivity
  have hδ : 0 < δ := Real.exp_pos _
  have hδ1 : δ < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hL)
  have hΩ := log_four_sub_div_le_two_mul_archLevyAntideriv hδ (hδ1.trans (by norm_num))
  have hquot : 1 / δ ≤ (4 - δ) / δ :=
    div_le_div_of_nonneg_right (by linarith only [hδ1]) hδ.le
  have hlog := Real.log_le_log (by positivity : 0 < 1 / δ) hquot
  have hlogδ : Real.log (1 / δ) = L := by
    rw [one_div, Real.log_inv]
    change -Real.log (Real.exp (-L)) = L
    rw [Real.log_exp, neg_neg]
  rw [hlogδ] at hlog
  refine ⟨δ, hδ, hδ1, ?_⟩
  rw [integral_archLevyDensity_Icc hδ hδ1.le]
  dsimp only [L] at hlog
  linarith only [hlog, hΩ, le_abs_self C, le_abs_self (archLevyAntideriv 1)]

/-- Total mass of a cutoff kernel row in the Doob source measure. -/
def archTailMass (δ x : ℝ) : ℝ := ∫ y, archTailKernel δ x y ∂massMeasure

theorem archTailMass_nonneg {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    0 ≤ archTailMass δ x := integral_nonneg (archTailKernel_nonneg hδ x)

theorem integrable_massDensity_archTailKernel {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    Integrable (fun y => massDensity y * archTailKernel δ x y) := by
  apply (integrable_weighted_iff volume continuous_massDensity.measurable
    (Filter.Eventually.of_forall fun y => (massDensity_pos y).le) _).mp
  exact (memLp_archTailKernel hδ x).integrable (by norm_num)

theorem massDensity_archTailKernel_translate {δ t : ℝ} (hδ : 0 < δ) (ht : δ ≤ t)
    (x : ℝ) :
    massDensity (x + t) * archTailKernel δ x (x + t) =
      archLevyDensity t * (riemannKernelReal (x + t) / Real.cosh (x / 2)) := by
  have habs : |x - (x + t)| = t := by
    rw [sub_add_cancel_left, abs_neg, abs_of_pos (hδ.trans_le ht)]
  rw [archTailKernel, habs, if_pos ht, massDensity]
  field_simp [ne_of_gt (Real.cosh_pos (x / 2)), ne_of_gt (Real.cosh_pos ((x + t) / 2))]

theorem archTailMass_ge_interval {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (x : ℝ) :
    (∫ t in δ..1,
      archLevyDensity t * (riemannKernelReal (x + t) / Real.cosh (x / 2))) ≤
        archTailMass δ x := by
  let f := fun y => massDensity y * archTailKernel δ x y
  have hi : Integrable f := integrable_massDensity_archTailKernel hδ x
  have hnonneg (y : ℝ) : 0 ≤ f y :=
    mul_nonneg (massDensity_pos y).le (archTailKernel_nonneg hδ x y)
  have hshift : (∫ t in δ..1, f (x + t)) = ∫ y in x + δ..x + 1, f y :=
    intervalIntegral.integral_comp_add_left f x
  have heq : (∫ t in δ..1, f (x + t)) =
      ∫ t in δ..1,
        archLevyDensity t * (riemannKernelReal (x + t) / Real.cosh (x / 2)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hδ1] at ht
    exact massDensity_archTailKernel_translate hδ ht.1 x
  have hends : x + δ ≤ x + 1 := by linarith only [hδ1]
  rw [← heq, hshift, intervalIntegral.integral_of_le hends]
  rw [archTailMass, massMeasure, integral_weighted volume continuous_massDensity.measurable
    (Filter.Eventually.of_forall fun y => (massDensity_pos y).le)]
  exact setIntegral_le_integral hi (Filter.Eventually.of_forall hnonneg)

theorem compact_theta_cosh_ratio_lower (a : ℝ) :
    ∃ m : ℝ, 0 < m ∧ ∀ x t : ℝ, |x| ≤ a → 0 ≤ t → t ≤ 1 →
      m ≤ riemannKernelReal (x + t) / Real.cosh (x / 2) := by
  let K : Set (ℝ × ℝ) := Icc (-a) a ×ˢ Icc (-(a + 1)) (a + 1)
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hc : Continuous (fun p : ℝ × ℝ =>
      riemannKernelReal p.2 / Real.cosh (p.1 / 2)) :=
    (continuous_riemannKernelReal.comp continuous_snd).div (by fun_prop)
      (fun p => (Real.cosh_pos (p.1 / 2)).ne')
  obtain ⟨m, hm, hmin⟩ := hK.exists_forall_le' hc.continuousOn
    (fun p _ => div_pos (riemannKernelReal_pos _) (Real.cosh_pos _))
  refine ⟨m, hm, fun x t hx ht ht1 => hmin (x, x + t) ?_⟩
  have hxb := abs_le.mp hx
  exact ⟨hxb, ⟨by linarith only [hxb.1, ht], by linarith only [hxb.2, ht1]⟩⟩

/-- Every compact source interval admits a common cutoff with arbitrarily large row mass. -/
theorem archTailMass_uniformly_unbounded (a C : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ x : ℝ, |x| ≤ a → C < archTailMass δ x := by
  obtain ⟨m, hm, hmin⟩ := compact_theta_cosh_ratio_lower a
  obtain ⟨δ, hδ, hδ1, hlarge⟩ := archimedean_tail_integral_unbounded (C / m)
  refine ⟨δ, hδ, hδ1, fun x hx => ?_⟩
  have hω : IntervalIntegrable archLevyDensity volume δ 1 :=
    (continuousOn_archLevyDensity.mono (by
      intro t ht
      rw [uIcc_of_le hδ1.le] at ht
      exact hδ.trans_le ht.1)).intervalIntegrable
  have hratio : Continuous (fun t : ℝ =>
      riemannKernelReal (x + t) / Real.cosh (x / 2)) :=
    (continuous_riemannKernelReal.comp (continuous_const.add continuous_id)).div_const _
  have hprod : IntervalIntegrable (fun t : ℝ =>
      archLevyDensity t * (riemannKernelReal (x + t) / Real.cosh (x / 2))) volume δ 1 :=
    ((continuousOn_archLevyDensity.mono (by
      intro t ht
      rw [uIcc_of_le hδ1.le] at ht
      exact hδ.trans_le ht.1)).mul hratio.continuousOn).intervalIntegrable
  have hcmp : m * (∫ t in δ..1, archLevyDensity t) ≤
      ∫ t in δ..1,
        archLevyDensity t * (riemannKernelReal (x + t) / Real.cosh (x / 2)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hδ1.le (hω.const_mul m) hprod
    intro t ht
    have ht0 := hδ.trans_le ht.1
    simpa only [mul_comm m] using
      mul_le_mul_of_nonneg_left (hmin x t hx ht0.le ht.2) (archLevyDensity_pos ht0).le
  have hc : C < m * (∫ t in δ..1, archLevyDensity t) := by
    have h := (div_lt_iff₀ hm).mp hlarge
    simpa only [mul_comm m] using h
  exact hc.trans_le (hcmp.trans (archTailMass_ge_interval hδ hδ1.le x))

#print axioms archimedean_tail_integral_unbounded
#print axioms archTailMass_uniformly_unbounded

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
