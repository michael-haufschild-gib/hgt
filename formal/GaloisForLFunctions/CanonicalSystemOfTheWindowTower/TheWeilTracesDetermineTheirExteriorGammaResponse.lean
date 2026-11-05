import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilTracesDetermineTheirTruncatedExteriorIntegrals
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilGammaBoundaryPairing

/-!
# Exterior Gamma response of the actual normalized Weil trace

On a fixed finite interval, the displaced logarithmic kernel differs from
its truncated principal kernel by a uniformly bounded integral. The Gamma
remainder is bounded as well. Thus the normalized interior trace gives the
exact leading exterior Gamma response of each actual Weil Riesz source.
-/

open MeasureTheory Set Filter Topology Complex
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open _root_.RHTower HTGeometry

private theorem reference_density_bounds {t : ℝ} (ht : 0 < t) :
    0 ≤ logReferenceLevyDensity t ∧ logReferenceLevyDensity t ≤ 1 / (2*t) := by
  unfold logReferenceLevyDensity
  exact ⟨div_nonneg (Real.exp_pos _).le (by positivity),
    div_le_div_of_nonneg_right (Real.exp_le_one_iff.mpr (by linarith only [ht])) (by positivity)⟩

private theorem reference_density_middle_bound {t d : ℝ} (ht : 0 < t) (hd : 0 < d) :
    0 ≤ 1/(2*t) - logReferenceLevyDensity (t+d) ∧
      1/(2*t) - logReferenceLevyDensity (t+d) ≤ 1/2 + d/(2*t^2) := by
  have htd : 0 < t+d := add_pos ht hd
  have hrec : 1/(2*(t+d)) ≤ 1/(2*t) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith only [hd])
  refine ⟨sub_nonneg.mpr ((reference_density_bounds htd).2.trans hrec), ?_⟩
  have hsplit : 1/(2*t) - logReferenceLevyDensity (t+d) =
      (1-Real.exp (-(t+d)))/(2*(t+d)) + d/(2*t*(t+d)) := by
    unfold logReferenceLevyDensity
    field_simp [ht.ne', htd.ne']; ring
  have hfirst : (1-Real.exp (-(t+d)))/(2*(t+d)) ≤ 1/2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith only [Real.add_one_le_exp (-(t+d))]
  have hsecond : d/(2*t*(t+d)) ≤ d/(2*t^2) := by
    apply div_le_div_of_nonneg_left hd.le (by positivity)
    nlinarith only [mul_nonneg ht.le hd.le]
  rw [hsplit]
  exact add_le_add hfirst hsecond

private theorem integral_inverse_square {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) :
    (∫ t in d..1, 1/t^2) = 1/d - 1 := by
  have hz : (0 : ℝ) ∉ uIcc d 1 := by
    rw [uIcc_of_le hd1]
    exact fun h => (not_le_of_gt hd) h.1
  calc
    _ = ∫ t in d..1, t ^ (-2 : ℤ) := by
      apply intervalIntegral.integral_congr
      intro t _
      norm_num [zpow_neg, zpow_ofNat, one_div]
    _ = _ := by
      rw [integral_zpow (Or.inr ⟨by norm_num, hz⟩),
        show (-2 : ℤ)+1 = -1 by norm_num, zpow_neg_one, zpow_neg_one,
        show ((-2 : ℤ) : ℝ)+1 = -1 by norm_num]
      field_simp [hd.ne']; ring

private theorem continuousOn_reference_integrand {u : ℝ → ℂ} (hu : Continuous u)
    {d : ℝ} (hd : 0 < d) :
    ContinuousOn (fun t : ℝ => (logReferenceLevyDensity (t+d) : ℂ) * u t) (Ici 0) := by
  have hk : ContinuousOn (fun t : ℝ => logReferenceLevyDensity (t+d)) (Ici 0) := by
    unfold logReferenceLevyDensity
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht
    exact ne_of_gt (mul_pos (by norm_num) (add_pos_of_nonneg_of_pos ht hd))
  exact (Complex.continuous_ofReal.comp_continuousOn hk).mul hu.continuousOn

private theorem intervalIntegrable_of_continuousOn_nonneg {f : ℝ → ℂ}
    (hf : ContinuousOn f (Ici 0)) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable f volume a b := by
  apply (hf.mono ?_).intervalIntegrable
  intro t ht
  exact (le_min ha hb).trans ht.1

/-- A displaced logarithmic kernel differs from its truncated principal kernel by bounded mass. -/
theorem logarithmicExteriorIntegral_sub_principal_bound {u : ℝ → ℂ}
    (hu : Continuous u) {B R d : ℝ} (hB : 0 ≤ B) (hb : ∀ t, ‖u t‖ ≤ B)
    (hR : 1 ≤ R) (hd : 0 < d) (hd1 : d ≤ 1) :
    ‖(∫ t in (0 : ℝ)..R, (logReferenceLevyDensity (t+d) : ℂ) * u t) -
      ∫ t in d..1, u t / (2*(t : ℂ))‖ ≤ (2+R)*B := by
  let k : ℝ → ℂ := fun t => (logReferenceLevyDensity (t+d) : ℂ) * u t
  let g : ℝ → ℂ := fun t => u t / (2*(t : ℂ))
  have hk := continuousOn_reference_integrand hu hd
  have hki {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) : IntervalIntegrable k volume r s :=
    intervalIntegrable_of_continuousOn_nonneg hk hr hs
  have hgc : ContinuousOn g (Icc d 1) := by
    apply hu.continuousOn.div (by fun_prop)
    intro t ht
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr (hd.trans_le ht.1).ne')
  have hgi : IntervalIntegrable g volume d 1 := by
    apply (hgc.mono ?_).intervalIntegrable
    rw [uIcc_of_le hd1]
  have hinvCont : ContinuousOn (fun t : ℝ => 1/t^2) (Icc d 1) := by
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro t ht
    exact pow_ne_zero _ (hd.trans_le ht.1).ne'
  have hinvInt : IntervalIntegrable (fun t : ℝ => 1/t^2) volume d 1 := by
    apply (hinvCont.mono ?_).intervalIntegrable
    rw [uIcc_of_le hd1]
  have hshort : ‖∫ t in (0 : ℝ)..d, k t‖ ≤ B/2 := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := d) (f := k) (C := B/(2*d)) (fun t ht => by
        rw [uIoc_of_le hd.le] at ht
        have htd : 0 < t+d := add_pos ht.1 hd
        change ‖(logReferenceLevyDensity (t+d) : ℂ) * u t‖ ≤ _
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (reference_density_bounds htd).1]
        have hn : logReferenceLevyDensity (t+d) ≤ 1/(2*d) :=
          (reference_density_bounds htd).2.trans
            (div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith only [ht.1]))
        calc
          _ ≤ (1/(2*d))*B := mul_le_mul hn (hb t) (norm_nonneg _) (by positivity)
          _ = _ := by ring)
    rw [sub_zero, abs_of_pos hd] at h
    have he : B/(2*d)*d = B/2 := by field_simp [hd.ne']
    simpa only [he] using h
  have hmiddle : ‖∫ t in d..1, k t-g t‖ ≤ B := by
    let m : ℝ → ℝ := fun t => B*(1/2 + d/2*(1/t^2))
    have hmc : ContinuousOn m (Icc d 1) := by
      apply ContinuousOn.const_mul
      apply ContinuousOn.add continuousOn_const
      apply ContinuousOn.const_mul
      apply ContinuousOn.div continuousOn_const (by fun_prop)
      intro t ht
      exact pow_ne_zero _ (hd.trans_le ht.1).ne'
    have hmi : IntervalIntegrable m volume d 1 := by
      apply (hmc.mono ?_).intervalIntegrable
      rw [uIcc_of_le hd1]
    have hki' := hki hd.le zero_le_one
    have hp : ∀ t ∈ Icc d 1, ‖k t-g t‖ ≤ m t := by
      intro t ht
      have ht0 := hd.trans_le ht.1
      have he : k t-g t = -(((1/(2*t)-logReferenceLevyDensity (t+d) : ℝ) : ℂ)*u t) := by
        dsimp only [k, g]
        push_cast
        ring
      rw [he, norm_neg, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (reference_density_middle_bound ht0 hd).1]
      calc
        _ ≤ (1/2+d/(2*t^2))*B :=
          mul_le_mul (reference_density_middle_bound ht0 hd).2 (hb t)
            (norm_nonneg _) (by positivity)
        _ = m t := by dsimp only [m]; ring
    have hbound := (intervalIntegral.norm_integral_le_integral_norm hd1).trans
      (intervalIntegral.integral_mono_on hd1 (hki'.sub hgi).norm hmi hp)
    have hmval : (∫ t in d..1, m t) = B*(1-d) := by
      rw [show m = (fun t => B*((1/2 : ℝ)+d/2*(1/t^2))) from rfl,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add (continuous_const.intervalIntegrable _ _)
          (hinvInt.const_mul (d/2)),
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
        integral_inverse_square hd hd1]
      simp only [smul_eq_mul]
      field_simp [hd.ne'] <;> ring
    rw [hmval] at hbound
    exact hbound.trans (by nlinarith only [mul_nonneg hB hd.le])
  have hremote : ‖∫ t in (1 : ℝ)..R, k t‖ ≤ B*R/2 := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 1) (b := R) (f := k) (C := B/2) (fun t ht => by
        rw [uIoc_of_le hR] at ht
        have ht0 : 0 < t := zero_lt_one.trans ht.1
        have htd : 0 < t+d := add_pos ht0 hd
        change ‖(logReferenceLevyDensity (t+d) : ℂ)*u t‖ ≤ _
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (reference_density_bounds htd).1]
        have hn : logReferenceLevyDensity (t+d) ≤ 1/2 :=
          (reference_density_bounds htd).2.trans
            (div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith only [ht.1, hd]))
        calc
          _ ≤ (1/2)*B := mul_le_mul hn (hb t) (norm_nonneg _) (by norm_num)
          _ = _ := by ring)
    rw [abs_of_nonneg (sub_nonneg.mpr hR)] at h
    exact h.trans (by nlinarith only [hB])
  have h01 := intervalIntegral.integral_add_adjacent_intervals (hki le_rfl hd.le) (hki hd.le zero_le_one)
  have h0R := intervalIntegral.integral_add_adjacent_intervals
    (hki (show 0 ≤ (0 : ℝ) from le_rfl) zero_le_one) (hki zero_le_one (zero_le_one.trans hR))
  change ‖(∫ t in (0 : ℝ)..R, k t) - ∫ t in d..1, g t‖ ≤ _
  rw [← h0R, ← h01]
  have he : ((∫ t in (0 : ℝ)..d, k t)+(∫ t in d..1, k t))+
      (∫ t in (1 : ℝ)..R, k t)-(∫ t in d..1, g t) =
      (∫ t in (0 : ℝ)..d, k t)+(∫ t in d..1, k t-g t)+(∫ t in (1 : ℝ)..R, k t) := by
    rw [intervalIntegral.integral_sub (hki hd.le zero_le_one) hgi]
    abel
  rw [he]
  calc
    _ ≤ ‖∫ t in (0 : ℝ)..d, k t‖ + ‖∫ t in d..1, k t-g t‖ + ‖∫ t in (1 : ℝ)..R, k t‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ B/2+B+B*R/2 := add_le_add (add_le_add hshort hmiddle) hremote
    _ ≤ _ := by nlinarith only [hB, mul_nonneg hB (zero_le_one.trans hR)]

private theorem continuousOn_gamma_integrand {u : ℝ → ℂ} (hu : Continuous u)
    {d : ℝ} (hd : 0 < d) :
    ContinuousOn (fun t : ℝ => (archLevyDensity (t+d) : ℂ) * u t) (Ici 0) := by
  have hk : ContinuousOn (fun t : ℝ => archLevyDensity (t+d)) (Ici 0) := by
    unfold archLevyDensity
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht
    change (0 : ℝ) ≤ t at ht
    apply ne_of_gt
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith only [ht, hd]))
  exact (Complex.continuous_ofReal.comp_continuousOn hk).mul hu.continuousOn

/-- Replacing the logarithmic kernel by the exact Gamma kernel adds bounded mass. -/
theorem gammaExteriorIntegral_sub_logarithmic_bound {u : ℝ → ℂ}
    (hu : Continuous u) {B R d : ℝ} (hb : ∀ t, ‖u t‖ ≤ B)
    (hR : 0 ≤ R) (hd : 0 < d) :
    ‖(∫ t in (0 : ℝ)..R, (archLevyDensity (t+d) : ℂ) * u t) -
      ∫ t in (0 : ℝ)..R, (logReferenceLevyDensity (t+d) : ℂ) * u t‖ ≤ 3*B*R/4 := by
  have hg := intervalIntegrable_of_continuousOn_nonneg
    (continuousOn_gamma_integrand hu hd) (show (0 : ℝ) ≤ 0 from le_rfl) hR
  have hl := intervalIntegrable_of_continuousOn_nonneg
    (continuousOn_reference_integrand hu hd) (show (0 : ℝ) ≤ 0 from le_rfl) hR
  rw [← intervalIntegral.integral_sub hg hl]
  have he : (fun t : ℝ => (archLevyDensity (t+d) : ℂ) * u t -
      (logReferenceLevyDensity (t+d) : ℂ) * u t) =
      fun t => (archLogRemainder (t+d) : ℂ) * u t := by
    funext t
    simp only [archLogRemainder, Complex.ofReal_sub, sub_mul]
  rw [he]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := R) (C := 3*B/4)
    (f := fun t : ℝ => (archLogRemainder (t+d) : ℂ) * u t) (fun t ht => by
      rw [uIoc_of_le hR] at ht
      have htd : 0 < t+d := add_pos ht.1 hd
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (archLogRemainder_nonneg htd)]
      calc
        _ ≤ (3/4)*B := mul_le_mul (archLogRemainder_le_three_quarters htd) (hb t)
          (norm_nonneg _) (by norm_num)
        _ = _ := by ring)
  rw [sub_zero, abs_of_nonneg hR] at h
  convert h using 1; ring

/-- The exact Gamma exterior response has a uniformly bounded principal-kernel error. -/
theorem gammaExteriorIntegral_sub_principal_bound {u : ℝ → ℂ}
    (hu : Continuous u) {B R d : ℝ} (hB : 0 ≤ B) (hb : ∀ t, ‖u t‖ ≤ B)
    (hR : 1 ≤ R) (hd : 0 < d) (hd1 : d ≤ 1) :
    ‖(∫ t in (0 : ℝ)..R, (archLevyDensity (t+d) : ℂ) * u t) -
      ∫ t in d..1, u t / (2*(t : ℂ))‖ ≤ (2+2*R)*B := by
  have h1 := gammaExteriorIntegral_sub_logarithmic_bound hu hb (zero_le_one.trans hR) hd
  have h2 := logarithmicExteriorIntegral_sub_principal_bound hu hB hb hR hd hd1
  let X := ∫ t in (0 : ℝ)..R, (archLevyDensity (t+d) : ℂ) * u t
  let Y := ∫ t in (0 : ℝ)..R, (logReferenceLevyDensity (t+d) : ℂ) * u t
  let Z := ∫ t in d..1, u t / (2*(t : ℂ))
  have htriangle : ‖X-Z‖ ≤ ‖X-Y‖+‖Y-Z‖ := by
    have he : X-Z = (X-Y)+(Y-Z) := by abel
    rw [he]
    exact norm_add_le _ _
  calc
    _ ≤ ‖(∫ t in (0 : ℝ)..R, (archLevyDensity (t+d) : ℂ) * u t) -
        ∫ t in (0 : ℝ)..R, (logReferenceLevyDensity (t+d) : ℂ) * u t‖ +
        ‖(∫ t in (0 : ℝ)..R, (logReferenceLevyDensity (t+d) : ℂ) * u t) -
          ∫ t in d..1, u t / (2*(t : ℂ))‖ := htriangle
    _ ≤ 3*B*R/4 + (2+R)*B := add_le_add h1 h2
    _ ≤ _ := by nlinarith only [mul_nonneg hB (zero_le_one.trans hR)]

/-- A finite normalized interior trace gives the exact exterior Gamma coefficient. -/
theorem gammaExteriorIntegral_normalized_limit {u : ℝ → ℂ}
    (hu : Continuous u) {B R : ℝ} (hB : 0 ≤ B) (hb : ∀ t, ‖u t‖ ≤ B)
    (hR : 1 ≤ R) {τ : ℂ}
    (hτ : Tendsto (fun t : ℝ => u t * (Real.sqrt (Real.log (1/t)) : ℂ))
      (𝓝[>] (0 : ℝ)) (nhds τ)) :
    Tendsto (fun d : ℝ =>
      (∫ t in (0 : ℝ)..R, (archLevyDensity (t+d) : ℂ) * u t) /
        (Real.sqrt (Real.log (1/d)) : ℂ)) (𝓝[>] (0 : ℝ)) (nhds τ) := by
  let X : ℝ → ℂ := fun d => ∫ t in (0 : ℝ)..R, (archLevyDensity (t+d) : ℂ) * u t
  let Y : ℝ → ℂ := fun d => ∫ t in d..1, u t / (2*(t : ℂ))
  let L : ℝ → ℝ := fun d => Real.sqrt (Real.log (1/d))
  have hlog : Tendsto (fun d : ℝ => Real.log (1/d)) (𝓝[>] (0 : ℝ)) atTop := by
    simpa only [one_div, Real.log_inv, Function.comp_def] using
      tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hL : Tendsto L (𝓝[>] (0 : ℝ)) atTop := Real.tendsto_sqrt_atTop.comp hlog
  have hmajor : Tendsto (fun d : ℝ => (2+2*R)*B / L d) (𝓝[>] (0 : ℝ)) (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hL).const_mul ((2+2*R)*B)
  have herr : Tendsto (fun d : ℝ => (X d-Y d)/(L d : ℂ))
      (𝓝[>] (0 : ℝ)) (nhds 0) := by
    apply squeeze_zero_norm' _ hmajor
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds] with d hd hd1
    change (0 : ℝ) < d at hd
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact div_le_div_of_nonneg_right
      (gammaExteriorIntegral_sub_principal_bound hu hB hb hR hd hd1.le)
      (Real.sqrt_nonneg _)
  have hy := truncated_logarithmic_integral_normalized_limit hu hτ
  have h := herr.add hy
  simp only [zero_add] at h
  convert h using 1
  funext d
  change X d / (L d : ℂ) = (X d-Y d)/(L d : ℂ) + Y d/(L d : ℂ)
  ring

private theorem measurable_gammaExteriorIntegral {u : ℝ → ℂ} (hu : Measurable u)
    {R : ℝ} (hR : 0 ≤ R) :
    Measurable (fun d : ℝ => ∫ t in (0 : ℝ)..R,
      (archLevyDensity (t+d) : ℂ) * u t) := by
  have hm : Measurable (fun p : ℝ × ℝ => (archLevyDensity (p.2+p.1) : ℂ) * u p.2) :=
    (Complex.continuous_ofReal.measurable.comp
      (measurable_archLevyDensity.comp (measurable_snd.add measurable_fst))).mul
      (hu.comp measurable_snd)
  simpa only [intervalIntegral.integral_of_le hR] using
    (hm.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioc (0 : ℝ) R))).measurable

private theorem integral_positive_eq_interval_of_zero_tail {f : ℝ → ℂ} {R : ℝ}
    (hR : 0 ≤ R) (htail : ∀ t, R < t → f t = 0) :
    (∫ t in Ioi (0 : ℝ), f t) = ∫ t in (0 : ℝ)..R, f t := by
  rw [intervalIntegral.integral_of_le hR]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (fun _ ht => ht.1)
  intro t ht
  apply htail
  by_contra! hn
  exact ht.2 ⟨ht.1, hn⟩

private theorem boundaryTransfer_eq_truncated {a R : ℝ} (hR : 0 ≤ R)
    (u : SoninL2) (U : ℝ → ℂ) (hU : U =ᵐ[volume] u)
    (htail : ∀ t, R < t → U (a-t) = 0) :
    (ccmGammaRightBoundaryTransfer a u : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun s => ∫ t in (0 : ℝ)..R, (archLevyDensity (t+s) : ℂ) * U (a-t) := by
  have hm : MeasurePreserving (fun t : ℝ => a-t) volume volume := by
    simpa only [Function.comp_def, sub_eq_add_neg] using
      (measurePreserving_add_left volume a).comp
        (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hUa := hU.comp_tendsto hm.quasiMeasurePreserving.tendsto_ae
  filter_upwards [ccmGammaRightBoundaryTransfer_coeFn a u] with s hs
  rw [hs]
  calc
    _ = ∫ t in Ioi (0 : ℝ), (archLevyDensity (t+s) : ℂ) * U (a-t) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hUa] with t ht
      dsimp only [Function.comp_apply] at ht
      rw [← ht]
      simp only [ccmGammaTranslationDensity, archLevyDensity, neg_div, neg_mul, add_comm s t]
    _ = _ := integral_positive_eq_interval_of_zero_tail hR (fun t ht => by
      rw [htail t ht, mul_zero])

namespace WeilHilbertBeforeContact

/-- The literal right exterior Gamma response of the actual continuous Riesz source. -/
def evalVectorRightExteriorResponse (a : PrecontactAperture) (z : ℂ) (d : ℝ) : ℂ :=
  -(∫ t in (0 : ℝ)..max 1 (2*a.1.1),
    (archLevyDensity (t+d) : ℂ) * evalVectorContinuousRepresentative a z (a.1.1-t))

/-- The literal left exterior Gamma response of the same source. -/
def evalVectorLeftExteriorResponse (a : PrecontactAperture) (z : ℂ) (d : ℝ) : ℂ :=
  -(∫ t in (0 : ℝ)..max 1 (2*a.1.1),
    (archLevyDensity (t+d) : ℂ) * evalVectorContinuousRepresentative a z (t-a.1.1))

theorem measurable_evalVectorRightExteriorResponse (a : PrecontactAperture) (z : ℂ) :
    Measurable (evalVectorRightExteriorResponse a z) :=
  (measurable_gammaExteriorIntegral
    ((continuous_evalVectorContinuousRepresentative a z).measurable.comp
      (measurable_const.sub measurable_id))
    (zero_le_one.trans (le_max_left 1 (2*a.1.1)))).neg

theorem measurable_evalVectorLeftExteriorResponse (a : PrecontactAperture) (z : ℂ) :
    Measurable (evalVectorLeftExteriorResponse a z) :=
  (measurable_gammaExteriorIntegral
    ((continuous_evalVectorContinuousRepresentative a z).measurable.comp
      (measurable_id.sub_const a.1.1))
    (zero_le_one.trans (le_max_left 1 (2*a.1.1)))).neg

/-- The literal right response is the negative of the actual bounded Gamma boundary operator. -/
theorem evalVectorRightExteriorResponse_eq_boundaryTransfer (a : PrecontactAperture) (z : ℂ) :
    evalVectorRightExteriorResponse a z =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun d => -ccmGammaRightBoundaryTransfer a.1.1
        (ccmArchimedeanFormEmbedding a.1 (toForm a (evalVector a z))) d := by
  have h := boundaryTransfer_eq_truncated
    (a := a.1.1) (zero_le_one.trans (le_max_left 1 (2*a.1.1))) _ _
    (evalVectorContinuousRepresentative_ae a z) (fun t ht => by
      apply evalVectorContinuousRepresentative_eq_zero a z
      exact Or.inl (by linarith only [ht, le_max_right (1 : ℝ) (2*a.1.1)]))
  filter_upwards [h] with d hd
  exact congrArg Neg.neg hd.symm

/-- Reflection identifies the literal left response with the actual left boundary operator. -/
theorem evalVectorLeftExteriorResponse_eq_boundaryTransfer (a : PrecontactAperture) (z : ℂ) :
    evalVectorLeftExteriorResponse a z =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun d => -ccmGammaLeftBoundaryTransfer a.1.1
        (ccmArchimedeanFormEmbedding a.1 (toForm a (evalVector a z))) d := by
  let u := ccmArchimedeanFormEmbedding a.1 (toForm a (evalVector a z))
  have hU : (fun x : ℝ => evalVectorContinuousRepresentative a z (-x)) =ᵐ[volume]
      (l2Reflection u : ℝ → ℂ) := by
    have h := (evalVectorContinuousRepresentative_ae a z).comp_tendsto
      (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
    exact h.trans (l2Reflection_ae u).symm
  have h := boundaryTransfer_eq_truncated
    (a := a.1.1) (zero_le_one.trans (le_max_left 1 (2*a.1.1))) _ _ hU (fun t ht => by
      apply evalVectorContinuousRepresentative_eq_zero a z
      exact Or.inr (by linarith only [ht, le_max_right (1 : ℝ) (2*a.1.1)]))
  filter_upwards [h] with d hd
  simpa only [evalVectorLeftExteriorResponse, ccmGammaLeftBoundaryTransfer, neg_sub] using
    congrArg Neg.neg hd.symm

/-- The actual right exterior coefficient is minus the exact right renewal readout. -/
theorem evalVectorRightExteriorResponse_normalized_limit (a : PrecontactAperture) (z : ℂ) :
    Tendsto (fun d : ℝ => evalVectorRightExteriorResponse a z d /
      (Real.sqrt (Real.log (1/d)) : ℂ)) (𝓝[>] (0 : ℝ))
      (nhds (-(∫ y : ℝ, (logarithmicCausalKernel y : ℂ) *
        (evalVectorRightEndpointForcing a z : RealLineL2) y))) := by
  obtain ⟨B, hb⟩ := (continuous_evalVectorContinuousRepresentative a z).bounded_above_of_compact_support
    (hasCompactSupport_evalVectorContinuousRepresentative a z)
  have hB : 0 ≤ B := (norm_nonneg _).trans (hb 0)
  have h := gammaExteriorIntegral_normalized_limit
    ((continuous_evalVectorContinuousRepresentative a z).comp (by fun_prop)) hB
    (fun t => hb (a.1.1-t)) (le_max_left 1 (2*a.1.1))
    (evalVectorContinuousRepresentative_right_normalized_limit a z)
  simpa only [evalVectorRightExteriorResponse, neg_div, Function.comp_def] using h.neg

/-- The actual left exterior coefficient is minus the exact left renewal readout. -/
theorem evalVectorLeftExteriorResponse_normalized_limit (a : PrecontactAperture) (z : ℂ) :
    Tendsto (fun d : ℝ => evalVectorLeftExteriorResponse a z d /
      (Real.sqrt (Real.log (1/d)) : ℂ)) (𝓝[>] (0 : ℝ))
      (nhds (-(∫ y : ℝ, (logarithmicCausalKernel y : ℂ) *
        (evalVectorLeftEndpointForcing a z : RealLineL2) y))) := by
  obtain ⟨B, hb⟩ := (continuous_evalVectorContinuousRepresentative a z).bounded_above_of_compact_support
    (hasCompactSupport_evalVectorContinuousRepresentative a z)
  have hB : 0 ≤ B := (norm_nonneg _).trans (hb 0)
  have h := gammaExteriorIntegral_normalized_limit
    ((continuous_evalVectorContinuousRepresentative a z).comp (by fun_prop)) hB
    (fun t => hb (t-a.1.1)) (le_max_left 1 (2*a.1.1))
    (evalVectorContinuousRepresentative_left_normalized_limit a z)
  simpa only [evalVectorLeftExteriorResponse, neg_div, Function.comp_def] using h.neg

#print axioms evalVectorRightExteriorResponse_eq_boundaryTransfer
#print axioms evalVectorLeftExteriorResponse_eq_boundaryTransfer
#print axioms evalVectorRightExteriorResponse_normalized_limit
#print axioms evalVectorLeftExteriorResponse_normalized_limit
end WeilHilbertBeforeContact
#print axioms logarithmicExteriorIntegral_sub_principal_bound
#print axioms gammaExteriorIntegral_sub_principal_bound
end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
