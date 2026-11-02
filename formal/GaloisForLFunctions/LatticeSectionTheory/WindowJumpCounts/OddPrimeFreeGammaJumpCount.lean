import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.OddLogarithmicLagGap
import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.SinglePrimeWindowJumpGraphAndObstructions
import GaloisForLFunctions.ArithmeticIncidencePositivity.SecondOrderSurplusPotential
import GaloisForLFunctions.RHTower.HarmonicStirlingExactBounds
import GaloisForLFunctions.BiScaleUncertainty.NyquistCriticalFinitePartAndBroadClassification

/-!
# Odd Gamma jump counts on the prime-free window

Oddness cancels the total correlation. Centering its first moment at the
support radius improves the interior Gamma correction. The logarithmic
jump gap and exact exterior tail then pay the archimedean and pole costs.
For odd tests supported in `[-a,a]`, `0<2a≤log 2`, this gives
`W(f,f)≥‖f‖²/1000` and `h¹_prim≥‖f‖²/2000`.
-/

open Real MeasureTheory Set Filter Topology
open scoped CompactlySupported
open RHTower RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm
open RHTower.WeilMarkovPole RHTower.WeilLevyPoleGauss

noncomputable section

namespace GaloisForLFunctions.LatticeSectionTheory

open ArithmeticCastelnuovoSeveri ArithmeticCriticalityTheory ArithmeticIncidencePositivity
open ArithmeticEffectivityTheory
open BiScaleUncertainty WindowJumpCounts Zeta23

/-- Oddness cancels the correlation over its entire positive support. -/
theorem odd_autocorr_integral_zero {f : ℝ → ℝ} (hf : f ∈ realTests) {a : ℝ}
    (hs : tsupport f ⊆ Icc (-a) a) (ho : ∀ x, f (-x) = -f x) :
    (∫ t in Ioc (0 : ℝ) (2 * a), autocorr f t) = 0 := by
  let fc : C_c(ℝ, ℝ) := ⟨⟨f, hf.1.continuous⟩, hf.2⟩
  have hfull := integral_autocorr_eq_sq_integral fc
  have hmean : (∫ x, f x) = 0 := by
    have hn := integral_neg_eq_self f volume
    rw [integral_congr_ae (Eventually.of_forall ho), integral_neg] at hn
    linarith only [hn]
  change (∫ t, autocorr f t) = (∫ x, f x) ^ 2 at hfull
  rw [hmean, zero_pow two_ne_zero] at hfull
  have habs : ∀ t, autocorr f |t| = autocorr f t := by
    intro t
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_nonpos ht, autocorr_neg]
  have hhalf : (∫ t, autocorr f t) = 2 * ∫ t in Ioi (0 : ℝ), autocorr f t := by
    rw [← integral_congr_ae (Eventually.of_forall habs), integral_comp_abs]
  have hcut : (∫ t in Ioi (0 : ℝ), autocorr f t) =
      ∫ t in Ioc (0 : ℝ) (2 * a), autocorr f t := by
    have he : ∀ t ∈ Ioi (0 : ℝ), autocorr f t =
        (Iic (2 * a)).indicator (autocorr f) t := by
      intro t ht
      by_cases h : t ≤ 2 * a
      · exact (Set.indicator_of_mem (Set.mem_Iic.mpr h) (autocorr f)).symm
      · rw [Set.indicator_of_notMem (show t ∉ Iic (2 * a) from h),
          autocorr_eq_zero_of_support hs (lt_of_not_ge h)]
    rw [setIntegral_congr_fun measurableSet_Ioi he, setIntegral_indicator measurableSet_Iic,
      Ioi_inter_Iic]
  rw [hhalf, hcut] at hfull
  linarith only [hfull]

private theorem integral_centered_abs {a : ℝ} (ha : 0 ≤ a) :
    (∫ t in Ioc (0 : ℝ) (2 * a), |t - a|) = a ^ 2 := by
  rw [← intervalIntegral.integral_of_le (by positivity)]
  rw [← intervalIntegral.integral_add_adjacent_intervals (f := fun t : ℝ => |t - a|)
    ((continuous_id.sub continuous_const).abs.intervalIntegrable 0 a)
    ((continuous_id.sub continuous_const).abs.intervalIntegrable a (2 * a))]
  have hleft : (∫ t in (0 : ℝ)..a, |t - a|) = ∫ t in (0 : ℝ)..a, a - t := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [uIcc_of_le ha] at ht
    rw [abs_of_nonpos (sub_nonpos.mpr ht.2)]
    ring
  have hright : (∫ t in a..2 * a, |t - a|) = ∫ t in a..2 * a, t - a := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    exact abs_of_nonneg (sub_nonneg.mpr ht.1)
  rw [hleft, hright, intervalIntegral.integral_sub (f := fun _ : ℝ => a) (g := fun t : ℝ => t)
    intervalIntegrable_const (continuous_id.intervalIntegrable _ _),
    intervalIntegral.integral_sub (f := fun t : ℝ => t) (g := fun _ : ℝ => a)
    (continuous_id.intervalIntegrable _ _) intervalIntegrable_const]
  simp only [intervalIntegral.integral_const, integral_id, smul_eq_mul]
  ring

/-- Centering at `a` bounds the first jump moment by `3a²` times the mass. -/
theorem odd_jump_first_moment_le {f : ℝ → ℝ} (hf : f ∈ realTests) {a : ℝ}
    (ha : 0 < a) (hs : tsupport f ⊆ Icc (-a) a) (ho : ∀ x, f (-x) = -f x) :
    (∫ t in Ioc (0 : ℝ) (2 * a), t * (autocorr f 0 - autocorr f t)) ≤
      3 * a ^ 2 * autocorr f 0 := by
  set M := autocorr f 0
  have hc : Continuous (autocorr f) := continuous_autocorr hf.1 hf.2
  have hcenter : -a ^ 2 * M ≤ ∫ t in Ioc (0 : ℝ) (2 * a), (t - a) * autocorr f t := by
    have hb : ∀ t, -|t - a| * M ≤ (t - a) * autocorr f t := by
      intro t
      have hab := abs_autocorr_le_zero hf.2 hf.1.continuous t
      have hprod := mul_le_mul_of_nonneg_left hab (abs_nonneg (t - a))
      have hn := neg_abs_le ((t - a) * autocorr f t)
      rw [abs_mul] at hn
      linarith only [hprod, hn]
    have hi : (∫ t in Ioc (0 : ℝ) (2 * a), -|t - a| * M) ≤
        ∫ t in Ioc (0 : ℝ) (2 * a), (t - a) * autocorr f t := setIntegral_mono_on
      (f := fun t => -|t - a| * M) (g := fun t => (t - a) * autocorr f t)
      (((continuous_id.sub continuous_const).abs.neg.mul continuous_const).integrableOn_Icc.mono_set
        Ioc_subset_Icc_self)
      (((continuous_id.sub continuous_const).mul hc).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      measurableSet_Ioc (fun t _ => hb t)
    rw [integral_mul_const, integral_neg, integral_centered_abs ha.le] at hi
    exact hi
  have hzero := odd_autocorr_integral_zero hf hs ho
  have he : (∫ t in Ioc (0 : ℝ) (2 * a), (t - a) * autocorr f t) =
      ∫ t in Ioc (0 : ℝ) (2 * a), t * autocorr f t := by
    simp_rw [sub_mul]
    rw [integral_sub (f := fun t => t * autocorr f t) (g := fun t => a * autocorr f t)
      ((continuous_id.mul hc).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      ((continuous_const.mul hc).integrableOn_Icc.mono_set Ioc_subset_Icc_self),
      integral_const_mul, hzero, mul_zero, sub_zero]
  have hlin : (∫ t in Ioc (0 : ℝ) (2 * a), t * M) = 2 * a ^ 2 * M := by
    rw [integral_mul_const, ← intervalIntegral.integral_of_le (by positivity), integral_id]
    ring
  simp_rw [mul_sub]
  rw [integral_sub (f := fun t => t * M) (g := fun t => t * autocorr f t)
    ((continuous_id.mul continuous_const).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    ((continuous_id.mul hc).integrableOn_Icc.mono_set Ioc_subset_Icc_self), hlin]
  rw [he] at hcenter
  linarith only [hcenter]

/-- The Gamma weight dominates the logarithmic weight with an affine correction. -/
theorem archLevySinhWeight_ge_log_affine {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 3 / 4) :
    1 / t + 1 / 2 - t / 10 ≤ archLevySinhWeight t := by
  have h := (archLevyDensity_secondOrder_bounds ht ht1).1
  have ht2 : t ^ 2 ≤ 3 / 4 * t := by nlinarith only [mul_nonneg ht.le (sub_nonneg.mpr ht1)]
  have he : 2 * (1 / (2 * t)) = 1 / t := by field_simp
  rw [archLevySinhWeight, exp_half_div_sinh_eq ht]
  nlinarith only [h, ht2, he, ht]


/-- The actual Gamma jump count, including its full exterior tail. -/
theorem odd_gamma_jump_count_ge {f : ℝ → ℝ} (hf : f ∈ realTests) {a : ℝ}
    (ha : 0 < a) (ha1 : 2 * a ≤ 3 / 4) (hs : tsupport f ⊆ Icc (-a) a)
    (ho : ∀ x, f (-x) = -f x) :
    (Real.log 2 + 7 / 5 + 2 * archLevyAntideriv (2 * a) + a - 3 * a ^ 2 / 10) *
      (∫ x, f x ^ 2) ≤ jumpCount f := by
  set M := autocorr f 0
  set D := fun t => M - autocorr f t
  set W := fun t => D t * archLevySinhWeight t
  have hc : Continuous (autocorr f) := continuous_autocorr hf.1 hf.2
  have hdc : Continuous D := continuous_const.sub hc
  have hd : ∀ t, 0 ≤ D t := fun t => sub_nonneg.mpr
    ((le_abs_self _).trans (abs_autocorr_le_zero hf.2 hf.1.continuous t))
  have hi : IntegrableOn W (Ioi 0) := integrableOn_biScaleLevyIntegrand hf.1 hf.2
  have hsub : Ioc (0 : ℝ) (2 * a) ⊆ Ioi 0 := fun t ht => Set.mem_Ioi.mpr ht.1
  have hsubtail : Ioi (2 * a) ⊆ Ioi (0 : ℝ) := fun t ht =>
    Set.mem_Ioi.mpr (lt_trans (show 0 < 2 * a by positivity) (Set.mem_Ioi.mp ht))
  have hilog : IntegrableOn (fun t => D t / t) (Ioc (0 : ℝ) (2 * a)) := by
    apply (hi.mono_set hsub).mono'
      ((hdc.measurable.div measurable_id).aestronglyMeasurable.restrict)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    change ‖D t / t‖ ≤ W t
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hd t) ht.1.le)]
    have hw := archLevySinhWeight_ge_log_affine ht.1 (le_trans ht.2 ha1)
    have hwinv : 1 / t ≤ archLevySinhWeight t := by linarith only [hw, ht.2, ha1]
    simpa only [W, div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hwinv (hd t)
  have hiD : IntegrableOn D (Ioc (0 : ℝ) (2 * a)) :=
    hdc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hitD : IntegrableOn (fun t => t * D t) (Ioc (0 : ℝ) (2 * a)) :=
    (continuous_id.mul hdc).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hcomp : (∫ t in Ioc (0 : ℝ) (2 * a), D t / t + D t / 2 - (t * D t) / 10) ≤
      ∫ t in Ioc (0 : ℝ) (2 * a), W t := by
    apply setIntegral_mono_on ((hilog.add (hiD.div_const 2)).sub (hitD.div_const 10))
      (hi.mono_set hsub) measurableSet_Ioc
    intro t ht
    have h := mul_le_mul_of_nonneg_left
      (archLevySinhWeight_ge_log_affine ht.1 (le_trans ht.2 ha1)) (hd t)
    calc D t / t + D t / 2 - t * D t / 10 = D t * (1 / t + 1 / 2 - t / 10) := by ring
      _ ≤ W t := h
  have hD : (∫ t in Ioc (0 : ℝ) (2 * a), D t) = 2 * a * M := by
    rw [show D = (fun t => M - autocorr f t) from rfl,
      integral_sub (f := fun _ : ℝ => M) (g := autocorr f)
        (continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
        (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self),
      odd_autocorr_integral_zero hf hs ho, sub_zero, setIntegral_const]
    simp only [Measure.real, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal (show 0 ≤ 2 * a by positivity),
      smul_eq_mul]
  have hlog := odd_interior_jump_poincare hf.1 ha hs ho
  rw [← autocorr_zero_eq] at hlog
  have hmom := odd_jump_first_moment_le hf ha hs ho
  rw [integral_sub (f := fun t => D t / t + D t / 2) (g := fun t => t * D t / 10)
      (hilog.add (hiD.div_const 2)) (hitD.div_const 10),
    integral_add (f := fun t => D t / t) (g := fun t => D t / 2)
      hilog (hiD.div_const 2), integral_div, integral_div, hD] at hcomp
  have htail : (∫ t in Ioi (2 * a), W t) = 2 * archLevyAntideriv (2 * a) * M := by
    have he : ∀ t ∈ Ioi (2 * a), W t = 2 * archLevyDensity t * M := by
      intro t ht
      dsimp [W, D, M]
      rw [autocorr_eq_zero_of_support hs ht, sub_zero,
        archLevySinhWeight, exp_half_div_sinh_eq
          (lt_trans (show 0 < 2 * a by positivity) (Set.mem_Ioi.mp ht))]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi he, integral_mul_const, integral_const_mul,
      WeilLevyCoshCrossover.integral_archLevyDensity_Ioi (by positivity)]
  have hsplit : (∫ t in Ioc (0 : ℝ) (2 * a), W t) +
      (∫ t in Ioi (2 * a), W t) = jumpCount f := by
    rw [← setIntegral_union (s := Ioc (0 : ℝ) (2 * a)) (t := Ioi (2 * a))
      (Set.disjoint_left.mpr (fun t ht ht' => not_lt_of_ge ht.2 ht'))
      measurableSet_Ioi (hi.mono_set hsub) (hi.mono_set hsubtail)]
    have he : Ioc (0 : ℝ) (2 * a) ∪ Ioi (2 * a) = Ioi 0 := by
      ext t
      simp only [mem_union, mem_Ioc, mem_Ioi]
      constructor
      · rintro (h | h)
        · exact h.1
        · linarith only [h, ha]
      · intro ht
        rcases le_total t (2 * a) with h | h
        · exact Or.inl ⟨ht, h⟩
        · rcases h.eq_or_lt with h | h
          · exact Or.inl ⟨ht, h.ge⟩
          · exact Or.inr h
    rw [he]
    rfl
  rw [htail] at hsplit
  rw [← autocorr_zero_eq]
  change (Real.log 2 + 7 / 5 + 2 * archLevyAntideriv (2 * a) + a - 3 * a ^ 2 / 10) * M ≤ _
  change (Real.log 2 + 7 / 5) * M ≤ ∫ t in Ioc (0 : ℝ) (2 * a), D t / t at hlog
  change (∫ t in Ioc (0 : ℝ) (2 * a), t * D t) ≤ 3 * a ^ 2 * M at hmom
  nlinarith only [hcomp, hlog, hmom, hsplit]

private theorem sinh_sq_le_window_moment {a x : ℝ} (ha : 0 < a)
  (hx : x ∈ Icc (-a) a) :
  Real.sinh (x / 2) ^ 2 ≤ Real.cosh (a / 2) ^ 2 / 4 * x ^ 2 := by
  have hxa : |x| ≤ a := abs_le.mpr hx
  have hb : |Real.sinh (x / 2)| ≤ |x| / 2 * Real.cosh (a / 2) := by
    rw [Real.abs_sinh, abs_div, abs_two]
    have hc : Real.cosh (|x| / 2) ≤ Real.cosh (a / 2) := by
      rw [Real.cosh_le_cosh, abs_of_nonneg (show 0 ≤ |x| / 2 by positivity),
        abs_of_pos (show 0 < a / 2 by positivity)]
      linarith only [hxa]
    exact (ArithmeticIncidencePositivity.sinh_le_mul_cosh (by positivity)).trans
      (mul_le_mul_of_nonneg_left hc (by positivity))
  have hsq := pow_le_pow_left₀ (abs_nonneg _) hb 2
  rw [sq_abs, mul_pow, div_pow, sq_abs] at hsq
  nlinarith only [hsq]

private theorem integral_sinh_sq_window_le {a : ℝ} (ha : 0 < a) :
    (∫ x in Icc (-a) a, Real.sinh (x / 2) ^ 2) ≤ a ^ 3 / 6 * Real.cosh (a / 2) ^ 2 := by
  have hc : Continuous (fun x : ℝ => Real.sinh (x / 2)) := by fun_prop
  calc (∫ x in Icc (-a) a, Real.sinh (x / 2) ^ 2) ≤
        ∫ x in Icc (-a) a, Real.cosh (a / 2) ^ 2 / 4 * x ^ 2 :=
      setIntegral_mono_on (hc.pow 2).integrableOn_Icc
        ((continuous_const.mul (continuous_pow 2)).integrableOn_Icc) measurableSet_Icc
        (fun x hx => sinh_sq_le_window_moment ha hx)
    _ = _ := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith only [ha]),
        intervalIntegral.integral_const_mul, integral_pow]
      ring

private def windowSinh (a : ℝ) : ℝ → ℝ :=
  (Icc (-a) a).indicator (fun x => Real.sinh (x / 2))

private theorem windowSinh_sq_eq (a : ℝ) :
    (fun x => windowSinh a x ^ 2) =
      (Icc (-a) a).indicator (fun x => Real.sinh (x / 2) ^ 2) := by
  funext x
  by_cases hx : x ∈ Icc (-a) a <;>
    simp only [windowSinh, Set.indicator_apply, hx, if_true, if_false, zero_pow two_ne_zero]

private theorem windowSinh_measurable (a : ℝ) : AEStronglyMeasurable (windowSinh a) :=
  ((Real.continuous_sinh.comp (continuous_id.div_const 2)).aestronglyMeasurable.indicator
    measurableSet_Icc)

private theorem windowSinh_sq_integrable (a : ℝ) : Integrable (fun x => windowSinh a x ^ 2) := by
  rw [windowSinh_sq_eq]
  exact (integrable_indicator_iff measurableSet_Icc).mpr
    (((Real.continuous_sinh.comp (continuous_id.div_const 2)).pow 2).integrableOn_Icc)

private theorem oddPoleMoment_eq_windowSinh {f : ℝ → ℝ} {a : ℝ}
    (hs : tsupport f ⊆ Icc (-a) a) :
    oddPoleMoment f = ∫ x, f x * windowSinh a x := by
  unfold oddPoleMoment
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Icc (-a) a
  · simp only [windowSinh, Set.indicator_of_mem hx]
  · have hz : f x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
    rw [hz, zero_mul, zero_mul]

/-- The odd pole costs at most the second moment of its supporting interval. -/
theorem odd_pole_sq_le_support {f : ℝ → ℝ} (hf : f ∈ realTests) {a : ℝ}
    (ha : 0 < a) (hs : tsupport f ⊆ Icc (-a) a) :
    oddPoleMoment f ^ 2 ≤ a ^ 3 / 6 * Real.cosh (a / 2) ^ 2 * (∫ x, f x ^ 2) := by
  have hF2 : Integrable (fun x => f x ^ 2) :=
    (hf.1.continuous.pow 2).integrable_of_hasCompactSupport
      (RHTower.CHMDPolar.hasCompactSupport_sq hf.2)
  have hGbound : (∫ x, windowSinh a x ^ 2) ≤ a ^ 3 / 6 * Real.cosh (a / 2) ^ 2 := by
    rw [windowSinh_sq_eq, integral_indicator measurableSet_Icc]
    exact integral_sinh_sq_window_le ha
  have hCS := GaloisForLFunctions.HTGeometry.sq_integral_mul_le hf.1.continuous.aestronglyMeasurable
    (windowSinh_measurable a) hF2 (windowSinh_sq_integrable a)
  rw [oddPoleMoment_eq_windowSinh hs]
  calc (∫ x, f x * windowSinh a x) ^ 2 ≤ (∫ x, f x ^ 2) * (∫ x, windowSinh a x ^ 2) := hCS
    _ ≤ (∫ x, f x ^ 2) * (a ^ 3 / 6 * Real.cosh (a / 2) ^ 2) :=
      mul_le_mul_of_nonneg_left hGbound (integral_nonneg fun x => sq_nonneg _)
    _ = _ := by ring

/-- The logarithmic jump gap yields an explicit Weil floor, with its odd pole cost. -/
theorem odd_weil_count_floor {f : ℝ → ℝ} (hf : f ∈ realTests) {a : ℝ}
    (ha : 0 < a) (ha1 : 2 * a ≤ Real.log 2) (hs : tsupport f ⊆ Icc (-a) a)
    (ho : ∀ x, f (-x) = -f x) :
    (7 / 5 - Real.eulerMascheroniConstant - Real.log (2 * Real.pi * a) -
      13 * a ^ 2 / 60 - a ^ 3 / 3 * Real.cosh (a / 2) ^ 2) * (∫ x, f x ^ 2) ≤ weilPair f f := by
  have hsmall : 2 * a ≤ 3 / 4 := by linarith only [ha1, Real.log_two_lt_d9]
  have hJ := odd_gamma_jump_count_ge hf ha hsmall hs ho
  have htail := archLevyAntideriv_ge_second (show 0 < 2 * a by positivity)
    (show 2 * a ≤ 1 by linarith only [hsmall])
  have hp := odd_pole_sq_le_support hf ha hs
  have hM : 0 ≤ ∫ x, f x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have heven := evenPoleMoment_eq_zero_of_odd ho
  have hlogs : Real.log 2 - Real.log (2 * a / 4) - Real.log (8 * Real.pi) =
      -Real.log (2 * Real.pi * a) := by
    rw [Real.log_div (by positivity) (by norm_num),
      Real.log_mul (by norm_num) ha.ne', Real.log_mul (by norm_num) Real.pi_ne_zero,
      Real.log_mul (by positivity) ha.ne', Real.log_mul (by norm_num) Real.pi_ne_zero,
      show (4 : ℝ) = 2 ^ 2 by norm_num, show (8 : ℝ) = 2 ^ 3 by norm_num,
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  rw [weilPair_eq_jumpCount_add_poleSquares_of_le_log_two hf hs ha1, heven, zero_pow two_ne_zero,
    mul_zero, add_zero, gammaBracket_zero_eq]
  have htm := mul_le_mul_of_nonneg_right htail hM
  have hlm := congrArg (fun z => z * (∫ x, f x ^ 2)) hlogs
  nlinarith only [hJ, hp, htm, hlm]

private theorem odd_count_euler_bound : Real.eulerMascheroniConstant ≤ 289 / 500 := by
  have h := RHTower.harmonic_mascheroni_ge_half_sub_twelfth (n := 2) (by norm_num)
  norm_num [harmonic, Finset.sum_range_succ] at h
  linarith only [h, Real.log_two_gt_d9]

private theorem log_pi_log_two_le : Real.log (Real.pi * Real.log 2) ≤ 779 / 1000 := by
  rw [Real.log_le_iff_le_exp (mul_pos Real.pi_pos (Real.log_pos (by norm_num)))]
  have hT := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 779 / 1000 by norm_num) 7
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hT
  norm_num at hT
  have hprod := mul_le_mul Real.pi_lt_d6.le Real.log_two_lt_d9.le
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)) (by norm_num : (0 : ℝ) ≤ 3.141593)
  linarith only [hT, hprod]

private theorem odd_count_pole_coefficient_le {a : ℝ} (ha : 0 < a)
    (ha1 : 2 * a ≤ Real.log 2) : a ^ 3 / 3 * Real.cosh (a / 2) ^ 2 ≤ 3 / 200 := by
  have hb : a ≤ 347 / 1000 := by linarith only [ha1, Real.log_two_lt_d9]
  have ha2 : a ^ 2 ≤ 121 / 1000 := by
    have h := pow_le_pow_left₀ ha.le hb 2
    norm_num at h
    linarith only [h]
  have hz2 : (a / 2) ^ 2 ≤ 1 / 32 := by nlinarith only [ha2]
  have hcosh := (sinh_cosh_taylor_bounds (show 0 ≤ a / 2 by positivity)
    (show a / 2 ≤ 1 by linarith only [hb])).2.2.2
  have hcp : 0 ≤ Real.cosh (a / 2) := (Real.cosh_pos _).le
  have hc : Real.cosh (a / 2) ≤ 64 / 63 := by
    have hmul := mul_le_mul_of_nonneg_right (show (63 : ℝ) / 64 ≤ 1 - (a / 2) ^ 2 / 2 by
      linarith only [hz2]) hcp
    linarith only [hcosh, hmul]
  have hc2 : Real.cosh (a / 2) ^ 2 ≤ 16 / 15 := by
    have hsq := pow_le_pow_left₀ hcp hc 2
    norm_num at hsq
    linarith only [hsq]
  have ha3 := pow_le_pow_left₀ ha.le hb 3
  have hprod := mul_le_mul (div_le_div_of_nonneg_right ha3 (by norm_num : (0 : ℝ) ≤ 3))
    hc2 (sq_nonneg _) (by positivity)
  norm_num at hprod
  linarith only [hprod]

/-- The odd jump-count floor stays positive through the closed prime-free endpoint. -/
theorem odd_primefree_count_coefficient_ge {a : ℝ} (ha : 0 < a)
    (ha1 : 2 * a ≤ Real.log 2) :
    (1 : ℝ) / 1000 ≤ 7 / 5 - Real.eulerMascheroniConstant - Real.log (2 * Real.pi * a) -
      13 * a ^ 2 / 60 - a ^ 3 / 3 * Real.cosh (a / 2) ^ 2 := by
  have hb : a ≤ 347 / 1000 := by linarith only [ha1, Real.log_two_lt_d9]
  have ha2 : a ^ 2 ≤ 121 / 1000 := by
    have h := pow_le_pow_left₀ ha.le hb 2
    norm_num at h
    linarith only [h]
  have hlog : Real.log (2 * Real.pi * a) ≤ 779 / 1000 := by
    apply (Real.log_le_log (by positivity) ?_).trans log_pi_log_two_le
    nlinarith only [mul_le_mul_of_nonneg_left ha1 Real.pi_pos.le]
  have hp := odd_count_pole_coefficient_le ha ha1
  linarith only [odd_count_euler_bound, hlog, ha2, hp]

/-- Interior and exterior jumps pay the Weil form on the entire odd prime-free window. -/
theorem odd_primefree_Weil_from_jump_count {f : ℝ → ℝ} (hf : f ∈ realTests) {a : ℝ}
    (ha : 0 < a) (ha1 : 2 * a ≤ Real.log 2) (hs : tsupport f ⊆ Icc (-a) a)
    (ho : ∀ x, f (-x) = -f x) :
    (1 : ℝ) / 1000 * (∫ x, f x ^ 2) ≤ weilPair f f := by
  exact (mul_le_mul_of_nonneg_right (odd_primefree_count_coefficient_ge ha ha1)
    (integral_nonneg fun x => sq_nonneg _)).trans (odd_weil_count_floor hf ha ha1 hs ho)

/-- The odd primitive class has a positive count throughout the prime-free window. -/
theorem odd_primefree_primitiveH1_from_jump_count {a : ℝ} (ha : 0 < a)
    (ha1 : 2 * a ≤ Real.log 2) (x : ℝ × ℝ × realTestsAt a)
    (ho : ∀ u, x.2.2.1.1 (-u) = -x.2.2.1.1 u) :
    (1 : ℝ) / 2000 * (∫ u, (x.2.2.1.1 u) ^ 2) ≤
      primitiveH1 (scalingSubsurface (realTestsAt a)) x := by
  rw [primitiveH1_eq, scalingSubsurface_defect_self]
  have h := odd_primefree_Weil_from_jump_count x.2.2.1.2 ha ha1 x.2.2.2 ho
  linarith only [h]

end GaloisForLFunctions.LatticeSectionTheory
