import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLogarithmicFactorHasOneNegativeZero

/-!
# The reciprocal logarithmic factor's cut density

Analytic divided differences remove the unique reciprocal pole. The remainder
has a continuous upper cut representative, including the logarithmic branch
endpoint, and is bounded on both sides of the cut. Its exact jump is a bounded
positive density, which supplies the measure for Cauchy inversion.
-/

open MeasureTheory Set Filter Topology Complex Metric
noncomputable section

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower

/-- The divided factor cancels its unique simple zero. -/
def dividedLogReferenceFactor : ℂ → ℂ :=
  dslope continuedLogReferenceFactor (-(logarithmicFactorZeroRadius : ℂ))

/-- Removing the reciprocal pole by divided differences also defines its regular value. -/
def regularLogReferenceReciprocal : ℂ → ℂ :=
  dslope (fun z => (dividedLogReferenceFactor z)⁻¹) (-(logarithmicFactorZeroRadius : ℂ))

theorem neg_logarithmicFactorZeroRadius_mem :
    -(logarithmicFactorZeroRadius : ℂ) ∈ logarithmicFactorContinuationDomain := by
  apply Or.inl
  simp only [Complex.neg_re, Complex.ofReal_re]
  linarith only [logarithmicFactorZeroRadius_lt_one]

theorem dividedLogReferenceFactor_neg_radius :
    dividedLogReferenceFactor (-(logarithmicFactorZeroRadius : ℂ)) =
      (logarithmicFactorReciprocalResidue : ℂ)⁻¹ := by
  rw [dividedLogReferenceFactor, dslope_same,
    hasDerivAt_continuedLogReferenceFactor_neg_radius.deriv]

theorem dividedLogReferenceFactor_ne_zero (z : ℂ) : dividedLogReferenceFactor z ≠ 0 := by
  by_cases hz : z = -(logarithmicFactorZeroRadius : ℂ)
  · rw [hz, dividedLogReferenceFactor_neg_radius]
    exact inv_ne_zero (by exact_mod_cast logarithmicFactorReciprocalResidue_pos.ne')
  · rw [dividedLogReferenceFactor, dslope_of_ne continuedLogReferenceFactor hz,
      slope_def_field, continuedLogReferenceFactor_neg_radius, sub_zero]
    exact div_ne_zero (mt (continuedLogReferenceFactor_eq_zero_iff z).mp hz) (sub_ne_zero.mpr hz)

theorem analyticOnNhd_dividedLogReferenceFactor :
    AnalyticOnNhd ℂ dividedLogReferenceFactor logarithmicFactorContinuationDomain := by
  have hd := (Complex.differentiableOn_dslope
    (isOpen_logarithmicFactorContinuationDomain.mem_nhds neg_logarithmicFactorZeroRadius_mem)).mpr
      analyticOnNhd_continuedLogReferenceFactor.differentiableOn
  intro z hz
  exact hd.analyticAt (isOpen_logarithmicFactorContinuationDomain.mem_nhds hz)

theorem analyticOnNhd_regularLogReferenceReciprocal :
    AnalyticOnNhd ℂ regularLogReferenceReciprocal logarithmicFactorContinuationDomain := by
  have hi : DifferentiableOn ℂ (fun z => (dividedLogReferenceFactor z)⁻¹)
      logarithmicFactorContinuationDomain := by
    intro z hz
    exact ((analyticOnNhd_dividedLogReferenceFactor z hz).differentiableAt.inv
      (dividedLogReferenceFactor_ne_zero z)).differentiableWithinAt
  have hd := (Complex.differentiableOn_dslope
    (isOpen_logarithmicFactorContinuationDomain.mem_nhds neg_logarithmicFactorZeroRadius_mem)).mpr hi
  intro z hz
  exact hd.analyticAt (isOpen_logarithmicFactorContinuationDomain.mem_nhds hz)

/-- Away from the pole, the analytic remainder is literal subtraction of its residue. -/
theorem regularLogReferenceReciprocal_eq {z : ℂ}
    (hz : z ≠ -(logarithmicFactorZeroRadius : ℂ)) :
    regularLogReferenceReciprocal z = (continuedLogReferenceFactor z)⁻¹ -
      (logarithmicFactorReciprocalResidue : ℂ) / (z + (logarithmicFactorZeroRadius : ℂ)) := by
  rw [regularLogReferenceReciprocal, dslope_of_ne _ hz, slope_def_field,
    dividedLogReferenceFactor_neg_radius, inv_inv]
  rw [dividedLogReferenceFactor, dslope_of_ne _ hz, slope_def_field,
    continuedLogReferenceFactor_neg_radius, sub_zero, sub_neg_eq_add]
  have hzp : z + (logarithmicFactorZeroRadius : ℂ) ≠ 0 := by
    simpa only [sub_neg_eq_add] using sub_ne_zero.mpr hz
  have hk := mt (continuedLogReferenceFactor_eq_zero_iff z).mp hz
  field_simp [hzp, hk]

private theorem nonreal_ne_neg_radius {z : ℂ} (hz : z.im ≠ 0) :
    z ≠ -(logarithmicFactorZeroRadius : ℂ) := by
  intro he
  apply hz
  rw [he]
  simp only [Complex.neg_im, Complex.ofReal_im, neg_zero]

theorem regularLogReferenceReciprocal_eq_nonreal {z : ℂ} (hz : z.im ≠ 0) :
    regularLogReferenceReciprocal z = (complexLogReferenceFactor z)⁻¹ -
      (logarithmicFactorReciprocalResidue : ℂ) / (z + (logarithmicFactorZeroRadius : ℂ)) := by
  rw [regularLogReferenceReciprocal_eq (nonreal_ne_neg_radius hz),
    continuedLogReferenceFactor_eq (Or.inr hz)]

theorem regularLogReferenceReciprocal_conj {z : ℂ} (hz : z.im ≠ 0) :
    regularLogReferenceReciprocal (starRingEnd ℂ z) =
      starRingEnd ℂ (regularLogReferenceReciprocal z) := by
  have hc : (starRingEnd ℂ z).im ≠ 0 := by
    simpa only [Complex.conj_im, neg_ne_zero] using hz
  rw [regularLogReferenceReciprocal_eq_nonreal hc, regularLogReferenceReciprocal_eq_nonreal hz,
    complexLogReferenceFactor_conj (Or.inr hz)]
  simp only [map_sub, map_inv₀, map_div₀, map_add, Complex.conj_ofReal]

/-- Subtracting the pole preserves uniform reciprocal decay in all nonreal directions. -/
theorem tendsto_regularLogReferenceReciprocal_nonreal :
    Tendsto regularLogReferenceReciprocal
      (cocompact ℂ ⊓ 𝓟 {z : ℂ | z.im ≠ 0}) (nhds 0) := by
  have hn : Tendsto (fun z : ℂ => ‖z + (logarithmicFactorZeroRadius : ℂ)‖)
      (cocompact ℂ) atTop := by
    simpa only [dist_eq_norm, sub_neg_eq_add] using
      tendsto_dist_right_cocompact_atTop (-(logarithmicFactorZeroRadius : ℂ))
  have hz : Tendsto (fun z : ℂ => z + (logarithmicFactorZeroRadius : ℂ))
      (cocompact ℂ) (Bornology.cobounded ℂ) := tendsto_norm_atTop_iff_cobounded.mp hn
  have hi := Filter.tendsto_inv₀_cobounded.comp hz
  have hr : Tendsto (fun z : ℂ => (logarithmicFactorReciprocalResidue : ℂ) /
      (z + (logarithmicFactorZeroRadius : ℂ)))
      (cocompact ℂ ⊓ 𝓟 {z : ℂ | z.im ≠ 0}) (nhds 0) := by
    simpa only [Function.comp_def, mul_zero, div_eq_mul_inv] using!
      (tendsto_const_nhds.mul hi).mono_left inf_le_left
  have hd := tendsto_inv_complexLogReferenceFactor_nonreal.sub hr
  rw [sub_zero] at hd
  apply hd.congr'
  filter_upwards [(Filter.eventually_principal.mpr (fun z hz => hz)).filter_mono inf_le_right]
    with z hz
  exact (regularLogReferenceReciprocal_eq_nonreal hz).symm

/-- The continuous part of the reciprocal factor's positive Stieltjes measure. -/
def logarithmicFactorCutDensity (t : ℝ) : ℝ :=
  2 * logReferenceFactor t / ((2 + Real.log (t ^ 2 - 1)) ^ 2 + Real.pi ^ 2)

theorem logarithmicFactorCutDensity_pos (t : ℝ) : 0 < logarithmicFactorCutDensity t := by
  unfold logarithmicFactorCutDensity
  exact div_pos (mul_pos (by norm_num) (zero_lt_one.trans_le (one_le_logReferenceFactor t)))
    (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos Real.pi_pos))

/-- The principal logarithm on the negative cut is the upper boundary value. -/
theorem logarithmicLaplaceSymbol_upper_cut {t : ℝ} (ht : 1 < t) :
    logarithmicLaplaceSymbol (-(-(t : ℂ)) ^ 2) =
      ((1 + (1 / 2 : ℝ) * Real.log (t ^ 2 - 1) : ℝ) : ℂ) +
        ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
  have ht2 : 1 < t ^ 2 := by nlinarith only [ht]
  have he : 1 + -(-(t : ℂ)) ^ 2 = ((1 - t ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have hn : ‖((1 - t ^ 2 : ℝ) : ℂ)‖ = t ^ 2 - 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith only [ht2])]
    ring
  have ha : Complex.arg ((1 - t ^ 2 : ℝ) : ℂ) = Real.pi :=
    Complex.arg_eq_pi_iff.mpr ⟨by simpa only [Complex.ofReal_re] using sub_neg.mpr ht2,
      Complex.ofReal_im _⟩
  rw [logarithmicLaplaceSymbol, he, Complex.log, hn, ha]
  push_cast
  ring

theorem continuedLogReferenceFactor_upper_cut {t : ℝ} (ht : 1 < t) :
    continuedLogReferenceFactor (-(t : ℂ)) =
      (((1 + (1 / 2 : ℝ) * Real.log (t ^ 2 - 1) : ℝ) : ℂ) +
        ((Real.pi / 2 : ℝ) : ℂ) * Complex.I) / (logReferenceFactor t : ℂ) := by
  have hr : (-(t : ℂ)).re < 0 := by
    simpa only [Complex.neg_re, Complex.ofReal_re] using neg_neg_of_pos (zero_lt_one.trans ht)
  rw [continuedLogReferenceFactor, if_pos hr, logarithmicLaplaceSymbol_upper_cut ht,
    neg_neg, complexLogReferenceFactor_ofReal (zero_lt_one.trans ht)]

private theorem conjugate_fraction_jump (a b k : ℝ) (hb : b ≠ 0) :
    (k : ℂ) / ((a : ℂ) + (b : ℂ) * Complex.I) -
      (k : ℂ) / ((a : ℂ) - (b : ℂ) * Complex.I) =
        -(2 * (b : ℂ) * (k : ℂ) * Complex.I) / ((a : ℂ) ^ 2 + (b : ℂ) ^ 2) := by
  have hp : (a : ℂ) + (b : ℂ) * Complex.I ≠ 0 := by
    intro he
    have hh := congrArg Complex.im he
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add, Complex.zero_im] at hh
    exact hb hh
  have hm : (a : ℂ) - (b : ℂ) * Complex.I ≠ 0 := by
    intro he
    have hh := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_sub, Complex.zero_im] at hh
    exact hb (neg_eq_zero.mp hh)
  have hD : (a : ℂ) ^ 2 + (b : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast (add_pos_of_nonneg_of_pos (sq_nonneg a) (sq_pos_of_ne_zero hb)).ne'
  field_simp [hp, hm, hD]
  ring_nf
  have hI : Complex.I ^ 3 = -Complex.I := by
    calc
      _ = Complex.I ^ 2 * Complex.I := by ring
      _ = -Complex.I := by rw [Complex.I_sq]; ring
  rw [hI]
  ring

/-- The upper-minus-lower reciprocal jump is exactly the positive density. -/
theorem regularLogReferenceReciprocal_cut_jump {t : ℝ} (ht : 1 < t) :
    regularLogReferenceReciprocal (-(t : ℂ)) -
      starRingEnd ℂ (regularLogReferenceReciprocal (-(t : ℂ))) =
        -(2 * (Real.pi : ℂ) * Complex.I) * (logarithmicFactorCutDensity t : ℂ) := by
  have htne : -(t : ℂ) ≠ -(logarithmicFactorZeroRadius : ℂ) := by
    intro he
    have he' : t = logarithmicFactorZeroRadius := by exact_mod_cast neg_injective he
    linarith only [he', ht, logarithmicFactorZeroRadius_lt_one]
  have hk : (logReferenceFactor t : ℂ) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans_le (one_le_logReferenceFactor t)).ne'
  let a : ℝ := 2 + Real.log (t ^ 2 - 1)
  have hval : continuedLogReferenceFactor (-(t : ℂ)) =
      ((a : ℂ) + (Real.pi : ℂ) * Complex.I) / (2 * (logReferenceFactor t : ℂ)) := by
    rw [continuedLogReferenceFactor_upper_cut ht]
    dsimp only [a]
    push_cast
    field_simp [hk]
  rw [regularLogReferenceReciprocal_eq htne, hval]
  simp only [map_sub, map_div₀, map_add, map_mul, Complex.conj_ofReal,
    Complex.conj_I, map_neg, map_ofNat, inv_div, mul_neg, ← sub_eq_add_neg]
  calc
    _ = (2 * (logReferenceFactor t : ℂ)) / ((a : ℂ) + (Real.pi : ℂ) * Complex.I) -
        (2 * (logReferenceFactor t : ℂ)) / ((a : ℂ) - (Real.pi : ℂ) * Complex.I) := by ring
    _ = -(2 * (Real.pi : ℂ) * ((2 * logReferenceFactor t : ℝ) : ℂ) * Complex.I) /
        ((a : ℂ) ^ 2 + (Real.pi : ℂ) ^ 2) := by
      simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using
        conjugate_fraction_jump a Real.pi (2 * logReferenceFactor t) Real.pi_ne_zero
    _ = _ := by
      dsimp only [a, logarithmicFactorCutDensity]
      push_cast
      ring

/-- Along the upper half-plane the continued factor has its literal cut value. -/
theorem continuousWithinAt_continuedLogReferenceFactor_upper_cut {t : ℝ} (ht : 1 < t) :
    ContinuousWithinAt continuedLogReferenceFactor {z : ℂ | 0 ≤ z.im} (-(t : ℂ)) := by
  let q : ℂ → ℂ := fun z => 1 - z ^ 2
  have htre : (-(t : ℂ)).re < 0 := by
    simpa only [Complex.neg_re, Complex.ofReal_re] using neg_neg_of_pos (zero_lt_one.trans ht)
  have hqre : (q (-(t : ℂ))).re < 0 := by
    simp only [q, Complex.sub_re, Complex.one_re, pow_two, Complex.mul_re,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, neg_zero, mul_zero, sub_zero]
    nlinarith only [ht]
  have hqim : (q (-(t : ℂ))).im = 0 := by
    simp only [q, Complex.sub_im, Complex.one_im, pow_two,
      Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      neg_zero, mul_zero, zero_mul, add_zero, sub_zero]
  have hqcont : Continuous q := by dsimp only [q]; fun_prop
  have hmap : Tendsto q (𝓝[{z : ℂ | 0 ≤ z.im}] (-(t : ℂ)))
      (𝓝[{z : ℂ | 0 ≤ z.im}] (q (-(t : ℂ)))) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hqcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      ((isOpen_lt Complex.continuous_re continuous_const).eventually_mem htre).filter_mono
        nhdsWithin_le_nhds] with z hz hr
    simp only [q, Complex.sub_im, Complex.one_im, pow_two, Complex.mul_im, zero_sub]
    nlinarith only [mul_nonpos_of_nonpos_of_nonneg hr.le hz]
  have hlog := (Complex.continuousWithinAt_log_of_re_neg_of_im_zero hqre hqim).tendsto.comp hmap
  have hsymbol : Tendsto (fun z : ℂ => logarithmicLaplaceSymbol (-z ^ 2))
      (𝓝[{z : ℂ | 0 ≤ z.im}] (-(t : ℂ)))
      (nhds (logarithmicLaplaceSymbol (-(-(t : ℂ)) ^ 2))) := by
    simpa only [q, logarithmicLaplaceSymbol, sub_eq_add_neg, Function.comp_def] using!
      tendsto_const_nhds.add (tendsto_const_nhds.mul hlog)
  have hK : ContinuousAt complexLogReferenceFactor (t : ℂ) :=
    (differentiableOn_complexLogReferenceFactor.differentiableAt
      (Complex.isOpen_slitPlane.mem_nhds (Or.inl (zero_lt_one.trans ht)))).continuousAt
  have hK' : ContinuousAt complexLogReferenceFactor (-(-(t : ℂ))) := by
    simpa only [neg_neg] using hK
  have hneg : ContinuousAt (fun z : ℂ => -z) (-(t : ℂ)) := by fun_prop
  have hden : Tendsto (fun z : ℂ => complexLogReferenceFactor (-z))
      (𝓝[{z : ℂ | 0 ≤ z.im}] (-(t : ℂ)))
      (nhds (complexLogReferenceFactor (-(-(t : ℂ))))) := by
    have hc : ContinuousAt (fun z : ℂ => complexLogReferenceFactor (-z)) (-(t : ℂ)) := by
      simpa only [Function.comp_def, neg_neg] using!
        (hK'.comp (f := fun z : ℂ => -z) (x := -(t : ℂ)) hneg)
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have hquot := hsymbol.div hden (complexLogReferenceFactor_ne_zero (-(-(t : ℂ))))
  change Tendsto _ _ (nhds (continuedLogReferenceFactor (-(t : ℂ))))
  rw [continuedLogReferenceFactor, if_pos htre]
  apply hquot.congr'
  filter_upwards [((isOpen_lt Complex.continuous_re continuous_const).eventually_mem htre).filter_mono
    nhdsWithin_le_nhds] with z hz
  simp only [Pi.div_apply, continuedLogReferenceFactor, if_pos hz]

/-- The regular reciprocal is continuous at every interior point of the upper cut. -/
theorem continuousWithinAt_regularLogReferenceReciprocal_upper_cut {t : ℝ} (ht : 1 < t) :
    ContinuousWithinAt regularLogReferenceReciprocal {z : ℂ | 0 ≤ z.im} (-(t : ℂ)) := by
  have htne : -(t : ℂ) ≠ -(logarithmicFactorZeroRadius : ℂ) := by
    intro he
    have he' : t = logarithmicFactorZeroRadius := by exact_mod_cast neg_injective he
    linarith only [he', ht, logarithmicFactorZeroRadius_lt_one]
  have hK := mt (continuedLogReferenceFactor_eq_zero_iff (-(t : ℂ))).mp htne
  have hden : -(t : ℂ) + (logarithmicFactorZeroRadius : ℂ) ≠ 0 := by
    simpa only [sub_neg_eq_add] using sub_ne_zero.mpr htne
  have hr : ContinuousAt
      (fun z : ℂ => (logarithmicFactorReciprocalResidue : ℂ) /
        (z + (logarithmicFactorZeroRadius : ℂ))) (-(t : ℂ)) :=
    continuousAt_const.div (continuousAt_id.add continuousAt_const) hden
  have hc := ((continuousWithinAt_continuedLogReferenceFactor_upper_cut ht).inv₀ hK).sub
    hr.continuousWithinAt
  change Tendsto _ _ (nhds (regularLogReferenceReciprocal (-(t : ℂ))))
  rw [regularLogReferenceReciprocal_eq htne]
  apply hc.tendsto.congr'
  filter_upwards [(isOpen_ne.eventually_mem htne).filter_mono nhdsWithin_le_nhds] with z hz
  exact (regularLogReferenceReciprocal_eq hz).symm

/-- The reflected reciprocal vanishes at the logarithmic branch point from every direction. -/
theorem tendsto_inv_continuedLogReferenceFactor_at_neg_one :
    Tendsto (fun z : ℂ => (continuedLogReferenceFactor z)⁻¹)
      (𝓝[≠] (-1 : ℂ)) (nhds 0) := by
  let q : ℂ → ℂ := fun z => 1 - z ^ 2
  have hqcont : Continuous q := by dsimp only [q]; fun_prop
  have hq0 : q (-1 : ℂ) = 0 := by norm_num [q]
  have hre : ∀ᶠ z in 𝓝[≠] (-1 : ℂ), z.re < 0 :=
    ((isOpen_lt Complex.continuous_re continuous_const).eventually_mem
      (by norm_num : (-1 : ℂ).re < 0)).filter_mono nhdsWithin_le_nhds
  have hqne : ∀ᶠ z in 𝓝[≠] (-1 : ℂ), q z ≠ 0 := by
    filter_upwards [hre, self_mem_nhdsWithin] with z hr hz
    have hzm : z ≠ -1 := by simpa only [mem_compl_iff, mem_singleton_iff] using hz
    intro hq
    have hp : (z - 1) * (z + 1) = 0 := by
      dsimp only [q] at hq
      linear_combination -hq
    rcases mul_eq_zero.mp hp with h | h
    · have he : z = 1 := sub_eq_zero.mp h
      norm_num [he] at hr
    · apply hzm
      linear_combination h
  have hqn : Tendsto (fun z => ‖q z‖) (𝓝[≠] (-1 : ℂ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h := hqcont.continuousAt.norm.tendsto.mono_left
        (show 𝓝[≠] (-1 : ℂ) ≤ 𝓝 (-1 : ℂ) from nhdsWithin_le_nhds)
      simpa only [hq0, norm_zero] using h
    · filter_upwards [hqne] with z hz
      exact norm_pos_iff.mpr hz
  have hlog := Real.tendsto_log_nhdsGT_zero.comp hqn
  have hn : Tendsto (fun z : ℂ => ‖logarithmicLaplaceSymbol (-z ^ 2)‖)
      (𝓝[≠] (-1 : ℂ)) atTop := by
    refine tendsto_atTop.mpr fun B => ?_
    filter_upwards [hlog.eventually_le_atBot (-2 * (B + 1))] with z hz
    have hr := Complex.re_le_norm (-logarithmicLaplaceSymbol (-z ^ 2))
    rw [Complex.neg_re, norm_neg] at hr
    have he : (logarithmicLaplaceSymbol (-z ^ 2)).re = 1 + (1 / 2 : ℝ) * Real.log ‖q z‖ := by
      simp only [logarithmicLaplaceSymbol, Complex.add_re, Complex.one_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, Complex.log_re,
        q, sub_eq_add_neg, neg_zero, add_zero]
    rw [he] at hr
    change Real.log ‖q z‖ ≤ -2 * (B + 1) at hz
    linarith only [hr, hz]
  have hinv : Tendsto (fun z : ℂ => (logarithmicLaplaceSymbol (-z ^ 2))⁻¹)
      (𝓝[≠] (-1 : ℂ)) (nhds 0) :=
    Filter.tendsto_inv₀_cobounded.comp (tendsto_norm_atTop_iff_cobounded.mp hn)
  have hK : ContinuousAt complexLogReferenceFactor (1 : ℂ) :=
    (differentiableOn_complexLogReferenceFactor.differentiableAt
      (Complex.isOpen_slitPlane.mem_nhds (Or.inl (by norm_num)))).continuousAt
  have hK' : ContinuousAt complexLogReferenceFactor (-(-1 : ℂ)) := by
    simpa only [neg_neg] using hK
  have hneg : ContinuousAt (fun z : ℂ => -z) (-1 : ℂ) := by fun_prop
  have hnum : Tendsto (fun z : ℂ => complexLogReferenceFactor (-z))
      (𝓝[≠] (-1 : ℂ)) (nhds (complexLogReferenceFactor 1)) := by
    have hc : ContinuousAt (fun z : ℂ => complexLogReferenceFactor (-z)) (-1 : ℂ) := by
      simpa only [Function.comp_def, neg_neg] using!
        (hK'.comp (f := fun z : ℂ => -z) (x := (-1 : ℂ)) hneg)
    simpa only [neg_neg] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hh := hnum.mul hinv
  rw [mul_zero] at hh
  apply hh.congr'
  filter_upwards [hre] with z hz
  rw [continuedLogReferenceFactor, if_pos hz, div_eq_mul_inv, mul_inv_rev, inv_inv]

/-- The regular reciprocal has a finite value at the end of its branch cut. -/
theorem tendsto_regularLogReferenceReciprocal_at_neg_one :
    Tendsto regularLogReferenceReciprocal (𝓝[≠] (-1 : ℂ))
      (nhds (-(logarithmicFactorReciprocalResidue : ℂ) /
        ((logarithmicFactorZeroRadius : ℂ) - 1))) := by
  have hb : (logarithmicFactorZeroRadius : ℂ) - 1 ≠ 0 := by
    exact_mod_cast (sub_ne_zero.mpr logarithmicFactorZeroRadius_lt_one.ne)
  have hp : (-1 : ℂ) ≠ -(logarithmicFactorZeroRadius : ℂ) := by
    intro he
    apply hb
    linear_combination he
  have hadd : (-1 : ℂ) + (logarithmicFactorZeroRadius : ℂ) =
      (logarithmicFactorZeroRadius : ℂ) - 1 := by ring
  have hden : (-1 : ℂ) + (logarithmicFactorZeroRadius : ℂ) ≠ 0 := by
    rwa [hadd]
  have hc : ContinuousAt
      (fun z : ℂ => (logarithmicFactorReciprocalResidue : ℂ) /
        (z + (logarithmicFactorZeroRadius : ℂ))) (-1 : ℂ) :=
    continuousAt_const.div (continuousAt_id.add continuousAt_const) hden
  have hr : Tendsto
      (fun z : ℂ => (logarithmicFactorReciprocalResidue : ℂ) /
        (z + (logarithmicFactorZeroRadius : ℂ))) (𝓝[≠] (-1 : ℂ))
      (nhds ((logarithmicFactorReciprocalResidue : ℂ) /
        ((logarithmicFactorZeroRadius : ℂ) - 1))) := by
    simpa only [hadd] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have h := tendsto_inv_continuedLogReferenceFactor_at_neg_one.sub hr
  simp only [zero_sub, neg_div] at h ⊢
  apply h.congr'
  filter_upwards [(isOpen_ne.eventually_mem hp).filter_mono nhdsWithin_le_nhds] with z hz
  exact (regularLogReferenceReciprocal_eq hz).symm

/-- The upper cut representative includes the continuous branch-end value. -/
def upperRegularLogReferenceReciprocal : ℂ → ℂ :=
  Function.update regularLogReferenceReciprocal (-1)
    (-(logarithmicFactorReciprocalResidue : ℂ) / ((logarithmicFactorZeroRadius : ℂ) - 1))

theorem upperRegularLogReferenceReciprocal_eq {z : ℂ} (hz : z ≠ -1) :
    upperRegularLogReferenceReciprocal z = regularLogReferenceReciprocal z := by
  exact Function.update_of_ne hz _ _

theorem continuousAt_upperRegularLogReferenceReciprocal_neg_one :
    ContinuousAt upperRegularLogReferenceReciprocal (-1) := by
  exact continuousAt_update_same.mpr tendsto_regularLogReferenceReciprocal_at_neg_one

theorem analyticOnNhd_upperRegularLogReferenceReciprocal :
    AnalyticOnNhd ℂ upperRegularLogReferenceReciprocal logarithmicFactorContinuationDomain := by
  intro z hz
  have hne : z ≠ -1 := by
    intro he
    simp only [logarithmicFactorContinuationDomain, mem_setOf_eq, he, Complex.neg_re,
      Complex.one_re, lt_self_iff_false, Complex.neg_im, Complex.one_im, neg_zero,
      ne_eq, not_true_eq_false, or_self] at hz
  apply (analyticOnNhd_regularLogReferenceReciprocal z hz).congr
  filter_upwards [isOpen_ne.eventually_mem hne] with w hw
  exact (upperRegularLogReferenceReciprocal_eq hw).symm

/-- Patching the branch endpoint makes the upper cut representative continuous on the closed half-plane. -/
theorem continuousOn_upperRegularLogReferenceReciprocal :
    ContinuousOn upperRegularLogReferenceReciprocal {z : ℂ | 0 ≤ z.im} := by
  intro z hz
  by_cases hD : z ∈ logarithmicFactorContinuationDomain
  · exact (analyticOnNhd_upperRegularLogReferenceReciprocal z hD).continuousAt.continuousWithinAt
  · have hp : z.re ≤ -1 ∧ z.im = 0 := by
      simpa only [logarithmicFactorContinuationDomain, mem_setOf_eq, not_or,
        not_lt, not_ne_iff] using hD
    rcases lt_or_eq_of_le hp.1 with hr | hr
    · have ht : 1 < -z.re := by linarith only [hr]
      have he : z = -((-z.re : ℝ) : ℂ) := by
        apply Complex.ext
        · simp only [Complex.neg_re, Complex.ofReal_re, neg_neg]
        · simpa only [Complex.neg_im, Complex.ofReal_im, neg_zero] using hp.2
      have hne : z ≠ -1 := by
        intro he'
        have hh := congrArg Complex.re he'
        simp only [Complex.neg_re, Complex.one_re] at hh
        linarith only [hr, hh]
      have hc : ContinuousWithinAt regularLogReferenceReciprocal {z : ℂ | 0 ≤ z.im} z := by
        rw [he]
        exact continuousWithinAt_regularLogReferenceReciprocal_upper_cut ht
      change Tendsto _ _ (nhds (upperRegularLogReferenceReciprocal z))
      rw [upperRegularLogReferenceReciprocal_eq hne]
      apply hc.tendsto.congr'
      filter_upwards [(isOpen_ne.eventually_mem hne).filter_mono nhdsWithin_le_nhds] with w hw
      exact (upperRegularLogReferenceReciprocal_eq hw).symm
    · have he : z = -1 := by
        apply Complex.ext
        · simpa only [Complex.neg_re, Complex.one_re] using hr
        · simpa only [Complex.neg_im, Complex.one_im, neg_zero] using hp.2
      rw [he]
      exact continuousAt_upperRegularLogReferenceReciprocal_neg_one.continuousWithinAt

#print axioms continuousOn_upperRegularLogReferenceReciprocal

/-- Continuity at the cut and uniform far-field decay bound the whole upper representative. -/
theorem exists_bound_upperRegularLogReferenceReciprocal :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 0 ≤ z.im → ‖upperRegularLogReferenceReciprocal z‖ ≤ C := by
  have he : ∀ᶠ z in cocompact ℂ ⊓ 𝓟 {z : ℂ | z.im ≠ 0},
      ‖regularLogReferenceReciprocal z‖ ≤ 1 := by
    have h := tendsto_regularLogReferenceReciprocal_nonreal.norm.eventually
      (eventually_lt_nhds (by norm_num : ‖(0 : ℂ)‖ < (1 : ℝ)))
    exact h.mono fun z hz => hz.le
  have hfar : ∀ᶠ z in cocompact ℂ, z.im ≠ 0 → ‖regularLogReferenceReciprocal z‖ ≤ 1 :=
    Filter.eventually_inf_principal.mp he
  obtain ⟨K, hK, hKfar⟩ := Filter.mem_cocompact.mp hfar
  have hclosed : IsClosed {z : ℂ | 0 ≤ z.im} :=
    isClosed_le continuous_const Complex.continuous_im
  have hcompact : IsCompact (K ∩ {z : ℂ | 0 ≤ z.im}) := hK.inter_right hclosed
  obtain ⟨B, hB⟩ := hcompact.exists_bound_of_continuousOn
    (continuousOn_upperRegularLogReferenceReciprocal.mono inter_subset_right)
  let C : ℝ := max 1 B
  have hC : 0 < C := zero_lt_one.trans_le (le_max_left _ _)
  have hi : ∀ z : ℂ, 0 < z.im → ‖upperRegularLogReferenceReciprocal z‖ ≤ C := by
    intro z hz
    by_cases hk : z ∈ K
    · exact (hB z ⟨hk, hz.le⟩).trans (le_max_right _ _)
    · have hne : z ≠ -1 := by
        intro he'
        simp only [he', Complex.neg_im, Complex.one_im, neg_zero, lt_self_iff_false] at hz
      rw [upperRegularLogReferenceReciprocal_eq hne]
      exact (hKfar hk hz.ne').trans (le_max_left _ _)
  refine ⟨C, hC, fun z hz => ?_⟩
  have hp : Tendsto (fun e : ℝ => z + (e : ℂ) * Complex.I)
      (𝓝[>] (0 : ℝ)) (𝓝[{w : ℂ | 0 ≤ w.im}] z) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : ContinuousAt (fun e : ℝ => z + (e : ℂ) * Complex.I) 0 := by fun_prop
      simpa only [Complex.ofReal_zero, zero_mul, add_zero] using!
        hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with e he
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
        mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
      exact add_nonneg hz (le_of_lt he)
  have hl := (continuousOn_upperRegularLogReferenceReciprocal z hz).tendsto.comp hp
  apply le_of_tendsto_of_tendsto hl.norm tendsto_const_nhds
  filter_upwards [self_mem_nhdsWithin] with e he
  apply hi
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
    mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
  exact add_pos_of_nonneg_of_pos hz he

/-- The same bound controls both sides of the slit by conjugation. -/
theorem exists_bound_regularLogReferenceReciprocal :
    ∃ C : ℝ, 0 < C ∧
      (∀ z : ℂ, 0 ≤ z.im → ‖upperRegularLogReferenceReciprocal z‖ ≤ C) ∧
      (∀ z : ℂ, z.im ≠ 0 → ‖regularLogReferenceReciprocal z‖ ≤ C) := by
  obtain ⟨C, hC, hupper⟩ := exists_bound_upperRegularLogReferenceReciprocal
  refine ⟨C, hC, hupper, fun z hz => ?_⟩
  have hu : ∀ w : ℂ, 0 < w.im → ‖regularLogReferenceReciprocal w‖ ≤ C := by
    intro w hw
    have hne : w ≠ -1 := by
      intro he
      simp only [he, Complex.neg_im, Complex.one_im, neg_zero, lt_self_iff_false] at hw
    simpa only [upperRegularLogReferenceReciprocal_eq hne] using hupper w hw.le
  rcases lt_or_gt_of_ne hz with hn | hp
  · have hc : 0 < (starRingEnd ℂ z).im := by
      simpa only [Complex.conj_im] using neg_pos.mpr hn
    have h := hu (starRingEnd ℂ z) hc
    rwa [regularLogReferenceReciprocal_conj hz, Complex.norm_conj] at h
  · exact hu z hp

#print axioms exists_bound_regularLogReferenceReciprocal

/-- Analytic continuation carries conjugation through the real interval above the cut. -/
theorem regularLogReferenceReciprocal_conj_of_mem {z : ℂ}
    (hz : z ∈ logarithmicFactorContinuationDomain) :
    regularLogReferenceReciprocal (starRingEnd ℂ z) =
      starRingEnd ℂ (regularLogReferenceReciprocal z) := by
  by_cases hi : z.im ≠ 0
  · exact regularLogReferenceReciprocal_conj hi
  · have hi0 : z.im = 0 := not_ne_iff.mp hi
    have hzstar : starRingEnd ℂ z = z := by
      apply Complex.ext
      · simp only [Complex.conj_re]
      · simp only [Complex.conj_im, hi0, neg_zero]
    have hsD : starRingEnd ℂ z ∈ logarithmicFactorContinuationDomain := by simpa only [hzstar] using hz
    have hp : Tendsto (fun e : ℝ => z + (e : ℂ) * Complex.I) (𝓝[>] (0 : ℝ)) (nhds z) := by
      have hc : ContinuousAt (fun e : ℝ => z + (e : ℂ) * Complex.I) 0 := by fun_prop
      simpa only [Complex.ofReal_zero, zero_mul, add_zero] using!
        hc.tendsto.mono_left nhdsWithin_le_nhds
    have hstar : Continuous (fun w : ℂ => starRingEnd ℂ w) := by fun_prop
    have hleft := (analyticOnNhd_regularLogReferenceReciprocal _ hsD).continuousAt.tendsto.comp
      ((hstar.tendsto z).comp hp)
    have hright := (hstar.tendsto (regularLogReferenceReciprocal z)).comp
      ((analyticOnNhd_regularLogReferenceReciprocal z hz).continuousAt.tendsto.comp hp)
    have heq : (fun e : ℝ => regularLogReferenceReciprocal
        (starRingEnd ℂ (z + (e : ℂ) * Complex.I))) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun e : ℝ => starRingEnd ℂ (regularLogReferenceReciprocal
          (z + (e : ℂ) * Complex.I))) := by
      filter_upwards [self_mem_nhdsWithin] with e he
      apply regularLogReferenceReciprocal_conj
      simpa only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
        mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, hi0, zero_add] using he.ne'
    exact tendsto_nhds_unique (hleft.congr' heq) hright

/-- The upper boundary jump vanishes above the cut and equals the explicit density below it. -/
theorem upperRegularLogReferenceReciprocal_jump (x : ℝ) :
    upperRegularLogReferenceReciprocal (x : ℂ) -
      starRingEnd ℂ (upperRegularLogReferenceReciprocal (x : ℂ)) =
        if x < -1 then -(2 * (Real.pi : ℂ) * Complex.I) *
          (logarithmicFactorCutDensity (-x) : ℂ) else 0 := by
  by_cases hx : x < -1
  · rw [if_pos hx]
    have hne : (x : ℂ) ≠ -1 := by exact_mod_cast hx.ne
    rw [upperRegularLogReferenceReciprocal_eq hne]
    have ht : 1 < -x := by linarith only [hx]
    simpa only [Complex.ofReal_neg, neg_neg] using regularLogReferenceReciprocal_cut_jump ht
  · rw [if_neg hx]
    by_cases he : x = -1
    · subst x
      simp [upperRegularLogReferenceReciprocal]
    · have hgt : -1 < x := lt_of_le_of_ne (le_of_not_gt hx) (Ne.symm he)
      have hne : (x : ℂ) ≠ -1 := by exact_mod_cast he
      rw [upperRegularLogReferenceReciprocal_eq hne]
      have hc := regularLogReferenceReciprocal_conj_of_mem
        (z := (x : ℂ)) (Or.inl hgt)
      rw [Complex.conj_ofReal] at hc
      exact sub_eq_zero.mpr hc

/-- Boundedness of the analytic remainder bounds its positive cut density. -/
theorem logarithmicFactorCutDensity_bounded :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 < t → logarithmicFactorCutDensity t ≤ C := by
  obtain ⟨B, hB, hupper, _⟩ := exists_bound_regularLogReferenceReciprocal
  refine ⟨B / Real.pi, div_pos hB Real.pi_pos, fun t ht => ?_⟩
  have hne : -(t : ℂ) ≠ -1 := by
    intro he
    have he' : t = 1 := by exact_mod_cast neg_injective he
    linarith only [ht, he']
  have hb : ‖regularLogReferenceReciprocal (-(t : ℂ))‖ ≤ B := by
    have h := hupper (-(t : ℂ)) (by simp only [Complex.neg_im, Complex.ofReal_im, neg_zero, le_refl])
    simpa only [upperRegularLogReferenceReciprocal_eq hne] using h
  have hn := norm_sub_le (regularLogReferenceReciprocal (-(t : ℂ)))
    (starRingEnd ℂ (regularLogReferenceReciprocal (-(t : ℂ))))
  rw [regularLogReferenceReciprocal_cut_jump ht, Complex.norm_conj] at hn
  have hd : ‖-(2 * (Real.pi : ℂ) * Complex.I) * (logarithmicFactorCutDensity t : ℂ)‖ =
      2 * Real.pi * logarithmicFactorCutDensity t := by
    simp only [norm_mul, norm_neg, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, Complex.norm_I, mul_one,
      abs_of_pos (logarithmicFactorCutDensity_pos t)]
  rw [hd] at hn
  apply (le_div_iff₀ Real.pi_pos).mpr
  nlinarith only [hn, hb]

/-- On the positive axis the regular remainder is a real reciprocal minus its positive pole. -/
theorem regularLogReferenceReciprocal_ofReal {s : ℝ} (hs : 0 < s) :
    regularLogReferenceReciprocal (s : ℂ) =
      ((logReferenceFactor s)⁻¹ - logarithmicFactorReciprocalResidue /
        (s + logarithmicFactorZeroRadius) : ℝ) := by
  have hne : (s : ℂ) ≠ -(logarithmicFactorZeroRadius : ℂ) := by
    intro he
    have he' : s = -logarithmicFactorZeroRadius := by exact_mod_cast he
    linarith only [hs, he', logarithmicFactorZeroRadius_pos]
  rw [regularLogReferenceReciprocal_eq hne, continuedLogReferenceFactor_ofReal hs]
  push_cast
  rfl

#print axioms upperRegularLogReferenceReciprocal_jump
#print axioms logarithmicFactorCutDensity_bounded

#print axioms analyticOnNhd_regularLogReferenceReciprocal
#print axioms regularLogReferenceReciprocal_cut_jump

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
