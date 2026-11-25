import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.FiniteResolution.Cumulative
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.FiniteResolution.Sandwich

/-! # The uniform distribution error is comparable to the Gibbs collision probability -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open Set Filter MeasureTheory Topology

theorem gapCDF_zero (h : Ioi (0:ℝ)) : gapCDF h 0 = (1+collisionMass h)/2 :=
  sampled_cumulative_zero (excessDamping_gt h) (half_pos (show 0 < h.val from h.property)).ne'

theorem collisionMass_nonneg (h : Ioi (0:ℝ)) : 0 ≤ collisionMass h := by
  rw [collisionMass_as_sum]
  exact tsum_nonneg (fun n => mul_self_nonneg _)

private theorem positive_cdf_comparison (h : Ioi (0:ℝ)) {t : ℝ} (ht : 0 ≤ t) :
    gapCDF h t-gapCDF h 0 ≤ rowIntegralFactor h*(1-Real.exp (-t)) ∧
    rowIntegralFactor h*(1-Real.exp (-t)) ≤ gapCDF h t-gapCDF h 0+collisionMass h := by
  have he := positive_band_sandwich h ht
  dsimp only at he
  rwa [real_band_eq_cdf_sub _ ht] at he

/-- Calibration at infinity bounds the common multiplicative factor in every row integral. -/
theorem rowIntegralFactor_calibration (h : Ioi (0:ℝ)) :
    |rowIntegralFactor h-1/2| ≤ collisionMass h/2 := by
  have hq : Tendsto (fun t : ℝ => 1-Real.exp (-t)) atTop (𝓝 1) := by
    have he := (tendsto_const_nhds (x := (1:ℝ))).sub
      (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot)
    rw [sub_zero] at he
    exact he.congr (fun _ => rfl)
  have ha := (tendsto_const_nhds (x := rowIntegralFactor h)).mul hq
  have hp := (gapCDF_atTop h).sub_const (gapCDF h 0)
  have hl := le_of_tendsto_of_tendsto hp ha ((eventually_ge_atTop (0:ℝ)).mono fun t ht => (positive_cdf_comparison h ht).1)
  have hu := le_of_tendsto_of_tendsto ha (hp.add_const (collisionMass h))
    ((eventually_ge_atTop (0:ℝ)).mono fun t ht => (positive_cdf_comparison h ht).2)
  rw [mul_one,gapCDF_zero] at hl hu
  exact abs_le.mpr ⟨by linarith only [hl],by linarith only [hu]⟩

private theorem positive_cdf_error (h : Ioi (0:ℝ)) {t : ℝ} (ht : 0 ≤ t) :
    |gapCDF h t-laplaceCDF t| ≤ collisionMass h := by
  let q := 1-Real.exp (-t)
  have hq : 0 ≤ q := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht))
  have hq' : |q| ≤ 1 := by rw [abs_of_nonneg hq]; exact sub_le_self _ (Real.exp_pos _).le
  have hm : |(rowIntegralFactor h-1/2)*q| ≤ collisionMass h/2 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hq' (abs_nonneg _)).trans (by simpa only [mul_one] using rowIntegralFactor_calibration h)
  have hs := positive_cdf_comparison h ht
  rw [gapCDF_zero] at hs
  have hl : laplaceCDF t = (1+q)/2 := by rw [laplaceCDF_positive ht]; dsimp [q]; ring
  rw [hl]
  change gapCDF h t-(1+collisionMass h)/2 ≤ rowIntegralFactor h*q ∧
    rowIntegralFactor h*q ≤ gapCDF h t-(1+collisionMass h)/2+collisionMass h at hs
  exact abs_le.mpr ⟨by linarith only [hs.2,(abs_le.mp hm).1],by linarith only [hs.1,(abs_le.mp hm).2]⟩

private theorem gapCDF_reflection (h : Ioi (0:ℝ)) (v : ℝ) :
    gapCDF h (-v) + (criticalGapLaw h : Measure ℝ).real (Iio v) = 1 := by
  let μ : Measure ℝ := criticalGapLaw h
  have hr : μ.map Neg.neg = μ := sampledGapLaw_map_neg (excessDamping_gt h) (h.val/2)
  have hs : (Neg.neg : ℝ → ℝ) ⁻¹' Iic (-v) = Ici v := by ext t; simp
  have he := congrArg (fun m : Measure ℝ => m (Iic (-v))) hr
  change (μ.map Neg.neg) (Iic (-v)) = μ (Iic (-v)) at he
  rw [Measure.map_apply measurable_neg measurableSet_Iic,hs] at he
  have hc := measureReal_add_measureReal_compl (μ := μ) (s := Iio v) measurableSet_Iio
  change μ.real (Iic (-v)) + μ.real (Iio v) = 1
  simpa only [compl_Iio,measureReal_def,he,measure_univ,ENNReal.toReal_one,add_comm] using hc

/-- Every closed-half-line discrepancy is at most the diagonal probability. -/
theorem uniform_gap_cdf_error (h : Ioi (0:ℝ)) (t : ℝ) :
    |gapCDF h t-laplaceCDF t| ≤ collisionMass h := by
  by_cases ht : 0 ≤ t
  · exact positive_cdf_error h ht
  let v := -t
  have hv : 0 < v := neg_pos.mpr (lt_of_not_ge ht)
  let μ : Measure ℝ := criticalGapLaw h
  have hu : μ.real (Iio v) ≤ laplaceCDF v+collisionMass h := by
    have hx : μ.real (Iio v) ≤ gapCDF h v := measureReal_mono Iio_subset_Iic_self
    linarith only [hx,(abs_le.mp (positive_cdf_error h hv.le)).2]
  have hl : laplaceCDF v-collisionMass h ≤ μ.real (Iio v) := by
    have hlim : Tendsto laplaceCDF (𝓝[<] v) (𝓝 (laplaceCDF v)) :=
      (laplaceCDF_derivative v).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    apply le_of_tendsto (hlim.sub_const (collisionMass h))
    filter_upwards [self_mem_nhdsWithin (s := Iio v),nhdsWithin_le_nhds (Ioi_mem_nhds hv)] with s hlt hpos
    have hx : gapCDF h s ≤ μ.real (Iio v) := measureReal_mono (Iic_subset_Iio.mpr hlt)
    linarith only [hx,(abs_le.mp (positive_cdf_error h (le_of_lt hpos))).1]
  have hr := gapCDF_reflection h v
  have hf : laplaceCDF (-v) = 1-laplaceCDF v := by
    rw [laplaceCDF_negative (neg_nonpos.mpr hv.le),laplaceCDF_positive hv.le]
    ring
  have htv : t = -v := (neg_neg t).symm
  rw [htv,hf]
  change gapCDF h (-v) + μ.real (Iio v) = 1 at hr
  exact abs_le.mpr ⟨by linarith only [hr,hu],by linarith only [hr,hl]⟩

/-- Kolmogorov distance for the two measured laws. -/
def gapKolmogorovDistance (h : Ioi (0:ℝ)) :=
  sSup (range fun t => |gapCDF h t-laplaceCDF t|)

/-- The atom at zero supplies half the collision mass as a lower bound. -/
theorem gapKolmogorov_bounds (h : Ioi (0:ℝ)) :
    collisionMass h/2 ≤ gapKolmogorovDistance h ∧ gapKolmogorovDistance h ≤ collisionMass h := by
  let S := range fun t => |gapCDF h t-laplaceCDF t|
  have hb : ∀ a ∈ S, a ≤ collisionMass h := by rintro _ ⟨t,rfl⟩; exact uniform_gap_cdf_error h t
  have hm : |gapCDF h 0-laplaceCDF 0| ∈ S := ⟨0,rfl⟩
  have he : |gapCDF h 0-laplaceCDF 0| = collisionMass h/2 := by
    rw [gapCDF_zero,show laplaceCDF 0 = 1/2 from laplace_cumulative_zero,
      show (1+collisionMass h)/2-1/2 = collisionMass h/2 by ring,abs_of_nonneg (div_nonneg (collisionMass_nonneg h) zero_le_two)]
  constructor
  · rw [← he]
    exact le_csSup ⟨_,hb⟩ hm
  · exact csSup_le ⟨_,hm⟩ hb

theorem collisionMass_quadratic_limit :
    Tendsto (fun h : Ioi (0:ℝ) => collisionMass h/h.val^2) criticalApproach (𝓝 (riemannZeta 2).re) := by
  have hv : Tendsto (Subtype.val : Ioi (0:ℝ) → ℝ) criticalApproach (𝓝[>] 0) := tendsto_comap
  apply ((Complex.continuous_re.tendsto _).comp (constant_line_quadratic_limit.comp hv)).congr
  intro h
  change (overlapCoefficient ((1+h.val)/2) 0/(h.val:ℂ)^2).re = _
  rw [show (1+h.val)/2 = excessDamping h by unfold excessDamping; ring,← Complex.ofReal_pow,Complex.div_ofReal_re]
  rfl

/-- The normalized distance is eventually bounded below and above by any strict outer bounds. -/
theorem gapKolmogorov_quadratic_order {c C : ℝ} (hc : c < (riemannZeta 2).re/2) (hC : (riemannZeta 2).re < C) :
    ∀ᶠ h : Ioi (0:ℝ) in criticalApproach,
      c*h.val^2 ≤ gapKolmogorovDistance h ∧ gapKolmogorovDistance h ≤ C*h.val^2 := by
  have hlower : ∀ᶠ h : Ioi (0:ℝ) in criticalApproach, c < collisionMass h/h.val^2/2 :=
    (collisionMass_quadratic_limit.div_const 2) (Ioi_mem_nhds hc)
  have hupper : ∀ᶠ h : Ioi (0:ℝ) in criticalApproach, collisionMass h/h.val^2 < C :=
    collisionMass_quadratic_limit (Iio_mem_nhds hC)
  filter_upwards [hlower,hupper] with h hl hu
  have hs : 0 < h.val^2 := sq_pos_of_pos h.property
  have hh : c*h.val^2 ≤ collisionMass h/2 := by
    apply (le_div_iff₀ hs).mp
    exact hl.le.trans_eq (by ring)
  exact ⟨hh.trans (gapKolmogorov_bounds h).1,(gapKolmogorov_bounds h).2.trans ((div_le_iff₀ hs).mp hu.le)⟩

#print axioms gapCDF_zero
#print axioms collisionMass_nonneg
#print axioms rowIntegralFactor_calibration
#print axioms uniform_gap_cdf_error
#print axioms gapKolmogorov_bounds
#print axioms collisionMass_quadratic_limit
#print axioms gapKolmogorov_quadratic_order

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
