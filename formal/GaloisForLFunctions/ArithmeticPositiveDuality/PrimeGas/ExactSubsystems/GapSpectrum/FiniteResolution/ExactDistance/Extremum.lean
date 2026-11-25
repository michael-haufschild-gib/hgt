import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.FiniteResolution.ExactDistance.Calibration

/-! # The exact Kolmogorov distance of the critical gap and its unique maximizing cutoff -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open Set Filter Topology MeasureTheory

private theorem reflected_gap (h : Ioi (0:ℝ)) (v : ℝ) :
    gapCDF h (-v) + (criticalGapLaw h : Measure ℝ).real (Iio v) = 1 := by
  let μ : Measure ℝ := criticalGapLaw h
  have he : μ.map Neg.neg = μ := sampledGapLaw_map_neg (excessDamping_gt h) (h.val/2)
  have hs : (Neg.neg : ℝ → ℝ) ⁻¹' Iic (-v) = Ici v := by ext t; simp
  have hr : gapCDF h (-v) = μ.real (Ici v) := by
    change (μ (Iic (-v))).toReal = _
    rw [← he,Measure.map_apply measurable_neg measurableSet_Iic,hs,he]
    rfl
  rw [hr,add_comm]
  simpa only [compl_Iio,probReal_univ] using
    (measureReal_add_measureReal_compl (μ := μ) (s := Iio v) measurableSet_Iio)

private theorem open_gap_margins (h : Ioi (0:ℝ)) {v : ℝ} (hv : 0 < v) :
    let δ := 1/2-rowIntegralFactor h
    let M := (criticalGapLaw h : Measure ℝ).real (Iio v)
    (-(collisionMass h/2)+δ*Real.exp (-v) ≤ M-laplaceCDF v) ∧
    M-laplaceCDF v ≤ collisionMass h/2-δ*(1-Real.exp (-v)) := by
  let μ : Measure ℝ := criticalGapLaw h
  let δ := 1/2-rowIntegralFactor h
  have hupper : μ.real (Iio v) ≤ gapCDF h v := measureReal_mono Iio_subset_Iic_self
  have hl : laplaceCDF v-collisionMass h/2+δ*Real.exp (-v) ≤ μ.real (Iio v) := by
    have hc : ContinuousAt (fun s : ℝ => laplaceCDF s-collisionMass h/2+δ*Real.exp (-s)) v :=
      ((laplaceCDF_derivative v).continuousAt.sub continuousAt_const).add
        (continuousAt_const.mul (Real.continuous_exp.comp continuous_neg).continuousAt)
    apply le_of_tendsto (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio v)))
    filter_upwards [self_mem_nhdsWithin (s := Iio v),nhdsWithin_le_nhds (Ioi_mem_nhds hv)] with s hs hpos
    have hm : gapCDF h s ≤ μ.real (Iio v) := measureReal_mono (Iic_subset_Iio.mpr hs)
    have he := (gap_positive_margins h (le_of_lt hpos)).1
    change -(collisionMass h/2)+δ*Real.exp (-s) ≤ gapCDF h s-laplaceCDF s at he
    linarith only [hm,he]
  change -(collisionMass h/2)+δ*Real.exp (-v) ≤ μ.real (Iio v)-laplaceCDF v ∧
    μ.real (Iio v)-laplaceCDF v ≤ collisionMass h/2-δ*(1-Real.exp (-v))
  have hu := (gap_positive_margins h hv.le).2
  change gapCDF h v-laplaceCDF v ≤ collisionMass h/2-δ*(1-Real.exp (-v)) at hu
  exact ⟨by linarith only [hl],by linarith only [hu,hupper]⟩

private theorem positive_margins_strict (h : Ioi (0:ℝ)) {v x : ℝ} (hv : 0 < v)
    (hl : -(collisionMass h/2)+(1/2-rowIntegralFactor h)*Real.exp (-v) ≤ x)
    (hu : x ≤ collisionMass h/2-(1/2-rowIntegralFactor h)*(1-Real.exp (-v))) :
    |x| < collisionMass h/2 := by
  have hd := sub_pos.mpr (rowIntegralFactor_lt_half h)
  have he := mul_pos hd (Real.exp_pos (-v))
  have hf := mul_pos hd (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hv)))
  exact abs_lt.mpr ⟨by linarith only [hl,he],by linarith only [hu,hf]⟩

/-- At every nonzero cutoff the discrepancy is strictly smaller than half the collision probability. -/
theorem gap_discrepancy_strict_off_zero (h : Ioi (0:ℝ)) {t : ℝ} (ht : t ≠ 0) :
    |gapCDF h t-laplaceCDF t| < collisionMass h/2 := by
  rcases lt_or_gt_of_ne ht with hn | hp
  · let v := -t
    have hv : 0 < v := neg_pos.mpr hn
    have he := open_gap_margins h hv
    have hm := positive_margins_strict h hv he.1 he.2
    have hr := reflected_gap h v
    have hf : laplaceCDF (-v) = 1-laplaceCDF v := by
      rw [laplaceCDF_negative (neg_nonpos.mpr hv.le),laplaceCDF_positive hv.le]
      ring
    have ht' : t = -v := (neg_neg t).symm
    have hx : gapCDF h t-laplaceCDF t =
        -((criticalGapLaw h : Measure ℝ).real (Iio v)-laplaceCDF v) := by
      rw [ht',hf]
      linarith only [hr]
    rwa [hx,abs_neg]
  · have he := gap_positive_margins h hp.le
    exact positive_margins_strict h hp he.1 he.2

private theorem gap_zero_error (h : Ioi (0:ℝ)) :
    |gapCDF h 0-laplaceCDF 0| = collisionMass h/2 := by
  rw [gapCDF_zero,show laplaceCDF 0 = 1/2 from laplace_cumulative_zero,
    show (1+collisionMass h)/2-1/2 = collisionMass h/2 by ring,
    abs_of_nonneg (div_nonneg (collisionMass_nonneg h) zero_le_two)]

/-- The exact distance is half the measured probability of the zero-energy line. -/
theorem gapKolmogorov_exact (h : Ioi (0:ℝ)) : gapKolmogorovDistance h = collisionMass h/2 := by
  refine le_antisymm (csSup_le (Set.range_nonempty _) ?_) (gapKolmogorov_bounds h).1
  rintro _ ⟨t,rfl⟩
  by_cases ht : t = 0
  · subst t
    exact (gap_zero_error h).le
  · exact (gap_discrepancy_strict_off_zero h ht).le

/-- The collision cutoff is the unique maximizer, including among the negative cutoffs at spectral atoms. -/
theorem gapKolmogorov_attained_iff (h : Ioi (0:ℝ)) (t : ℝ) :
    |gapCDF h t-laplaceCDF t| = gapKolmogorovDistance h ↔ t = 0 := by
  rw [gapKolmogorov_exact]
  constructor
  · intro he
    by_contra hn
    exact (gap_discrepancy_strict_off_zero h hn).ne he
  · rintro rfl
    exact gap_zero_error h

/-- Critical leading coefficient for the full uniform distance. -/
theorem gapKolmogorov_exact_quadratic_limit :
    Tendsto (fun h : Ioi (0:ℝ) => gapKolmogorovDistance h/h.val^2) criticalApproach (𝓝 ((riemannZeta 2).re/2)) := by
  apply (collisionMass_quadratic_limit.div_const 2).congr
  intro h
  rw [gapKolmogorov_exact]
  ring

#print axioms gap_discrepancy_strict_off_zero
#print axioms gapKolmogorov_exact
#print axioms gapKolmogorov_attained_iff
#print axioms gapKolmogorov_exact_quadratic_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
