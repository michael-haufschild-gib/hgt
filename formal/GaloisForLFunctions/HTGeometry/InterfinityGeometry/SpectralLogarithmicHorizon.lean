import GaloisForLFunctions.HTGeometry.InterfinityGeometry.SpectralDeficientAsymptotics

/-!
# The logarithmic contact law at the cut

Exactly at the cut the projective normalization is logarithmic: the transported finite part of a
smooth chart satisfies

`η₀(e^{-V·} h) / log V → − c h(0)`.

The mechanism is the exponential-integral splitting
`∫₀^V (e^{-t} − 1)/t dt = C + ∫₁^V e^{-t}/t dt − log V`, whose middle term stays bounded by
`e^{-1}`, so the whole cut integral is `− log V + O(1)`.
-/

namespace GaloisForLFunctions.HTGeometry.Interfinity

open MeasureTheory Set Filter Topology

noncomputable section

variable {V : ℝ}

/-! ## The cut integral at the cut -/

theorem gammaDefect_zero (t : ℝ) : gammaDefect 0 t = (Real.exp (-t) - 1) / t := by
  rw [gammaDefect, zero_sub, Real.rpow_neg_one, div_eq_mul_inv]

theorem cutIntegral_zero_eq (hV : 0 < V) :
    cutIntegral 0 V = ∫ t in (0 : ℝ)..V, gammaDefect 0 t := by
  rw [cutIntegral_scaling hV, neg_zero, Real.rpow_zero, one_mul]

theorem integrableOn_expDivId {b : ℝ} (hb : 1 ≤ b) :
    IntervalIntegrable (fun t : ℝ => Real.exp (-t) / t) volume 1 b := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hb]
  exact (Real.continuous_exp.comp continuous_neg).continuousOn.div continuousOn_id
    fun x hx => ne_of_gt (lt_of_lt_of_le zero_lt_one hx.1)

theorem integral_exp_neg_interval {b : ℝ} :
    (∫ t in (1 : ℝ)..b, Real.exp (-t)) = Real.exp (-1) - Real.exp (-b) := by
  have hderiv : ∀ x ∈ Set.uIcc (1 : ℝ) b, HasDerivAt (fun t : ℝ => -Real.exp (-t))
      (Real.exp (-x)) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => -t) (-1 : ℝ) x := hasDerivAt_neg x
    have h2 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (Real.exp (-x) * (-1)) x := h1.exp
    have h3 := h2.neg
    simpa using h3
  have hint : IntervalIntegrable (fun t : ℝ => Real.exp (-t)) volume 1 b :=
    ((Real.continuous_exp.comp continuous_neg)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

/-- The exponential-integral tail stays bounded. -/
theorem abs_integral_expDivId_le {b : ℝ} (hb : 1 ≤ b) :
    |∫ t in (1 : ℝ)..b, Real.exp (-t) / t| ≤ 1 := by
  have hnonneg : (0 : ℝ) ≤ ∫ t in (1 : ℝ)..b, Real.exp (-t) / t := by
    refine intervalIntegral.integral_nonneg hb fun t ht => ?_
    have ht1 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht.1
    positivity
  have hle : (∫ t in (1 : ℝ)..b, Real.exp (-t) / t) ≤ ∫ t in (1 : ℝ)..b, Real.exp (-t) := by
    refine intervalIntegral.integral_mono_on hb (integrableOn_expDivId hb)
      (((Real.continuous_exp.comp continuous_neg)).intervalIntegrable _ _) fun t ht => ?_
    have ht1 : (1 : ℝ) ≤ t := ht.1
    have hexp : (0 : ℝ) < Real.exp (-t) := Real.exp_pos _
    rw [div_le_iff₀ (lt_of_lt_of_le zero_lt_one ht1)]
    nlinarith
  have hval : (∫ t in (1 : ℝ)..b, Real.exp (-t)) ≤ 1 := by
    rw [integral_exp_neg_interval]
    have h1 : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
    have h2 : (0 : ℝ) < Real.exp (-b) := Real.exp_pos _
    linarith
  rw [abs_of_nonneg hnonneg]
  linarith

/-- **The exponential-integral splitting of the cut integral.** -/
theorem cutIntegral_zero_split (hV : 1 ≤ V) :
    cutIntegral 0 V = (∫ t in (0 : ℝ)..1, gammaDefect 0 t) +
      (∫ t in (1 : ℝ)..V, Real.exp (-t) / t) - Real.log V := by
  have hV0 : (0 : ℝ) < V := lt_of_lt_of_le zero_lt_one hV
  have hsplit : (∫ t in (0 : ℝ)..V, gammaDefect 0 t) =
      (∫ t in (0 : ℝ)..1, gammaDefect 0 t) + ∫ t in (1 : ℝ)..V, gammaDefect 0 t := by
    refine (intervalIntegral.integral_add_adjacent_intervals ?_ ?_).symm
    · exact (integrableOn_gammaDefect_Ioc (a := 0) (by norm_num)).intervalIntegrable_of_Ioc
        (by norm_num)
    · refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hV]
      refine ContinuousOn.congr ?_ fun t ht => (gammaDefect_zero t).symm
      exact (((Real.continuous_exp.comp continuous_neg).sub continuous_const).continuousOn.div
        continuousOn_id fun x hx => ne_of_gt (lt_of_lt_of_le zero_lt_one hx.1))
  have htail : (∫ t in (1 : ℝ)..V, gammaDefect 0 t) =
      (∫ t in (1 : ℝ)..V, Real.exp (-t) / t) - Real.log V := by
    have hcongr : (∫ t in (1 : ℝ)..V, gammaDefect 0 t) =
        ∫ t in (1 : ℝ)..V, (Real.exp (-t) / t - t⁻¹) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hV] at ht
      have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht.1
      rw [gammaDefect_zero]
      field_simp
    have hinv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 1 V := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hV]
      exact continuousOn_id.inv₀ fun x hx => ne_of_gt (lt_of_lt_of_le zero_lt_one hx.1)
    rw [hcongr, intervalIntegral.integral_sub (integrableOn_expDivId hV) hinv,
      integral_inv_of_pos zero_lt_one hV0]
    simp
  rw [cutIntegral_zero_eq hV0, hsplit, htail]
  ring

/-- **The logarithmic contact law for the cut integral.** -/
theorem tendsto_cutIntegral_zero_div_log :
    Tendsto (fun V : ℝ => cutIntegral 0 V / Real.log V) atTop (𝓝 (-1)) := by
  set C : ℝ := ∫ t in (0 : ℝ)..1, gammaDefect 0 t with hC
  have hlog : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have hbdd : Tendsto (fun V : ℝ => (C + ∫ t in (1 : ℝ)..V, Real.exp (-t) / t) / Real.log V)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (Filter.Tendsto.div_atTop
      (f := fun _ : ℝ => |C| + 1) tendsto_const_nhds hlog)
    filter_upwards [eventually_ge_atTop (1 : ℝ), hlog.eventually_gt_atTop 0] with V hV hlogV
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hlogV]
    gcongr
    calc |C + ∫ t in (1 : ℝ)..V, Real.exp (-t) / t|
        ≤ |C| + |∫ t in (1 : ℝ)..V, Real.exp (-t) / t| := abs_add_le _ _
      _ ≤ |C| + 1 := by linarith [abs_integral_expDivId_le hV]
  have hone : Tendsto (fun V : ℝ => (C + ∫ t in (1 : ℝ)..V, Real.exp (-t) / t) / Real.log V - 1)
      atTop (𝓝 (0 - 1)) := hbdd.sub tendsto_const_nhds
  rw [zero_sub] at hone
  refine hone.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ), hlog.eventually_gt_atTop 0] with V hV hlogV
  rw [cutIntegral_zero_split hV, ← hC]
  field_simp

end

end GaloisForLFunctions.HTGeometry.Interfinity
