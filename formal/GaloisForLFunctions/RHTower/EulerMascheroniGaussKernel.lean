import GaloisForLFunctions.RHTower.EulerMascheroniExponentialIntegral

/-!
# The Euler–Mascheroni constant as the Gauss kernel integral

`γ = ∫_0^∞ ( e^{-t}/(1 - e^{-t}) - e^{-t}/t ) dt`.

Both halves diverge logarithmically at the origin and the divergences cancel: on `(ε,∞)`

* `∫ e^{-t}/(1-e^{-t}) dt = -log(1 - e^{-ε})`,
* `∫ e^{-t}/t dt = -log ε + Ein(ε) - γ`,

so their difference is `γ - Ein(ε) + log((1-e^{-ε})/ε)`, and `Ein(ε) → 0`,
`(1-e^{-ε})/ε → 1` as `ε → 0+`.

This is the `s = 1` case of Gauss's integral representation of the digamma function, and the
ingredient that converts the corpus's Gauss *series* for digamma into that integral.
-/

open MeasureTheory Set Filter Real

noncomputable section

namespace RHTower

/-! ## Elementary positivity and the two truncated integrals -/

theorem one_sub_exp_neg_pos {t : ℝ} (ht : 0 < t) : 0 < 1 - Real.exp (-t) := by
  have h : Real.exp (-t) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  linarith

theorem exp_neg_le_one_sub_exp_neg_div (t : ℝ) :
    t * Real.exp (-t) ≤ 1 - Real.exp (-t) := by
  have hexp : t + 1 ≤ Real.exp t := Real.add_one_le_exp t
  have hinv : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  nlinarith [mul_nonneg (sub_nonneg.mpr hexp) (le_of_lt (Real.exp_pos (-t))),
    Real.exp_pos (-t)]

/-- `∫_ε^∞ e^{-t}/(1 - e^{-t}) dt = -log(1 - e^{-ε})`. -/
theorem integral_geometricGaussKernel_Ioi {ε : ℝ} (hε : 0 < ε) :
    (∫ t in Ioi ε, Real.exp (-t) / (1 - Real.exp (-t)))
      = -Real.log (1 - Real.exp (-ε)) := by
  have hmono : ∀ t : ℝ, ε ≤ t → Real.exp (-ε) ≥ Real.exp (-t) := by
    intro t ht
    exact Real.exp_le_exp.mpr (by linarith)
  have hposε : 0 < 1 - Real.exp (-ε) := one_sub_exp_neg_pos hε
  have hderiv : ∀ t ∈ Ioi ε,
      HasDerivAt (fun u : ℝ => Real.log (1 - Real.exp (-u)))
        (Real.exp (-t) / (1 - Real.exp (-t))) t := by
    intro t ht
    have ht0 : 0 < t := lt_trans hε ht
    have hpos : 0 < 1 - Real.exp (-t) := one_sub_exp_neg_pos ht0
    have hbase : HasDerivAt (fun u : ℝ => 1 - Real.exp (-u)) (Real.exp (-t)) t := by
      have h1 : HasDerivAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-t)) t := by
        simpa using (hasDerivAt_neg t).exp
      simpa using h1.const_sub 1
    have := hbase.log (ne_of_gt hpos)
    simpa using this
  have hcont : ContinuousWithinAt (fun u : ℝ => Real.log (1 - Real.exp (-u))) (Ici ε) ε := by
    have hbase : ContinuousAt (fun u : ℝ => 1 - Real.exp (-u)) ε := by fun_prop
    exact (hbase.log (ne_of_gt hposε)).continuousWithinAt
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-t) / (1 - Real.exp (-t))) (Ioi ε) volume := by
    have hmeas : AEStronglyMeasurable
        (fun t : ℝ => Real.exp (-t) / (1 - Real.exp (-t))) (volume.restrict (Ioi ε)) := by
      apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
      intro t ht
      have ht0 : 0 < t := lt_trans hε ht
      exact (ContinuousAt.continuousWithinAt (by
        have hb : ContinuousAt (fun u : ℝ => 1 - Real.exp (-u)) t := by fun_prop
        exact ContinuousAt.div (by fun_prop) hb (ne_of_gt (one_sub_exp_neg_pos ht0))))
    have hbound : IntegrableOn (fun t : ℝ => (1 - Real.exp (-ε))⁻¹ * Real.exp (-t))
        (Ioi ε) volume := by
      have h : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi ε) volume :=
        exp_neg_integrableOn_Ioi ε zero_lt_one |>.congr_fun (fun t _ => by simp)
          measurableSet_Ioi
      exact h.const_mul _
    refine hbound.mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans hε ht
    have hpos : 0 < 1 - Real.exp (-t) := one_sub_exp_neg_pos ht0
    have hge : 1 - Real.exp (-ε) ≤ 1 - Real.exp (-t) := by
      have := hmono t (le_of_lt ht)
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [div_le_iff₀ hpos]
    have hexp : 0 < Real.exp (-t) := Real.exp_pos _
    have : (1 - Real.exp (-ε))⁻¹ * Real.exp (-t) * (1 - Real.exp (-ε))
        ≤ (1 - Real.exp (-ε))⁻¹ * Real.exp (-t) * (1 - Real.exp (-t)) := by
      apply mul_le_mul_of_nonneg_left hge
      positivity
    calc Real.exp (-t) = (1 - Real.exp (-ε))⁻¹ * Real.exp (-t) * (1 - Real.exp (-ε)) := by
          field_simp
      _ ≤ _ := this
  have htend : Tendsto (fun u : ℝ => Real.log (1 - Real.exp (-u))) atTop (nhds 0) := by
    have hexp : Tendsto (fun u : ℝ => Real.exp (-u)) atTop (nhds 0) := by
      simpa [Function.comp_def] using Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
    have hsub : Tendsto (fun u : ℝ => 1 - Real.exp (-u)) atTop (nhds 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℝ))).sub hexp
    have := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hsub
    simpa [Function.comp_def] using this
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint htend
  simpa using h

/-- `|Ein(ε)| ≤ ε`. -/
theorem abs_ein_le {ε : ℝ} (hε : 0 ≤ ε) : |ein ε| ≤ ε := by
  have hbound : ∀ t ∈ Set.uIoc (0 : ℝ) ε, ‖einProfile t‖ ≤ 1 := by
    intro t ht
    rw [Set.uIoc_of_le hε] at ht
    rw [Real.norm_eq_abs, abs_of_nonneg (einProfile_nonneg (le_of_lt ht.1))]
    exact einProfile_le_one (le_of_lt ht.1)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (C := 1) hbound
  rw [ein, Real.norm_eq_abs] at *
  simpa [abs_of_nonneg hε] using h

theorem tendsto_ein_nhdsWithin_zero : Tendsto ein (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  refine squeeze_zero_norm' (a := fun ε : ℝ => ε) ?_ (tendsto_id.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [Real.norm_eq_abs]
  exact abs_ein_le (le_of_lt hε)

/-- `∫_ε^∞ e^{-t}/t dt = -log ε + Ein(ε) - γ` for `0 < ε ≤ 1`. -/
theorem integral_expNegDiv_Ioi_small {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ t in Ioi ε, Real.exp (-t) / t)
      = -Real.log ε + ein ε - Real.eulerMascheroniConstant := by
  have hsplitSet : Set.Ioc ε 1 ∪ Set.Ioi (1 : ℝ) = Set.Ioi ε := Set.Ioc_union_Ioi_eq_Ioi hε1
  have hdisj : Disjoint (Set.Ioc ε 1) (Set.Ioi (1 : ℝ)) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx' (not_lt.mpr hx.2)
  have hIoc : IntegrableOn (fun t : ℝ => Real.exp (-t) / t) (Set.Ioc ε 1) volume := by
    have h := intervalIntegrable_exp_neg_div hε hε1
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le hε1] at h
  have hunion := MeasureTheory.setIntegral_union (μ := volume)
    (f := fun t : ℝ => Real.exp (-t) / t) hdisj measurableSet_Ioi hIoc
    integrableOn_exp_neg_div_Ioi_one
  rw [hsplitSet] at hunion
  have hval : (∫ s in Set.Ioc ε 1, Real.exp (-s) / s)
      = ∫ s in ε..1, Real.exp (-s) / s :=
    (intervalIntegral.integral_of_le hε1).symm
  rw [hval] at hunion
  -- the finite piece
  have hcongr : (∫ s in ε..1, Real.exp (-s) / s)
      = ∫ s in ε..1, (1 / s - einProfile s) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hε1] at ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hε ht.1
    rw [einProfile, if_neg (ne_of_gt ht0)]
    ring
  have hfin : (∫ s in ε..1, Real.exp (-s) / s)
      = -Real.log ε - (frullaniHead - ein ε) := by
    rw [hcongr, intervalIntegral.integral_sub (intervalIntegrable_one_div_pos hε hε1)
      (intervalIntegrable_einProfile_pos hε hε1),
      integral_one_div_of_pos hε zero_lt_one]
    have hein : (∫ s in ε..1, einProfile s) = frullaniHead - ein ε := by
      have hadd := intervalIntegral.integral_add_adjacent_intervals
        (μ := volume) (f := einProfile) (a := 0) (b := ε) (c := 1)
        (intervalIntegrable_einProfile (le_of_lt hε))
        (intervalIntegrable_einProfile_pos hε hε1)
      rw [← ein, ← frullaniHead] at hadd
      linarith
    rw [hein, one_div, Real.log_inv]
  rw [hfin] at hunion
  rw [hunion, show (∫ x in Ioi (1 : ℝ), Real.exp (-x) / x) = frullaniTail from rfl]
  have hγ := frullani_eq_eulerMascheroni
  linarith

/-! ## The Gauss kernel and its integral -/

/-- The integrand `e^{-t}/t - e^{-t}/(1 - e^{-t})` of Gauss's representation at `s = 1`. -/
def gaussKernel (t : ℝ) : ℝ :=
  Real.exp (-t) / t - Real.exp (-t) / (1 - Real.exp (-t))

theorem abs_gaussKernel_le {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    |gaussKernel t| ≤ Real.exp 1 := by
  have hpos : 0 < 1 - Real.exp (-t) := one_sub_exp_neg_pos ht
  have hlow : t * Real.exp (-t) ≤ 1 - Real.exp (-t) := exp_neg_le_one_sub_exp_neg_div t
  have hexp1 : Real.exp (-1 : ℝ) ≤ Real.exp (-t) := Real.exp_le_exp.mpr (by linarith)
  have hlow' : t * Real.exp (-1 : ℝ) ≤ 1 - Real.exp (-t) := by
    have : t * Real.exp (-1 : ℝ) ≤ t * Real.exp (-t) :=
      mul_le_mul_of_nonneg_left hexp1 (le_of_lt ht)
    linarith
  have hnum : |1 - Real.exp (-t) - t| ≤ t ^ 2 := by
    have h := Real.abs_exp_sub_one_sub_id_le (x := -t) (by rw [abs_of_nonpos (by linarith)]; linarith)
    have heq : Real.exp (-t) - 1 - -t = -(1 - Real.exp (-t) - t) := by ring
    rw [heq, abs_neg] at h
    simpa using h
  have hfactor : gaussKernel t
      = Real.exp (-t) * (1 - Real.exp (-t) - t) / (t * (1 - Real.exp (-t))) := by
    rw [gaussKernel]
    field_simp
  rw [hfactor, abs_div, abs_mul]
  have hden : |t * (1 - Real.exp (-t))| = t * (1 - Real.exp (-t)) :=
    abs_of_nonneg (by positivity)
  have hdenpos : 0 < t * (1 - Real.exp (-t)) := by positivity
  rw [hden, div_le_iff₀ hdenpos]
  have hexpabs : |Real.exp (-t)| = Real.exp (-t) := abs_of_nonneg (le_of_lt (Real.exp_pos _))
  rw [hexpabs]
  have hexple : Real.exp (-t) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  have hstep : Real.exp (-t) * |1 - Real.exp (-t) - t| ≤ t ^ 2 := by
    calc Real.exp (-t) * |1 - Real.exp (-t) - t| ≤ 1 * t ^ 2 := by
          apply mul_le_mul hexple hnum (abs_nonneg _) (by norm_num)
      _ = t ^ 2 := by ring
  have hkey : t ^ 2 ≤ Real.exp 1 * (t * (1 - Real.exp (-t))) := by
    have hexpinv : Real.exp 1 * Real.exp (-1 : ℝ) = 1 := by
      rw [← Real.exp_add]; norm_num
    have : Real.exp 1 * (t * (t * Real.exp (-1 : ℝ))) = t ^ 2 := by
      nlinarith [hexpinv]
    nlinarith [Real.exp_pos (1 : ℝ), mul_le_mul_of_nonneg_left hlow'
      (le_of_lt (mul_pos (Real.exp_pos (1 : ℝ)) ht))]
  linarith

theorem continuousOn_gaussKernel : ContinuousOn gaussKernel (Ioi 0) := by
  intro t ht
  have ht0 : 0 < t := ht
  have hpos : 0 < 1 - Real.exp (-t) := one_sub_exp_neg_pos ht0
  refine ContinuousAt.continuousWithinAt ?_
  apply ContinuousAt.sub
  · exact ContinuousAt.div (by fun_prop) continuousAt_id (ne_of_gt ht0)
  · exact ContinuousAt.div (by fun_prop) (by fun_prop) (ne_of_gt hpos)

theorem integrableOn_gaussKernel_Ioc :
    IntegrableOn gaussKernel (Ioc (0 : ℝ) 1) volume := by
  have hmeas : AEStronglyMeasurable gaussKernel (volume.restrict (Ioc (0 : ℝ) 1)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    exact continuousOn_gaussKernel.mono (fun t ht => ht.1)
  have hconst : IntegrableOn (fun _ : ℝ => Real.exp 1) (Ioc (0 : ℝ) 1) volume :=
    continuous_const.integrableOn_Ioc
  refine hconst.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Real.norm_eq_abs]
  exact abs_gaussKernel_le ht.1 ht.2

theorem integrableOn_gaussKernel_Ioi_one :
    IntegrableOn gaussKernel (Ioi (1 : ℝ)) volume := by
  have hmeas : AEStronglyMeasurable gaussKernel (volume.restrict (Ioi (1 : ℝ))) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact continuousOn_gaussKernel.mono (Set.Ioi_subset_Ioi zero_le_one)
  have hexpInt : IntegrableOn (fun t : ℝ => (1 + (1 - Real.exp (-1 : ℝ))⁻¹) * Real.exp (-t))
      (Ioi (1 : ℝ)) volume := by
    have h : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi (1 : ℝ)) volume :=
      integrableOn_exp_neg_Ioi_one
    exact h.const_mul _
  refine hexpInt.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
  have hpos : 0 < 1 - Real.exp (-t) := one_sub_exp_neg_pos ht0
  have hge : 1 - Real.exp (-1 : ℝ) ≤ 1 - Real.exp (-t) := by
    have := Real.exp_le_exp.mpr (show -t ≤ (-1 : ℝ) by linarith)
    linarith
  have hpos1 : 0 < 1 - Real.exp (-1 : ℝ) := one_sub_exp_neg_pos zero_lt_one
  have hexppos : 0 < Real.exp (-t) := Real.exp_pos _
  rw [Real.norm_eq_abs, gaussKernel]
  have h1 : |Real.exp (-t) / t| ≤ Real.exp (-t) := by
    rw [abs_of_nonneg (by positivity), div_le_iff₀ ht0]
    nlinarith
  have h2 : |Real.exp (-t) / (1 - Real.exp (-t))| ≤ (1 - Real.exp (-1 : ℝ))⁻¹ * Real.exp (-t) := by
    rw [abs_of_nonneg (by positivity), div_le_iff₀ hpos]
    have : (1 - Real.exp (-1 : ℝ))⁻¹ * Real.exp (-t) * (1 - Real.exp (-1 : ℝ))
        ≤ (1 - Real.exp (-1 : ℝ))⁻¹ * Real.exp (-t) * (1 - Real.exp (-t)) := by
      apply mul_le_mul_of_nonneg_left hge
      positivity
    calc Real.exp (-t)
        = (1 - Real.exp (-1 : ℝ))⁻¹ * Real.exp (-t) * (1 - Real.exp (-1 : ℝ)) := by field_simp
      _ ≤ _ := this
  calc |Real.exp (-t) / t - Real.exp (-t) / (1 - Real.exp (-t))|
      ≤ |Real.exp (-t) / t| + |Real.exp (-t) / (1 - Real.exp (-t))| := abs_sub _ _
    _ ≤ Real.exp (-t) + (1 - Real.exp (-1 : ℝ))⁻¹ * Real.exp (-t) := by linarith
    _ = (1 + (1 - Real.exp (-1 : ℝ))⁻¹) * Real.exp (-t) := by ring

theorem integrableOn_gaussKernel : IntegrableOn gaussKernel (Ioi (0 : ℝ)) volume := by
  have hsplit : Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ) = Ioi (0 : ℝ) :=
    Set.Ioc_union_Ioi_eq_Ioi (le_of_lt zero_lt_one)
  rw [← hsplit]
  exact integrableOn_gaussKernel_Ioc.union integrableOn_gaussKernel_Ioi_one


/-! ## The truncated integral and its limit -/

theorem integral_gaussKernel_Ioi_eq {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ t in Ioi ε, gaussKernel t)
      = -Real.eulerMascheroniConstant + ein ε
          + Real.log (1 - Real.exp (-ε)) - Real.log ε := by
  have h1 : IntegrableOn (fun t : ℝ => Real.exp (-t) / t) (Ioi ε) volume := by
    have hsub : Ioi ε ⊆ Ioi (0 : ℝ) := Set.Ioi_subset_Ioi (le_of_lt hε)
    have hIoc : IntegrableOn (fun t : ℝ => Real.exp (-t) / t) (Set.Ioc ε 1) volume := by
      have h := intervalIntegrable_exp_neg_div hε hε1
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le hε1] at h
    have hsplit : Set.Ioc ε 1 ∪ Set.Ioi (1 : ℝ) = Set.Ioi ε := Set.Ioc_union_Ioi_eq_Ioi hε1
    rw [← hsplit]
    exact hIoc.union integrableOn_exp_neg_div_Ioi_one
  have h2 : IntegrableOn (fun t : ℝ => Real.exp (-t) / (1 - Real.exp (-t))) (Ioi ε) volume := by
    have hmeas : AEStronglyMeasurable
        (fun t : ℝ => Real.exp (-t) / (1 - Real.exp (-t))) (volume.restrict (Ioi ε)) := by
      apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
      intro t ht
      have ht0 : 0 < t := lt_trans hε ht
      exact ContinuousAt.continuousWithinAt (by
        have hb : ContinuousAt (fun u : ℝ => 1 - Real.exp (-u)) t := by fun_prop
        exact ContinuousAt.div (by fun_prop) hb (ne_of_gt (one_sub_exp_neg_pos ht0)))
    have hposε : 0 < 1 - Real.exp (-ε) := one_sub_exp_neg_pos hε
    have hbound : IntegrableOn (fun t : ℝ => (1 - Real.exp (-ε))⁻¹ * Real.exp (-t))
        (Ioi ε) volume := by
      have h : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi ε) volume :=
        exp_neg_integrableOn_Ioi ε zero_lt_one |>.congr_fun (fun t _ => by simp)
          measurableSet_Ioi
      exact h.const_mul _
    refine hbound.mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans hε ht
    have hpos : 0 < 1 - Real.exp (-t) := one_sub_exp_neg_pos ht0
    have htlt : ε < t := ht
    have hge : 1 - Real.exp (-ε) ≤ 1 - Real.exp (-t) := by
      have := Real.exp_le_exp.mpr (show -t ≤ -ε by linarith)
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ hpos]
    have hstep : (1 - Real.exp (-ε))⁻¹ * Real.exp (-t) * (1 - Real.exp (-ε))
        ≤ (1 - Real.exp (-ε))⁻¹ * Real.exp (-t) * (1 - Real.exp (-t)) := by
      apply mul_le_mul_of_nonneg_left hge
      positivity
    calc Real.exp (-t) = (1 - Real.exp (-ε))⁻¹ * Real.exp (-t) * (1 - Real.exp (-ε)) := by
          field_simp
      _ ≤ _ := hstep
  have hsub : (∫ t in Ioi ε, gaussKernel t)
      = (∫ t in Ioi ε, Real.exp (-t) / t)
        - ∫ t in Ioi ε, Real.exp (-t) / (1 - Real.exp (-t)) := by
    rw [← MeasureTheory.integral_sub h1 h2]
    rfl
  rw [hsub, integral_expNegDiv_Ioi_small hε hε1, integral_geometricGaussKernel_Ioi hε]
  ring

theorem norm_integral_gaussKernel_Ioc {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |∫ t in Ioc (0 : ℝ) ε, gaussKernel t| ≤ Real.exp 1 * ε := by
  have hfin : volume (Ioc (0 : ℝ) ε) < ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have hbd : ∀ t ∈ Ioc (0 : ℝ) ε, ‖gaussKernel t‖ ≤ Real.exp 1 := by
    intro t ht
    rw [Real.norm_eq_abs]
    exact abs_gaussKernel_le ht.1 (le_trans ht.2 hε1)
  have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const hfin hbd
  rw [Real.norm_eq_abs] at h
  have hmeas : (volume : Measure ℝ).real (Ioc (0 : ℝ) ε) = ε := by
    rw [MeasureTheory.Measure.real, Real.volume_Ioc, sub_zero,
      ENNReal.toReal_ofReal (le_of_lt hε)]
  rwa [hmeas] at h

/-- **Gauss's representation of the Euler–Mascheroni constant.**
`∫_0^∞ ( e^{-t}/t - e^{-t}/(1-e^{-t}) ) dt = -γ`. -/
theorem integral_gaussKernel :
    (∫ t in Ioi (0 : ℝ), gaussKernel t) = -Real.eulerMascheroniConstant := by
  have hsmall : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Ioi 0), ε ≤ 1 :=
    Filter.eventually_of_mem
      (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (by norm_num))) (fun x hx => hx)
  -- the truncated integral converges to the full one
  have hlim1 : Tendsto (fun ε : ℝ => ∫ t in Ioi ε, gaussKernel t)
      (nhdsWithin 0 (Ioi 0)) (nhds (∫ t in Ioi (0 : ℝ), gaussKernel t)) := by
    have hdiff : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        (∫ t in Ioi (0 : ℝ), gaussKernel t) - (∫ t in Ioi ε, gaussKernel t)
          = ∫ t in Ioc (0 : ℝ) ε, gaussKernel t := by
      intro ε hε hε1
      have hsplit : Ioc (0 : ℝ) ε ∪ Ioi ε = Ioi (0 : ℝ) := Set.Ioc_union_Ioi_eq_Ioi (le_of_lt hε)
      have hdisj : Disjoint (Ioc (0 : ℝ) ε) (Ioi ε) := by
        rw [Set.disjoint_left]
        intro x hx hx'
        exact absurd hx' (not_lt.mpr hx.2)
      have hIoc : IntegrableOn gaussKernel (Ioc (0 : ℝ) ε) volume :=
        integrableOn_gaussKernel.mono_set (fun t ht => ht.1)
      have hIoi : IntegrableOn gaussKernel (Ioi ε) volume :=
        integrableOn_gaussKernel.mono_set (Set.Ioi_subset_Ioi (le_of_lt hε))
      have hunion := MeasureTheory.setIntegral_union (μ := volume) (f := gaussKernel)
        hdisj measurableSet_Ioi hIoc hIoi
      rw [hsplit] at hunion
      rw [hunion]
      ring
    have hbound : Tendsto (fun ε : ℝ => Real.exp 1 * ε) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      have h0 : Tendsto (fun ε : ℝ => ε) (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using h0.const_mul (Real.exp 1)
    have hsq : Tendsto (fun ε : ℝ =>
        (∫ t in Ioi (0 : ℝ), gaussKernel t) - (∫ t in Ioi ε, gaussKernel t))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      refine squeeze_zero_norm' (a := fun ε : ℝ => Real.exp 1 * ε) ?_ hbound
      filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε hε1
      rw [hdiff ε hε hε1, Real.norm_eq_abs]
      exact norm_integral_gaussKernel_Ioc hε hε1
    have := (tendsto_const_nhds (x := ∫ t in Ioi (0 : ℝ), gaussKernel t)
      (f := nhdsWithin (0 : ℝ) (Ioi 0))).sub hsq
    simpa using this
  -- and to `-γ`
  have hslope : Tendsto (fun ε : ℝ => (1 - Real.exp (-ε)) / ε)
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    have hd : HasDerivAt (fun u : ℝ => 1 - Real.exp (-u)) 1 0 := by
      have h1 : HasDerivAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-0 : ℝ)) 0 := by
        simpa using (hasDerivAt_neg (0 : ℝ)).exp
      simpa using h1.const_sub 1
    have hs := hasDerivAt_iff_tendsto_slope.mp hd
    have hmono : nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ :=
      nhdsWithin_mono _ (fun x hx => ne_of_gt hx)
    refine (hs.mono_left hmono).congr ?_
    intro x
    simp [slope_def_field, div_eq_inv_mul]
  have hlogdiff : Tendsto (fun ε : ℝ => Real.log (1 - Real.exp (-ε)) - Real.log ε)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hcomp : Tendsto (fun ε : ℝ => Real.log ((1 - Real.exp (-ε)) / ε))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      have := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hslope
      simpa [Function.comp_def] using this
    refine hcomp.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [Real.log_div (ne_of_gt (one_sub_exp_neg_pos hε)) (ne_of_gt hε)]
  have hlim2 : Tendsto (fun ε : ℝ => ∫ t in Ioi ε, gaussKernel t)
      (nhdsWithin 0 (Ioi 0)) (nhds (-Real.eulerMascheroniConstant)) := by
    have hbase : Tendsto (fun ε : ℝ => -Real.eulerMascheroniConstant + ein ε
        + (Real.log (1 - Real.exp (-ε)) - Real.log ε))
        (nhdsWithin 0 (Ioi 0)) (nhds (-Real.eulerMascheroniConstant)) := by
      have := ((tendsto_const_nhds (x := -Real.eulerMascheroniConstant)
        (f := nhdsWithin (0 : ℝ) (Ioi 0))).add tendsto_ein_nhdsWithin_zero).add hlogdiff
      simpa using this
    refine hbase.congr' ?_
    filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε hε1
    rw [integral_gaussKernel_Ioi_eq hε hε1]
    ring
  exact tendsto_nhds_unique hlim1 hlim2

end RHTower
