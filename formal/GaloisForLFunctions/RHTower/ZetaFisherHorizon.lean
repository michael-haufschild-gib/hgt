import GaloisForLFunctions.RHTower.ZetaFisherMetric

/-!
# The critical line is at infinite Fisher distance

The Fisher metric of the arithmetic state family blows up like `1/(x-1)²` at the pole of `ζ`.
Since `∫ dx/(x-1)` diverges, the Fisher arclength of any interval reaching the wall is infinite:
the critical line is an information-geometric horizon.
-/

noncomputable section

open Filter Topology MeasureTheory Set

namespace RHTower

/-- The Fisher metric along the real axis. -/
def zetaFisherReal (x : ℝ) : ℝ := (zetaFisherMetric (x : ℂ)).re

theorem tendsto_sub_one_sq_mul_zetaFisherReal :
    Tendsto (fun x : ℝ => (x - 1) ^ 2 * zetaFisherReal x) (𝓝[>] (1 : ℝ)) (𝓝 1) := by
  have h := tendsto_sub_one_sq_mul_zetaFisherMetric.comp tendsto_ofReal_nhdsGT_one_ne
  have hre := (Complex.continuous_re.tendsto (1 : ℂ)).comp h
  simp only [Function.comp_def, Complex.one_re] at hre
  refine hre.congr fun x => ?_
  have hcast : ((x : ℂ) - 1) ^ 2 = (((x - 1) ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [zetaFisherReal, hcast, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-! ### Regularity right of the wall -/

theorem analyticAt_riemannZeta_ofReal {x : ℝ} (hx : 1 < x) :
    AnalyticAt ℂ riemannZeta ((x : ℝ) : ℂ) := by
  have hne : ((x : ℝ) : ℂ) ≠ 1 := by
    simp only [Ne, Complex.ofReal_eq_one]
    exact ne_of_gt hx
  have hdiff : DifferentiableOn ℂ riemannZeta ({(1 : ℂ)}ᶜ) := fun z hz =>
    (differentiableAt_riemannZeta (by simpa using hz)).differentiableWithinAt
  exact (hdiff.analyticOnNhd isOpen_compl_singleton) _ (by simpa using hne)

theorem riemannZeta_ofReal_ne_zero {x : ℝ} (hx : 1 < x) : riemannZeta ((x : ℝ) : ℂ) ≠ 0 :=
  riemannZeta_ne_zero_of_one_lt_re (by simpa using hx)

theorem analyticAt_zetaFisherMetric {x : ℝ} (hx : 1 < x) :
    AnalyticAt ℂ zetaFisherMetric ((x : ℝ) : ℂ) := by
  have hana := analyticAt_riemannZeta_ofReal hx
  have hlog : AnalyticAt ℂ (logDeriv riemannZeta) ((x : ℝ) : ℂ) := by
    have hfun : logDeriv riemannZeta = fun z : ℂ => deriv riemannZeta z / riemannZeta z := by
      funext z; exact logDeriv_apply _ _
    rw [hfun]
    exact hana.deriv.div hana (riemannZeta_ofReal_ne_zero hx)
  exact hlog.deriv

theorem continuousOn_zetaFisherReal : ContinuousOn zetaFisherReal (Set.Ioi (1 : ℝ)) := by
  intro x hx
  have hx1 : (1 : ℝ) < x := hx
  have hcont : ContinuousAt zetaFisherMetric ((x : ℝ) : ℂ) :=
    (analyticAt_zetaFisherMetric hx1).continuousAt
  have h : ContinuousAt (fun y : ℝ => (zetaFisherMetric ((y : ℝ) : ℂ)).re) x :=
    (Complex.continuous_re.continuousAt).comp (hcont.comp Complex.continuous_ofReal.continuousAt)
  exact h.continuousWithinAt

/-! ### The divergent Fisher length -/

theorem sqrt_zetaFisherReal_ge_of_gt {x : ℝ} (hx : 1 < x)
    (h : 1 / 4 < (x - 1) ^ 2 * zetaFisherReal x) :
    (1 / 2) * (x - 1)⁻¹ ≤ Real.sqrt (zetaFisherReal x) := by
  have hpos : 0 < x - 1 := by linarith
  have hsq : 0 < (x - 1) ^ 2 := by positivity
  have hg : 1 / (4 * (x - 1) ^ 2) < zetaFisherReal x := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hval : ((1 / 2) * (x - 1)⁻¹) ^ 2 = 1 / (4 * (x - 1) ^ 2) := by
    field_simp
    ring
  have hle : ((1 / 2) * (x - 1)⁻¹) ^ 2 ≤ zetaFisherReal x := by rw [hval]; linarith
  have hnn : 0 ≤ (1 / 2) * (x - 1)⁻¹ := by positivity
  calc (1 / 2) * (x - 1)⁻¹ = Real.sqrt (((1 / 2) * (x - 1)⁻¹) ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hnn]
    _ ≤ Real.sqrt (zetaFisherReal x) := Real.sqrt_le_sqrt hle

theorem integral_half_inv_sub_one {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∫ x in a..b, (1 / 2) * (x - 1)⁻¹) = (Real.log (b - 1) - Real.log (a - 1)) / 2 := by
  have ha1 : 0 < a - 1 := by linarith
  have hb1 : 0 < b - 1 := by linarith
  rw [intervalIntegral.integral_const_mul]
  have hshift : (∫ x in a..b, (x - 1)⁻¹) = ∫ u in (a - 1)..(b - 1), u⁻¹ :=
    intervalIntegral.integral_comp_sub_right (fun u : ℝ => u⁻¹) 1
  rw [hshift]
  have hzero : (0 : ℝ) ∉ Set.uIcc (a - 1) (b - 1) := by
    rw [Set.uIcc_of_le (by linarith : a - 1 ≤ b - 1)]
    intro hmem
    exact absurd hmem.1 (by linarith)
  rw [integral_inv hzero, Real.log_div (ne_of_gt hb1) (ne_of_gt ha1)]
  ring

/-- **The critical line is at infinite Fisher distance.**  For a suitable right endpoint the
Fisher arclength of `(a, b]` tends to infinity as `a` approaches the wall. -/
theorem exists_tendsto_zetaFisherLength_atTop :
    ∃ b : ℝ, 1 < b ∧ Tendsto (fun a : ℝ => ∫ x in a..b, Real.sqrt (zetaFisherReal x))
      (𝓝[>] (1 : ℝ)) atTop := by
  have hev : ∀ᶠ x : ℝ in 𝓝[>] (1 : ℝ), 1 / 4 < (x - 1) ^ 2 * zetaFisherReal x :=
    tendsto_sub_one_sq_mul_zetaFisherReal.eventually
      (eventually_gt_nhds (by norm_num : (1 : ℝ) / 4 < 1))
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  have hu1 : (1 : ℝ) < u := Set.mem_Ioi.mp hu
  set b : ℝ := (1 + u) / 2 with hbdef
  have hb1 : 1 < b := by rw [hbdef]; linarith
  have hbu : b < u := by rw [hbdef]; linarith
  refine ⟨b, hb1, ?_⟩
  have hbound : ∀ a : ℝ, 1 < a → a ≤ b →
      (Real.log (b - 1) - Real.log (a - 1)) / 2
        ≤ ∫ x in a..b, Real.sqrt (zetaFisherReal x) := by
    intro a ha hab
    have hsubset : Set.uIcc a b ⊆ Set.Ioi (1 : ℝ) := by
      rw [Set.uIcc_of_le hab]
      intro x hx
      exact lt_of_lt_of_le ha hx.1
    have hint1 : IntervalIntegrable (fun x : ℝ => (1 / 2) * (x - 1)⁻¹) volume a b := by
      apply ContinuousOn.intervalIntegrable
      refine continuousOn_const.mul (ContinuousOn.inv₀
        (continuousOn_id.sub continuousOn_const) ?_)
      exact fun x hx => sub_ne_zero.mpr (ne_of_gt (Set.mem_Ioi.mp (hsubset hx)))
    have hint2 : IntervalIntegrable (fun x : ℝ => Real.sqrt (zetaFisherReal x)) volume a b := by
      apply ContinuousOn.intervalIntegrable
      exact Real.continuous_sqrt.comp_continuousOn (continuousOn_zetaFisherReal.mono hsubset)
    have hmono : ∫ x in a..b, (1 / 2) * (x - 1)⁻¹
        ≤ ∫ x in a..b, Real.sqrt (zetaFisherReal x) := by
      refine intervalIntegral.integral_mono_on hab hint1 hint2 fun x hx => ?_
      have hx1 : 1 < x := lt_of_lt_of_le ha hx.1
      have hxu : x < u := lt_of_le_of_lt hx.2 hbu
      exact sqrt_zetaFisherReal_ge_of_gt hx1 (hsub ⟨hx1, hxu⟩)
    rw [integral_half_inv_sub_one ha hab] at hmono
    exact hmono
  have hlog : Tendsto (fun a : ℝ => Real.log (a - 1)) (𝓝[>] (1 : ℝ)) atBot := by
    have hmap : Tendsto (fun a : ℝ => a - 1) (𝓝[>] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have hc : Tendsto (fun a : ℝ => a - 1) (𝓝 (1 : ℝ)) (𝓝 (0 : ℝ)) := by
          simpa using (continuous_sub_right (1 : ℝ)).tendsto (1 : ℝ)
        exact hc.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with a ha
        simpa using sub_pos.mpr (Set.mem_Ioi.mp ha)
    exact Real.tendsto_log_nhdsGT_zero.comp hmap
  have hdiv : Tendsto (fun a : ℝ => (Real.log (b - 1) - Real.log (a - 1)) / 2)
      (𝓝[>] (1 : ℝ)) atTop := by
    have hneg : Tendsto (fun a : ℝ => -Real.log (a - 1)) (𝓝[>] (1 : ℝ)) atTop :=
      tendsto_neg_atBot_atTop.comp hlog
    have hadd : Tendsto (fun a : ℝ => Real.log (b - 1) + -Real.log (a - 1))
        (𝓝[>] (1 : ℝ)) atTop := tendsto_atTop_add_const_left _ _ hneg
    have hhalf := hadd.atTop_div_const (by norm_num : (0 : ℝ) < 2)
    refine hhalf.congr fun a => ?_
    ring
  have hlt : {x : ℝ | x < b} ∈ 𝓝[>] (1 : ℝ) :=
    nhdsWithin_le_nhds ((isOpen_lt continuous_id continuous_const).mem_nhds hb1)
  refine tendsto_atTop_mono' _ ?_ hdiv
  filter_upwards [self_mem_nhdsWithin, hlt] with a ha hab
  exact hbound a (Set.mem_Ioi.mp ha) (le_of_lt hab)

end RHTower
