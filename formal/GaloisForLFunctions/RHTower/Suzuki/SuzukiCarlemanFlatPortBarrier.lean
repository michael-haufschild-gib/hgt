import GaloisForLFunctions.RHTower.Suzuki.SuzukiCarlemanFlatPortAsymptotic

/-!
# The weighted strip barrier of the flat Carleman port

Dominated convergence in the shifted chart turns the logistic average into the profile itself:
`B'(L)/F(L) → 1`.  The flat profile therefore transfers its own rate to the Carleman response, and
since `exp(2σL - 2√L) → ∞` for every `σ > 0`, the weighted derivative is not square integrable on
any ray.  Zero half-log trace, `L²` membership, Carleman boundedness and the endpoint counterterm
together do not produce a positive Gamma strip.
-/

open Set MeasureTheory Filter Topology

namespace RHTower

noncomputable section

/-- The `L`-derivative of the Carleman response as a function of the cutoff scale. -/
def carlemanLogResponseDeriv (L : ℝ) : ℝ :=
  ∫ v in Ioi (1:ℝ), flatPortProfile v * logisticKernel (v - L)

/-- The shifted integrand of the derivative, normalized by the profile. -/
def carlemanShiftedRatio (L y : ℝ) : ℝ :=
  Set.indicator (Ioi (1:ℝ)) (fun v => flatPortProfile v * logisticKernel (v - L)) (L + y)
    / flatPortProfile L

theorem carlemanLogResponseDeriv_eq_shift (L : ℝ) :
    carlemanLogResponseDeriv L / flatPortProfile L = ∫ y, carlemanShiftedRatio L y := by
  have h1 : carlemanLogResponseDeriv L
      = ∫ v, Set.indicator (Ioi (1:ℝ)) (fun v => flatPortProfile v * logisticKernel (v - L)) v := by
    rw [carlemanLogResponseDeriv, integral_indicator measurableSet_Ioi]
  have h2 : (∫ v, Set.indicator (Ioi (1:ℝ))
        (fun v => flatPortProfile v * logisticKernel (v - L)) v)
      = ∫ y, Set.indicator (Ioi (1:ℝ))
        (fun v => flatPortProfile v * logisticKernel (v - L)) (L + y) :=
    (integral_add_left_eq_self _ L).symm
  simp only [carlemanShiftedRatio]
  rw [h1, h2, ← integral_div]

theorem carlemanShiftedRatio_eq_of_lt {L y : ℝ} (h : 1 < L + y) :
    carlemanShiftedRatio L y
      = flatPortProfile (L + y) / flatPortProfile L * logisticKernel y := by
  simp only [carlemanShiftedRatio]
  rw [Set.indicator_of_mem (show L + y ∈ Ioi (1:ℝ) from h)]
  have hy : L + y - L = y := by ring
  rw [hy]
  field_simp

theorem carlemanShiftedRatio_eq_zero_of_le {L y : ℝ} (h : L + y ≤ 1) :
    carlemanShiftedRatio L y = 0 := by
  simp only [carlemanShiftedRatio]
  rw [Set.indicator_of_notMem (by simpa using h), zero_div]

theorem abs_carlemanShiftedRatio_le {L : ℝ} (hL : 4 ≤ L) (y : ℝ) :
    ‖carlemanShiftedRatio L y‖ ≤ Real.exp (-|y| / 2) := by
  rcases le_or_gt (L + y) 1 with hle | hgt
  · rw [carlemanShiftedRatio_eq_zero_of_le hle, norm_zero]
    exact (Real.exp_pos _).le
  · rw [carlemanShiftedRatio_eq_of_lt hgt, Real.norm_eq_abs]
    have hpos : 0 ≤ flatPortProfile (L + y) / flatPortProfile L * logisticKernel y := by
      have h1 := (flatPortProfile_pos (L + y)).le
      have h2 := (flatPortProfile_pos L).le
      have h3 := (logisticKernel_pos y).le
      positivity
    rw [abs_of_nonneg hpos]
    have hratio : flatPortProfile (L + y) / flatPortProfile L ≤ Real.exp (|y| / 2) :=
      flatPortProfile_ratio_le hL (by linarith)
    have hk : logisticKernel y ≤ Real.exp (-|y|) := logisticKernel_le_exp_neg_abs y
    have hprod : flatPortProfile (L + y) / flatPortProfile L * logisticKernel y
        ≤ Real.exp (|y| / 2) * Real.exp (-|y|) := by
      apply mul_le_mul hratio hk (logisticKernel_pos y).le (Real.exp_pos _).le
    refine hprod.trans (le_of_eq ?_)
    rw [← Real.exp_add]
    congr 1
    ring

/-- **`(7)`: the Carleman response inherits the exact flat rate.** -/
theorem tendsto_carlemanLogResponseDeriv_div :
    Tendsto (fun L => carlemanLogResponseDeriv L / flatPortProfile L) atTop (𝓝 1) := by
  have hmeas : ∀ᶠ L in atTop,
      AEStronglyMeasurable (fun y => carlemanShiftedRatio L y) volume := by
    filter_upwards with L
    apply Measurable.aestronglyMeasurable
    have hfun : (fun y => carlemanShiftedRatio L y)
        = (fun y => (Set.indicator (Ioi (1:ℝ))
            (fun v => flatPortProfile v * logisticKernel (v - L))
              ∘ fun y : ℝ => L + y) y / flatPortProfile L) := rfl
    rw [hfun]
    apply Measurable.div_const
    apply Measurable.comp _ (measurable_const_add L)
    apply Measurable.indicator _ measurableSet_Ioi
    unfold flatPortProfile logisticKernel
    fun_prop
  have hbound : ∀ᶠ L in atTop, ∀ᵐ y ∂(volume : Measure ℝ),
      ‖carlemanShiftedRatio L y‖ ≤ Real.exp (-|y| / 2) := by
    filter_upwards [eventually_ge_atTop (4:ℝ)] with L hL
    filter_upwards with y
    exact abs_carlemanShiftedRatio_le hL y
  have hlim : ∀ᵐ y ∂(volume : Measure ℝ),
      Tendsto (fun L => carlemanShiftedRatio L y) atTop (𝓝 (logisticKernel y)) := by
    filter_upwards with y
    have hbase : Tendsto (fun L : ℝ =>
        flatPortProfile (L + y) / flatPortProfile L * logisticKernel y) atTop
        (𝓝 (1 * logisticKernel y)) :=
      (tendsto_flatPortProfile_ratio y).mul_const _
    rw [one_mul] at hbase
    refine hbase.congr' ?_
    filter_upwards [eventually_gt_atTop (1 - y)] with L hL
    exact (carlemanShiftedRatio_eq_of_lt (by linarith)).symm
  have hdct := tendsto_integral_filter_of_dominated_convergence
    (fun y => Real.exp (-|y| / 2)) hmeas hbound integrable_exp_neg_half_abs hlim
  rw [integral_logisticKernel] at hdct
  exact hdct.congr fun L => (carlemanLogResponseDeriv_eq_shift L).symm

/-- **`(8)`: no positive exponential weight makes the response derivative square integrable.** -/
theorem not_integrableOn_weighted_carlemanLogResponseDeriv {σ : ℝ} (hσ : 0 < σ) (c : ℝ) :
    ¬ IntegrableOn
      (fun L => (Real.exp (σ * L) * carlemanLogResponseDeriv L) ^ (2 : ℕ)) (Ioi c) volume := by
  have hhalf : ∀ᶠ L in atTop, flatPortProfile L / 2 ≤ carlemanLogResponseDeriv L := by
    have hlim := tendsto_carlemanLogResponseDeriv_div
    have hev : ∀ᶠ L in atTop, 1 / 2 ≤ carlemanLogResponseDeriv L / flatPortProfile L := by
      have := hlim.eventually (eventually_ge_nhds (by norm_num : (1:ℝ)/2 < 1))
      exact this
    filter_upwards [hev] with L hL
    have hpos := flatPortProfile_pos L
    rw [le_div_iff₀ hpos] at hL
    linarith
  have hgrow : Tendsto
      (fun L => Real.exp (2 * σ * L - 2 * Real.sqrt L) / 4) atTop atTop := by
    have hinner : Tendsto (fun L : ℝ => 2 * σ * L - 2 * Real.sqrt L) atTop atTop := by
      have hev : ∀ᶠ L : ℝ in atTop, σ * L ≤ 2 * σ * L - 2 * Real.sqrt L := by
        filter_upwards [eventually_ge_atTop (0:ℝ), eventually_ge_atTop ((2 / σ) ^ (2 : ℕ))] with L h0 hL
        have hs : Real.sqrt L ≤ σ * L / 2 := by
          have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt h0
          have h2 : (2 / σ) ≤ Real.sqrt L := by
            have hmono : Real.sqrt ((2 / σ) ^ (2 : ℕ)) ≤ Real.sqrt L := Real.sqrt_le_sqrt hL
            rwa [Real.sqrt_sq (by positivity)] at hmono
          have hmul : (2 / σ) * Real.sqrt L ≤ L := by
            nlinarith [mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg L)]
          have hscaled := mul_le_mul_of_nonneg_left hmul hσ.le
          rw [show σ * ((2 / σ) * Real.sqrt L) = 2 * Real.sqrt L by field_simp] at hscaled
          linarith
        linarith
      exact tendsto_atTop_mono' atTop hev
        ((tendsto_id (α := ℝ)).const_mul_atTop hσ)
    have := Real.tendsto_exp_atTop.comp hinner
    exact (this.atTop_div_const (by norm_num : (0:ℝ) < 4)).congr fun L => rfl
  have hev : ∀ᶠ L in atTop,
      Real.exp (2 * σ * L - 2 * Real.sqrt L) / 4
        ≤ (Real.exp (σ * L) * carlemanLogResponseDeriv L) ^ (2 : ℕ) := by
    filter_upwards [hhalf] with L hL
    have hFpos := flatPortProfile_pos L
    have h1 : Real.exp (σ * L) ^ (2 : ℕ) = Real.exp (2 * σ * L) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    have h2 : flatPortProfile L ^ (2 : ℕ) = Real.exp (-(2 * Real.sqrt L)) := by
      rw [flatPortProfile, sq, ← Real.exp_add]
      congr 1
      ring
    have hsq : (Real.exp (σ * L) * (flatPortProfile L / 2)) ^ (2 : ℕ)
        = Real.exp (2 * σ * L - 2 * Real.sqrt L) / 4 := by
      calc (Real.exp (σ * L) * (flatPortProfile L / 2)) ^ (2 : ℕ)
          = Real.exp (σ * L) ^ (2 : ℕ) * flatPortProfile L ^ (2 : ℕ) / 4 := by ring
        _ = Real.exp (2 * σ * L) * Real.exp (-(2 * Real.sqrt L)) / 4 := by rw [h1, h2]
        _ = Real.exp (2 * σ * L - 2 * Real.sqrt L) / 4 := by
            rw [← Real.exp_add,
              show 2 * σ * L + -(2 * Real.sqrt L) = 2 * σ * L - 2 * Real.sqrt L by ring]
    rw [← hsq]
    have hmul : Real.exp (σ * L) * (flatPortProfile L / 2)
        ≤ Real.exp (σ * L) * carlemanLogResponseDeriv L :=
      mul_le_mul_of_nonneg_left hL (Real.exp_pos _).le
    have hnn : 0 ≤ Real.exp (σ * L) * (flatPortProfile L / 2) := by positivity
    nlinarith
  exact not_integrableOn_Ioi_of_tendsto_atTop (tendsto_atTop_mono' atTop hev hgrow) c

end

end RHTower
