/-
# The two-sided window torus law for unit-head Dirichlet polynomials

For a real bounded unit-head Dirichlet polynomial `Ψ = edPoly b (Icc 1 N)` on the critical line,
with `a_n = Re(b_n)/√n` its line coefficients and `J(ε) = ½ E_χ log max(|∑ a_n χ(n)|², ε²)`,

  `J(ε) − η − D/log(1/ε) ≤ (1/T)∫_T^{2T} log|Ψ(1/2+it)| dt ≤ J(ε) + η`   eventually,

for every `ε ∈ (0,1)`, `η > 0`: the Jessen–Tornehave law on dyadic windows with a quantitative
truncation error, from the continuous Bohr transfer (upper side) and the small-values estimate
(lower side).
-/
import GaloisForLFunctions.RHTower.OuterLawMollifiedProductEquivalence

open MeasureTheory intervalIntegral Filter Topology Complex Finset Set
open scoped Classical

namespace RHTower

open SteinhausModel

noncomputable section

/-- The critical-line real coefficients of an entire coefficient sequence. -/
def lineCoeff (b : ℕ → ℂ) (n : ℕ) : ℝ := (b n).re / Real.sqrt n

/-- Shift identity: the entire polynomial of the line coefficients is `Ψ(· + 1/2)`. -/
theorem edPoly_lineCoeff_eq_shift (b : ℕ → ℂ) {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n)
    (hreal : ∀ n ∈ s, (starRingEnd ℂ) (b n) = b n) (z : ℂ) :
    edPoly (fun n => ((lineCoeff b n : ℝ) : ℂ)) s z = edPoly b s (z + (1 / 2 : ℂ)) := by
  unfold edPoly lineCoeff
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hs n hn
  have hnC : ((n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hbre : b n = (((b n).re : ℝ) : ℂ) := (Complex.conj_eq_iff_re.mp (hreal n hn)).symm
  have hsqrt : (((Real.sqrt n : ℝ) : ℂ))⁻¹ = ((n : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) := by
    rw [Complex.cpow_neg]
    congr 1
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hn0.le]
    norm_num
  show (((b n).re / Real.sqrt n : ℝ) : ℂ) * ((n : ℝ) : ℂ) ^ (-z)
      = b n * ((n : ℝ) : ℂ) ^ (-(z + 1 / 2))
  rw [show -(z + 1 / 2 : ℂ) = -z + -(1 / 2 : ℂ) by ring, Complex.cpow_add _ _ hnC, ← hsqrt]
  conv_rhs => rw [hbre]
  push_cast
  ring

/-- On the critical line, `Ψ(1/2+it)` is the real Dirichlet polynomial of the line coefficients. -/
theorem edPoly_line_eq_dpoly_lineCoeff (b : ℕ → ℂ) {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n)
    (hreal : ∀ n ∈ s, (starRingEnd ℂ) (b n) = b n) (t : ℝ) :
    edPoly b s (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) = dpoly (lineCoeff b) s t := by
  rw [← edPoly_ofReal_imaginaryAxis (lineCoeff b) s hs t, edPoly_lineCoeff_eq_shift b hs hreal]
  congr 1
  push_cast
  ring

/-- The truncated torus Jensen mass of a coefficient sequence on the line. -/
def lineTorusLogMean (b : ℕ → ℂ) (s : Finset ℕ) (ε : ℝ) : ℝ :=
  ∫ ω, logMaxHalf ε (‖steinhausAmp (lineCoeff b) s ω‖ ^ 2) ∂steinhausMeasure

/-- **The two-sided window torus law.** -/
theorem exists_window_logMean_torus_twoSided (b : ℕ → ℂ) {N : ℕ} (hN : 1 ≤ N) (hb1 : b 1 = 1)
    (hbn : ∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1)
    (hreal : ∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ η : ℝ, 0 < η → ∀ᶠ T in atTop,
      lineTorusLogMean b (Finset.Icc 1 N) ε - η - D / Real.log (1 / ε) ≤
          T⁻¹ * ∫ t in T..(2 * T),
            Real.log ‖edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ∧
      T⁻¹ * (∫ t in T..(2 * T),
            Real.log ‖edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖)
        ≤ lineTorusLogMean b (Finset.Icc 1 N) ε + η := by
  set s : Finset ℕ := Finset.Icc 1 N with hsdef
  have hs : ∀ n ∈ s, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have h1 : 1 ∈ s := Finset.mem_Icc.mpr ⟨le_rfl, hN⟩
  have hne : ∃ z : ℂ, edPoly b s z ≠ 0 := by
    refine ⟨(7 : ℂ), fun h0 => ?_⟩
    have h := norm_edPoly_sub_one_le_half_of_six_le b hs h1 hb1 hbn (z := (7 : ℂ)) (by simp; norm_num)
    rw [h0] at h
    have : ‖(0 : ℂ) - 1‖ = 1 := by simp
    rw [this] at h
    norm_num at h
  set a : ℕ → ℝ := lineCoeff b with ha
  have hne' : ∃ z : ℂ, edPoly (fun n => ((a n : ℝ) : ℂ)) s z ≠ 0 := by
    obtain ⟨z, hz⟩ := hne
    refine ⟨z - 1 / 2, ?_⟩
    rw [ha, edPoly_lineCoeff_eq_shift b hs hreal, sub_add_cancel]
    exact hz
  have hline : ∀ t : ℝ, edPoly b s (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) = dpoly a s t :=
    fun t => edPoly_line_eq_dpoly_lineCoeff b hs hreal t
  obtain ⟨C₁, C₂, hC₁, hC₂, hsmall⟩ := exists_line_smallValues_bound b hN hb1 hbn
  refine ⟨C₁ + 4 * C₂, by positivity, ?_⟩
  intro ε hε hε1 η hη
  set lam : ℝ := Real.log (1 / ε) with hlam
  have hlampos : 0 < lam := Real.log_pos (by rw [lt_div_iff₀ hε]; linarith)
  have hupper := eventually_window_logMean_dpoly_le a s hs hne' hε hη
  have hlim := tendsto_contMoment_window_steinhaus a s hs (logMaxHalf ε) (continuous_logMaxHalf hε)
  obtain ⟨T₀, hT₀⟩ := (Metric.tendsto_atTop.mp hlim) η hη
  have hΨan : AnalyticOnNhd ℂ (edPoly b s) Set.univ := analyticOnNhd_edPoly b hs
  have hcontD : Continuous (dpoly a s) := by
    unfold dpoly cterm
    exact continuous_finset_sum _ fun n _ => by fun_prop
  have hcφ : Continuous (fun t : ℝ => logMaxHalf ε (‖dpoly a s t‖ ^ 2)) :=
    (continuous_logMaxHalf hε).comp (by fun_prop)
  filter_upwards [hupper, eventually_ge_atTop T₀, eventually_ge_atTop (20 : ℝ)] with T hup hT h20
  have hTpos : 0 < T := by linarith
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hint_eq : (∫ t in T..(2 * T), Real.log ‖edPoly b s (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖)
      = ∫ t in T..(2 * T), Real.log ‖dpoly a s t‖ := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only
    rw [hline t]
  refine ⟨?_, ?_⟩
  · have hclose := hT₀ T hT
    rw [Real.dist_eq, abs_lt] at hclose
    set φ : ℝ → ℝ := fun t => max (Real.log ε -
      Real.log ‖edPoly b s (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) 0 with hφ
    have hφint : IntervalIntegrable φ MeasureTheory.volume T (2 * T) := by
      have hf : IntervalIntegrable (fun t : ℝ => Real.log ε -
          Real.log ‖edPoly b s (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) MeasureTheory.volume T (2 * T) :=
        intervalIntegrable_const.sub (intervalIntegrable_log_norm_vertical_of_entire hΨan (1 / 2) T (2 * T))
      rw [intervalIntegrable_iff] at hf ⊢
      exact hf.pos_part
    have hdecomp : (∫ t in T..(2 * T), Real.log ‖edPoly b s (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖)
        = (∫ t in T..(2 * T), logMaxHalf ε (‖dpoly a s t‖ ^ 2)) - ∫ t in T..(2 * T), φ t := by
      rw [← intervalIntegral.integral_sub (hcφ.intervalIntegrable _ _) hφint]
      apply intervalIntegral.integral_congr_ae
      have hfin := finite_edPolyLine_zeros b hs hne T (2 * T)
      have hnull := hfin.measure_zero MeasureTheory.volume
      rw [MeasureTheory.measure_eq_zero_iff_ae_notMem] at hnull
      filter_upwards [hnull] with t ht hmem
      have hIcc : t ∈ Set.Icc T (2 * T) := by
        rw [Set.uIoc_of_le (by linarith)] at hmem
        exact ⟨hmem.1.le, hmem.2⟩
      have hne0 : edPoly b s (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 := fun h0 => ht ⟨hIcc, h0⟩
      have hpos : 0 < ‖edPoly b s (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := norm_pos_iff.mpr hne0
      simp only [hφ]
      rw [← hline t, logMaxHalf_sq_eq_max hε hpos, max_sub_max_sub_eq]
    have hsm := hsmall T (2 * T) (by linarith) ε hε hε1
    have hsm' : (∫ t in T..(2 * T), φ t) ≤ (C₁ + 4 * C₂) * T / lam := by
      refine hsm.trans ?_
      rw [div_le_div_iff_of_pos_right hlampos]
      rw [abs_of_pos hTpos, abs_of_pos (by linarith : (0 : ℝ) < 2 * T)]
      nlinarith [hC₂, hT1]
    rw [hdecomp, mul_sub]
    have hJ : lineTorusLogMean b s ε - η ≤
        T⁻¹ * ∫ t in T..(2 * T), logMaxHalf ε (‖dpoly a s t‖ ^ 2) := by
      unfold lineTorusLogMean
      linarith [hclose.1]
    have hφ' : T⁻¹ * ∫ t in T..(2 * T), φ t ≤ (C₁ + 4 * C₂) / lam := by
      calc T⁻¹ * ∫ t in T..(2 * T), φ t ≤ T⁻¹ * ((C₁ + 4 * C₂) * T / lam) := by
            gcongr
        _ = (C₁ + 4 * C₂) / lam := by field_simp
    linarith
  · rw [hint_eq]
    unfold lineTorusLogMean
    exact hup

end

end RHTower
