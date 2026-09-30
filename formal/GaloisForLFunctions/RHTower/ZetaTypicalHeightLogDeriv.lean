import GaloisForLFunctions.RHTower.ZetaTypicalHeightSup
import GaloisForLFunctions.RHTower.XiRightDiscSeamFixedRadiusDensity
import GaloisForLFunctions.RHTower.ThetaThresholdXiDivisibleUniqueness
import GaloisForLFunctions.HTGeometry.LogDerivativeBound

/-!
# `ζ'/ζ` and `1/ζ` at almost every height

A height `t ∈ [T, 2T]` is *typical* (`zetaTypicalHeight η ε T t`) when `ζ` has no zero with
`Re ≥ ½ + η/4` and `|Im − t| ≤ 2`, and `|ζ| ≤ T^ε` on `½ ≤ Re ≤ 2`, `|Im − t| ≤ 2`. For fixed
`η, ε` the atypical heights have measure `o(T)` (`eventually_volume_not_zetaTypicalHeight_le`):
the zero shadow has density zero (`eventually_volume_zetaZeroShadow_le`) and so do the large values
(`eventually_volume_zetaLargeNear_le`).

At a typical height, `ζ` is zero-free and at most `T^ε + 2` on the disc of radius `3/2 − η/4`
about `2 + it`, and at least `1/3` at the centre. Borel–Carathéodory for a branch of `log ζ` and
Cauchy's estimate (`HTGeometry.norm_logDeriv_le`, `HTGeometry.norm_lower_bound_of_ball`) give

* `|ζ'/ζ(s)| ≤ 24 (ε log T + 9)/η²` for `|s − (2 + it)| ≤ 3/2 − η`,
* `|ζ(s)| ≥ e^{−12(ε log T + 9)/η}/3` for `|s − (2 + it)| ≤ 3/2 − η/2`.
-/

noncomputable section

open Complex Set MeasureTheory Metric

namespace RHTower

theorem norm_riemannZeta_bounds_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    1 / 3 ≤ ‖riemannZeta s‖ ∧ ‖riemannZeta s‖ ≤ 2 := by
  have h := norm_riemannZeta_sub_one_le_zeta_two hs
  have hπ : Real.pi ^ 2 / 6 - 1 ≤ 2 / 3 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have h1 := norm_sub_norm_le (1 : ℂ) (1 - riemannZeta s)
  have h2 := norm_sub_le (riemannZeta s - 1) (-1 : ℂ)
  simp only [norm_one, sub_sub_cancel, sub_neg_eq_add, sub_add_cancel, norm_neg] at h1 h2
  rw [norm_sub_rev] at h1
  constructor <;> linarith

/-- **Typical heights.** No zero of `ζ` with `Re ≥ ½ + η/4` lies within height distance `2` of
`t`, and `|ζ| ≤ T^ε` on `½ ≤ Re ≤ 2`, `|Im − t| ≤ 2`. -/
def zetaTypicalHeight (η ε T t : ℝ) : Prop :=
  t ∈ Icc T (2 * T) ∧ t ∉ zetaZeroShadow (1 / 2 + η / 4) 2 ∧ t ∉ zetaLargeNear T (T ^ ε)

namespace zetaTypicalHeight

variable {η ε T t : ℝ}

theorem ne_zero (h : zetaTypicalHeight η ε T t) {s : ℂ} (hs : 1 / 2 + η / 4 ≤ s.re)
    (hst : |s.im - t| ≤ 2) : riemannZeta s ≠ 0 := fun h0 => h.2.1 ⟨s, h0, hs, hst⟩

theorem norm_le (h : zetaTypicalHeight η ε T t) (hT : 1 ≤ T) {s : ℂ} (hs : 1 / 2 ≤ s.re)
    (hst : |s.im - t| ≤ 2) : ‖riemannZeta s‖ ≤ T ^ ε + 2 := by
  have hTε : 0 ≤ T ^ ε := Real.rpow_nonneg (by linarith) ε
  rcases le_total s.re 2 with h2 | h2
  · have : ¬ T ^ ε < ‖riemannZeta s‖ := fun hlt => h.2.2 ⟨h.1, s, hs, h2, hst, hlt⟩
    linarith [not_lt.mp this]
  · linarith [(norm_riemannZeta_bounds_of_two_le_re h2).2]

theorem log_ratio_le (hT : 1 ≤ T) (hε : 0 ≤ ε) :
    Real.log ((T ^ ε + 2) / (1 / 3)) + 1 ≤ ε * Real.log T + 9 := by
  have hT0 : 0 < T := by linarith
  have h1 : 1 ≤ T ^ ε := Real.one_le_rpow hT hε
  have hpos : 0 < (T ^ ε + 2) / (1 / 3) := by positivity
  have hle : (T ^ ε + 2) / (1 / 3) ≤ 9 * T ^ ε := by
    rw [div_le_iff₀ (by norm_num)]; linarith
  have hlog := Real.log_le_log hpos hle
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hT0] at hlog
  have h9 : Real.log 9 ≤ 8 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9); linarith
  linarith

/-- The disc of radius `3/2 − η/4` about `2 + it` satisfies the hypotheses of
Borel–Carathéodory at a typical height. -/
theorem disc_hypotheses (h : zetaTypicalHeight η ε T t) (hη0 : 0 < η) (hT : 8 ≤ T) :
    DifferentiableOn ℂ riemannZeta (ball (2 + (t : ℂ) * I) (3 / 2 - η / 4))
      ∧ (∀ s ∈ ball (2 + (t : ℂ) * I) (3 / 2 - η / 4), riemannZeta s ≠ 0)
      ∧ (∀ s ∈ ball (2 + (t : ℂ) * I) (3 / 2 - η / 4), ‖riemannZeta s‖ ≤ T ^ ε + 2)
      ∧ 1 / 3 ≤ ‖riemannZeta (2 + (t : ℂ) * I)‖ := by
  have ht := h.1
  have hgeom : ∀ s ∈ ball (2 + (t : ℂ) * I) (3 / 2 - η / 4),
      1 / 2 + η / 4 < s.re ∧ |s.im - t| ≤ 2 := by
    intro s hs
    rw [mem_ball, dist_eq_norm] at hs
    have h1 := abs_lt.mp ((Complex.abs_re_le_norm _).trans_lt hs)
    have h2 := abs_le.mp ((Complex.abs_im_le_norm _).trans hs.le)
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_im, Complex.add_im,
      Complex.mul_im] at h1 h2
    norm_num at h1 h2
    exact ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  refine ⟨?_, fun s hs => ?_, fun s hs => ?_, ?_⟩
  · intro s hs
    have hg := hgeom s hs
    have hne : s ≠ 1 := by
      intro h1; rw [h1] at hg; simp at hg
      have := abs_le.mp hg.2; linarith [ht.1]
    exact (differentiableAt_riemannZeta hne).differentiableWithinAt
  · have hg := hgeom s hs
    exact h.ne_zero hg.1.le hg.2
  · have hg := hgeom s hs
    exact h.norm_le (by linarith) (by linarith [hg.1]) hg.2
  · exact (norm_riemannZeta_bounds_of_two_le_re (by simp)).1

/-- **Typical logarithmic derivative.** At a typical height,
`|ζ'/ζ(s)| ≤ 24 (ε log T + 9)/η²` for `|s − (2 + it)| ≤ 3/2 − η`. -/
theorem norm_logDeriv_le (h : zetaTypicalHeight η ε T t) (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hT : 8 ≤ T) (hε : 0 ≤ ε) {s : ℂ} (hs : ‖s - (2 + (t : ℂ) * I)‖ ≤ 3 / 2 - η) :
    ‖logDeriv riemannZeta s‖ ≤ 24 * (ε * Real.log T + 9) / η ^ 2 := by
  obtain ⟨hd, hne, hM, hm⟩ := h.disc_hypotheses hη0 hT
  have hb := GaloisForLFunctions.HTGeometry.norm_logDeriv_le (ρ := 3 / 2 - η) (r := 3 / 2 - η / 2)
    (by linarith) (by linarith) (by linarith) hd hne hM (by norm_num) hm hs
  rw [logDeriv_apply]
  refine hb.trans ?_
  have hL := log_ratio_le (T := T) (by linarith) hε
  have hL0 : 0 ≤ Real.log ((T ^ ε + 2) / (1 / 3)) + 1 := by
    have : 1 ≤ (T ^ ε + 2) / (1 / 3) := by
      rw [le_div_iff₀ (by norm_num)]; have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ T) ε
      linarith
    linarith [Real.log_nonneg this]
  have e : 3 / 2 - η / 4 - (3 / 2 - η / 2) = η / 4 := by ring
  have e2 : 3 / 2 - η / 2 - (3 / 2 - η) = η / 2 := by ring
  rw [e, e2]
  have hfac : (3 / 2 - η / 2) / (η / 4) / (η / 2) ≤ 12 / η ^ 2 := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  calc 2 * (Real.log ((T ^ ε + 2) / (1 / 3)) + 1) * (3 / 2 - η / 2) / (η / 4) / (η / 2)
      = 2 * (Real.log ((T ^ ε + 2) / (1 / 3)) + 1) * ((3 / 2 - η / 2) / (η / 4) / (η / 2)) := by
        ring
    _ ≤ 2 * (ε * Real.log T + 9) * (12 / η ^ 2) := by
        have h0 : 0 ≤ (3 / 2 - η / 2) / (η / 4) / (η / 2) :=
          div_nonneg (div_nonneg (by linarith) (by positivity)) (by positivity)
        exact mul_le_mul (by linarith) hfac h0 (by linarith)
    _ = 24 * (ε * Real.log T + 9) / η ^ 2 := by ring

/-- **Typical lower bound.** At a typical height,
`|ζ(s)| ≥ e^{−12(ε log T + 9)/η}/3` for `|s − (2 + it)| ≤ 3/2 − η/2`. -/
theorem norm_ge (h : zetaTypicalHeight η ε T t) (hη0 : 0 < η) (hη1 : η ≤ 1) (hT : 8 ≤ T)
    (hε : 0 ≤ ε) {s : ℂ} (hs : ‖s - (2 + (t : ℂ) * I)‖ ≤ 3 / 2 - η / 2) :
    Real.exp (-(12 * (ε * Real.log T + 9) / η)) / 3 ≤ ‖riemannZeta s‖ := by
  obtain ⟨hd, hne, hM, hm⟩ := h.disc_hypotheses hη0 hT
  have hb := GaloisForLFunctions.HTGeometry.norm_lower_bound_of_ball (r := 3 / 2 - η / 2)
    (by linarith) (by linarith) hd hne hM (by norm_num) hm hs
  refine le_trans ?_ hb
  have hL := log_ratio_le (T := T) (by linarith) hε
  have e : 3 / 2 - η / 4 - (3 / 2 - η / 2) = η / 4 := by ring
  rw [e]
  have hL0 : 0 ≤ Real.log ((T ^ ε + 2) / (1 / 3)) + 1 := by
    have : 1 ≤ (T ^ ε + 2) / (1 / 3) := by
      rw [le_div_iff₀ (by norm_num)]; have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ T) ε
      linarith
    linarith [Real.log_nonneg this]
  have hkey : 2 * (Real.log ((T ^ ε + 2) / (1 / 3)) + 1) * (3 / 2 - η / 2) / (η / 4)
      ≤ 12 * (ε * Real.log T + 9) / η := by
    calc 2 * (Real.log ((T ^ ε + 2) / (1 / 3)) + 1) * (3 / 2 - η / 2) / (η / 4)
        = (Real.log ((T ^ ε + 2) / (1 / 3)) + 1) * (8 * (3 / 2 - η / 2) / η) := by
          field_simp; ring
      _ ≤ (ε * Real.log T + 9) * (12 / η) := by
          refine mul_le_mul hL ?_ (div_nonneg (by linarith) hη0.le) (by linarith)
          rw [div_le_div_iff₀ hη0 hη0]; nlinarith
      _ = 12 * (ε * Real.log T + 9) / η := by ring
  have hexp := Real.exp_le_exp.mpr (neg_le_neg hkey)
  linarith

end zetaTypicalHeight

/-- **Almost every height is typical.** For `0 < η ≤ 1`, `0 < ε ≤ 1` and `δ > 0`, for all large
`T` the atypical heights in `[T, 2T]` have measure at most `δT`. -/
theorem eventually_volume_not_zetaTypicalHeight_le {η ε δ : ℝ} (hη0 : 0 < η) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hδ : 0 < δ) :
    ∀ᶠ T in Filter.atTop,
      volume {t | t ∈ Icc T (2 * T) ∧ ¬ zetaTypicalHeight η ε T t} ≤ ENNReal.ofReal (δ * T) := by
  filter_upwards [(Filter.tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).eventually
      (eventually_volume_zetaZeroShadow_le (σ := 1 / 2 + η / 4) (ℓ := 2) (κ := δ / 4)
        (by linarith) (by norm_num) (by positivity)),
    eventually_volume_zetaLargeNear_le hε hε1 (δ := δ / 2) (by positivity),
    Filter.eventually_ge_atTop 0] with T hshadow hlarge hT0
  have hsub : {t | t ∈ Icc T (2 * T) ∧ ¬ zetaTypicalHeight η ε T t} ⊆
      (zetaZeroShadow (1 / 2 + η / 4) 2 ∩ Icc 0 (2 * T)) ∪ zetaLargeNear T (T ^ ε) := by
    rintro t ⟨ht, hnt⟩
    by_cases hs : t ∈ zetaZeroShadow (1 / 2 + η / 4) 2
    · exact Or.inl ⟨hs, by linarith [ht.1], ht.2⟩
    · by_cases hl : t ∈ zetaLargeNear T (T ^ ε)
      · exact Or.inr hl
      · exact absurd ⟨ht, hs, hl⟩ hnt
  calc volume {t | t ∈ Icc T (2 * T) ∧ ¬ zetaTypicalHeight η ε T t}
      ≤ volume (zetaZeroShadow (1 / 2 + η / 4) 2 ∩ Icc 0 (2 * T)) + volume (zetaLargeNear T (T ^ ε)) :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (δ / 4 * (2 * T)) + ENNReal.ofReal (δ / 2 * T) := add_le_add hshadow hlarge
    _ = ENNReal.ofReal (δ * T) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

end RHTower

end
