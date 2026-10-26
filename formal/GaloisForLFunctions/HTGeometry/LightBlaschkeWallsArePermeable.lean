import GaloisForLFunctions.HTGeometry.InfiniteBlaschkeMultiplier

/-!
# Light Blaschke walls are permeable

A discrete Cauchy transform `Σ_n ν_n/(u − a_n)` with poles `a_n` in the unit disc accumulating only
at the unit circle can agree outside the circle with a holomorphic function without its poles
cancelling: the circle is then a wall (Wolff). The wall is permeable when the poles form a Blaschke
sequence, `Σ (1 − |a_n|) < ∞`, and the masses are light, `Σ |ν_n|/(1 − |a_n|) < ∞`.

* **Shadows** (`shadow`, `volume_shadow_inter_le`, `ae_eventually_notMem_shadow`). If the ray
  through `e^{iθ}` passes within `1 − |a|` of `a`, then `|(|a| e^{iθ}) − a| < 2(1 − |a|)`: an arc of
  length `O(1 − |a|)`. By Borel–Cantelli almost every ray meets only finitely many shadows.
* **Radial limits** (`tendsto_cauchy_radial`). Off finitely many shadows the masses dominate the
  series uniformly along the ray, so the transform has a radial limit at almost every `ζ`; from
  outside the series converges uniformly up to the circle (`continuousOn_cauchy_outside`).
* **Cancelling the poles** (`norm_infiniteBlaschkeProduct_le`). The Blaschke product `B` of the
  poles has `|B(u)| ≤ |u − a_n|/(1 − |a_n|)`, so `B·G` is bounded by the lightness sum.
* **Permeability** (`masses_eq_zero_of_cauchy_eq_outside`). If the transform agrees outside the
  circle with a function holomorphic beyond the poles, `B·(G − E)` extends holomorphically to an
  annulus inside the circle, is bounded there and has radial limits `0` almost everywhere. Its circle
  moments do not depend on the radius and tend to `0`, so it vanishes, and every residue `ν_n` is
  zero.
-/

open Complex Filter Topology Set Metric MeasureTheory
open scoped Real ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### 1. Shadows -/

/-- The **shadow** of a disc point `a`: the directions `θ` with `|(|a| e^{iθ}) − a| < 2(1 − |a|)`. -/
def shadow (a : ℂ) : Set ℝ := {θ | ‖(‖a‖ : ℂ) * cexp (θ * I) - a‖ < 2 * (1 - ‖a‖)}

theorem norm_exp_ofReal_mul_I' (θ : ℝ) : ‖cexp (θ * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

/-- Off its shadow, the ray through `e^{iθ}` stays at distance `≥ 1 − |a|` from `a`. -/
theorem one_sub_norm_le_of_notMem_shadow {a : ℂ} {θ : ℝ} (hθ : θ ∉ shadow a) {r : ℝ}
    (hr : 0 ≤ r) : 1 - ‖a‖ ≤ ‖(r : ℂ) * cexp (θ * I) - a‖ := by
  by_contra hlt
  push Not at hlt
  apply hθ
  show ‖(‖a‖ : ℂ) * cexp (θ * I) - a‖ < 2 * (1 - ‖a‖)
  have h1 : |r - ‖a‖| ≤ ‖(r : ℂ) * cexp (θ * I) - a‖ := by
    have := abs_norm_sub_norm_le ((r : ℂ) * cexp (θ * I)) a
    rwa [norm_mul, norm_exp_ofReal_mul_I', mul_one, Complex.norm_real,
      Real.norm_of_nonneg hr] at this
  have h2 : ‖(‖a‖ : ℂ) * cexp (θ * I) - (r : ℂ) * cexp (θ * I)‖ = |r - ‖a‖| := by
    rw [← sub_mul, norm_mul, norm_exp_ofReal_mul_I', mul_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  calc ‖(‖a‖ : ℂ) * cexp (θ * I) - a‖
      ≤ ‖(‖a‖ : ℂ) * cexp (θ * I) - (r : ℂ) * cexp (θ * I)‖ + ‖(r : ℂ) * cexp (θ * I) - a‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < 2 * (1 - ‖a‖) := by rw [h2]; linarith

/-- **Jordan's inequality on the circle**: `|e^{ix} − 1| ≥ 2|x|/π` for `|x| ≤ π`. -/
theorem two_div_pi_mul_abs_le_norm_exp_sub_one {x : ℝ} (hx : |x| ≤ π) :
    2 / π * |x| ≤ ‖cexp (x * I) - 1‖ := by
  rw [mul_comm (x : ℂ) I, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_two,
    Real.norm_eq_abs]
  have hy : |x| / 2 ≤ π / 2 := by linarith
  have hs := Real.mul_le_sin (by positivity : (0 : ℝ) ≤ |x| / 2) hy
  have habs : |Real.sin (x / 2)| = Real.sin (|x| / 2) := by
    rcases abs_cases x with ⟨hxa, -⟩ | ⟨hxa, -⟩
    · rw [hxa, abs_of_nonneg (by linarith)]
    · rw [hxa, neg_div, Real.sin_neg, abs_neg, abs_of_nonneg (by linarith)]
  rw [habs]
  have : 2 / π * |x| = 2 * (2 / π * (|x| / 2)) := by ring
  rw [this]
  linarith

/-- The shadow of `a ≠ 0` meets `(0, 2π]` in measure at most `4π (1 − |a|)/|a|`. -/
theorem volume_shadow_inter_le {a : ℂ} (ha0 : a ≠ 0) (ha1 : ‖a‖ ≤ 1) :
    volume (shadow a ∩ Ioc 0 (2 * π)) ≤ ENNReal.ofReal (4 * π * ((1 - ‖a‖) / ‖a‖)) := by
  set α := a.arg with hα
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  set c : ℝ := π * ((1 - ‖a‖) / ‖a‖) with hc
  have hc0 : 0 ≤ c := mul_nonneg Real.pi_pos.le (div_nonneg (by linarith) hna.le)
  have haexp : a = (‖a‖ : ℂ) * cexp (α * I) := (Complex.norm_mul_exp_arg_mul_I a).symm
  -- a shadow direction is within `c` of `α` or of `α + 2π`
  have hsub : shadow a ∩ Ioc 0 (2 * π) ⊆ Ioo (α - c) (α + c) ∪ Ioo (α + 2 * π - c) (α + 2 * π + c) := by
    rintro θ ⟨hθ, hθ0, hθ2⟩
    have hθ' : ‖a‖ * ‖cexp ((θ - α : ℝ) * I) - 1‖ < 2 * (1 - ‖a‖) := by
      have e : (‖a‖ : ℂ) * cexp (θ * I) - a =
          (‖a‖ : ℂ) * cexp (α * I) * (cexp ((θ - α : ℝ) * I) - 1) := by
        conv_lhs => rw [haexp]
        rw [mul_sub, mul_one, mul_assoc, ← Complex.exp_add]
        push_cast
        ring_nf
      have := hθ
      simp only [shadow, mem_setOf_eq] at this
      rw [e, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
        norm_exp_ofReal_mul_I', mul_one] at this
      exact this
    have hlt : ‖cexp ((θ - α : ℝ) * I) - 1‖ < 2 * ((1 - ‖a‖) / ‖a‖) := by
      rw [mul_div_assoc', lt_div_iff₀ hna]
      linarith
    have hαI := Complex.neg_pi_lt_arg a
    have hαS := Complex.arg_le_pi a
    by_cases hx : θ - α ≤ π
    · left
      have habs : |θ - α| ≤ π := abs_le.mpr ⟨by linarith, hx⟩
      have h := two_div_pi_mul_abs_le_norm_exp_sub_one habs
      have h' : |θ - α| < c := by
        rw [hc]
        have hpi := Real.pi_pos
        have : 2 / π * |θ - α| < 2 * ((1 - ‖a‖) / ‖a‖) := lt_of_le_of_lt h hlt
        rw [div_mul_eq_mul_div, div_lt_iff₀ hpi] at this
        linarith
      exact ⟨by linarith [neg_abs_le (θ - α)], by linarith [le_abs_self (θ - α)]⟩
    · right
      push Not at hx
      have habs : |θ - α - 2 * π| ≤ π := abs_le.mpr ⟨by linarith, by linarith⟩
      have h := two_div_pi_mul_abs_le_norm_exp_sub_one habs
      have hper : cexp ((θ - α - 2 * π : ℝ) * I) = cexp ((θ - α : ℝ) * I) := by
        push_cast
        rw [sub_mul, Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one]
      rw [hper] at h
      have h' : |θ - α - 2 * π| < c := by
        rw [hc]
        have hpi := Real.pi_pos
        have : 2 / π * |θ - α - 2 * π| < 2 * ((1 - ‖a‖) / ‖a‖) := lt_of_le_of_lt h hlt
        rw [div_mul_eq_mul_div, div_lt_iff₀ hpi] at this
        linarith
      exact ⟨by linarith [neg_abs_le (θ - α - 2 * π)], by linarith [le_abs_self (θ - α - 2 * π)]⟩
  calc volume (shadow a ∩ Ioc 0 (2 * π))
      ≤ volume (Ioo (α - c) (α + c) ∪ Ioo (α + 2 * π - c) (α + 2 * π + c)) := measure_mono hsub
    _ ≤ volume (Ioo (α - c) (α + c)) + volume (Ioo (α + 2 * π - c) (α + 2 * π + c)) :=
        measure_union_le _ _
    _ = ENNReal.ofReal (2 * c) + ENNReal.ofReal (2 * c) := by
        rw [Real.volume_Ioo, Real.volume_Ioo]
        congr 2 <;> ring
    _ = ENNReal.ofReal (4 * π * ((1 - ‖a‖) / ‖a‖)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        rw [hc]
        ring

/-- **Almost every ray meets only finitely many shadows** of a Blaschke sequence in `ρ₁ < |a_n|`. -/
theorem ae_eventually_notMem_shadow {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ < 1)
    (hbl : Summable fun n => 1 - ‖a n‖) {ρ₁ : ℝ} (hρ₁ : 0 < ρ₁) (hρa : ∀ n, ρ₁ < ‖a n‖) :
    ∀ᵐ θ ∂(volume.restrict (Ioc 0 (2 * π))), ∀ᶠ n in atTop, θ ∉ shadow (a n) := by
  refine ae_eventually_notMem ?_
  have hnn : ∀ n, 0 ≤ 4 * π / ρ₁ * (1 - ‖a n‖) := fun n =>
    mul_nonneg (by positivity) (by linarith [ha n])
  refine ne_top_of_le_ne_top (b := ∑' n, ENNReal.ofReal (4 * π / ρ₁ * (1 - ‖a n‖))) ?_
    (ENNReal.tsum_le_tsum fun n => ?_)
  · rw [← ENNReal.ofReal_tsum_of_nonneg hnn (hbl.mul_left _)]
    exact ENNReal.ofReal_ne_top
  · rw [Measure.restrict_apply' measurableSet_Ioc]
    have ha0 : a n ≠ 0 := fun h => by
      have := hρa n
      rw [h, norm_zero] at this
      linarith
    refine (volume_shadow_inter_le ha0 (ha n).le).trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : (1 - ‖a n‖) / ‖a n‖ ≤ (1 - ‖a n‖) / ρ₁ :=
      div_le_div_of_nonneg_left (by linarith [ha n]) hρ₁ (hρa n).le
    calc 4 * π * ((1 - ‖a n‖) / ‖a n‖) ≤ 4 * π * ((1 - ‖a n‖) / ρ₁) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 4 * π / ρ₁ * (1 - ‖a n‖) := by ring

/-! ### 2. The transform on the circle -/

variable {a ν : ℕ → ℂ}

/-- Outside the open disc the poles keep distance `1 − |a_n|`. -/
theorem one_sub_norm_le_norm_sub {b u : ℂ} (hu : 1 ≤ ‖u‖) : 1 - ‖b‖ ≤ ‖u - b‖ := by
  have := norm_sub_norm_le u b
  linarith

/-- **Up to the circle from outside.** For light masses the series converges uniformly on `|u| ≥ 1`. -/
theorem continuousOn_cauchy_outside (ha : ∀ n, ‖a n‖ < 1)
    (hlight : Summable fun n => ‖ν n‖ / (1 - ‖a n‖)) :
    ContinuousOn (fun u => ∑' n, ν n / (u - a n)) {u | 1 ≤ ‖u‖} := by
  refine continuousOn_tsum (fun n => ?_) hlight fun n u hu => ?_
  · refine continuousOn_const.div (continuousOn_id.sub continuousOn_const) fun u hu h0 => ?_
    have := one_sub_norm_le_norm_sub (b := a n) hu
    rw [h0, norm_zero] at this
    linarith [ha n]
  · rw [norm_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (by linarith [ha n])
      (one_sub_norm_le_norm_sub hu)

/-- **Radial limits.** If the ray through `e^{iθ}` meets only finitely many shadows, the transform
tends along it to the series at `e^{iθ}`. -/
theorem tendsto_cauchy_radial (ha : ∀ n, ‖a n‖ < 1)
    (hlight : Summable fun n => ‖ν n‖ / (1 - ‖a n‖)) {θ : ℝ}
    (hθ : ∀ᶠ n in atTop, θ ∉ shadow (a n)) :
    Tendsto (fun r : ℝ => ∑' n, ν n / ((r : ℂ) * cexp (θ * I) - a n)) (𝓝[<] 1)
      (𝓝 (∑' n, ν n / (cexp (θ * I) - a n))) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hθ
  have hd : ∀ n, 0 < 1 - ‖a n‖ := fun n => by linarith [ha n]
  -- near `1` the finitely many remaining poles keep distance `(1 − |a_n|)/2`
  have hnear : ∀ᶠ r in 𝓝[<] (1 : ℝ), 0 ≤ r ∧ ∀ n ∈ Finset.range N, 1 - (1 - ‖a n‖) / 2 ≤ r := by
    refine (eventually_nhdsWithin_of_eventually_nhds ?_).and ?_
    · exact Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)
    · refine (Finset.eventually_all _).mpr fun n _ => eventually_nhdsWithin_of_eventually_nhds ?_
      exact Ici_mem_nhds (by linarith [hd n])
  refine tendsto_tsum_of_dominated_convergence (bound := fun n => 2 * (‖ν n‖ / (1 - ‖a n‖)))
    (hlight.mul_left 2) (fun n => ?_) ?_
  · have hcont : ContinuousAt (fun r : ℝ => ν n / ((r : ℂ) * cexp (θ * I) - a n)) 1 := by
      refine continuousAt_const.div (by fun_prop) ?_
      intro h0
      have := one_sub_norm_le_norm_sub (b := a n) (u := cexp (θ * I))
        (by rw [norm_exp_ofReal_mul_I'])
      rw [show ((1 : ℝ) : ℂ) * cexp (θ * I) - a n = cexp (θ * I) - a n by push_cast; ring] at h0
      rw [h0, norm_zero] at this
      linarith [hd n]
    have := hcont.tendsto.mono_left nhdsWithin_le_nhds
    simpa using this
  · filter_upwards [hnear] with r ⟨hr0, hr⟩ n
    rw [norm_div]
    have hdist : (1 - ‖a n‖) / 2 ≤ ‖(r : ℂ) * cexp (θ * I) - a n‖ := by
      by_cases hn : n < N
      · have h1 := hr n (Finset.mem_range.mpr hn)
        have h2 := norm_sub_norm_le ((r : ℂ) * cexp (θ * I)) (a n)
        rw [norm_mul, norm_exp_ofReal_mul_I', mul_one, Complex.norm_real,
          Real.norm_of_nonneg hr0] at h2
        linarith
      · have := one_sub_norm_le_of_notMem_shadow (hN n (not_lt.mp hn)) hr0
        linarith [hd n]
    calc ‖ν n‖ / ‖(r : ℂ) * cexp (θ * I) - a n‖ ≤ ‖ν n‖ / ((1 - ‖a n‖) / 2) :=
          div_le_div_of_nonneg_left (norm_nonneg _) (by linarith [hd n]) hdist
      _ = 2 * (‖ν n‖ / (1 - ‖a n‖)) := by field_simp

/-! ### 3. Cancelling the poles -/

/-- The Blaschke product is dominated by each of its factors. -/
theorem norm_infiniteBlaschkeProduct_le_factor (ha : ∀ n, ‖a n‖ < 1)
    (hbl : Summable fun n => 1 - ‖a n‖) {z : ℂ} (hz : ‖z‖ < 1) (n : ℕ) :
    ‖infiniteBlaschkeProduct a z‖ ≤ ‖normalizedBlaschkeFactor (a n) z‖ := by
  have hprod := infiniteBlaschkeProduct_hasProdLocallyUniformlyOn a ha hbl
  have hzmem : z ∈ Metric.ball (0 : ℂ) 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz
  have hlim := hprod.tendstoLocallyUniformlyOn_finsetRange.tendsto_at hzmem
  have hnormlim : Tendsto (fun N => ‖∏ m ∈ Finset.range N, normalizedBlaschkeFactor (a m) z‖)
      atTop (𝓝 ‖infiniteBlaschkeProduct a z‖) := (continuous_norm.tendsto _).comp hlim
  apply le_of_tendsto hnormlim
  filter_upwards [eventually_gt_atTop n] with N hN
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_range.mpr hN), norm_mul, norm_prod]
  refine mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one (fun _ _ => norm_nonneg _)
    fun m _ => norm_normalizedBlaschkeFactor_le_one (ha m) hz.le)

/-- A normalized factor over its zero: `|b_a(z)| ≤ |z − a|/(1 − |a|)` on the closed disc. -/
theorem norm_normalizedBlaschkeFactor_le {b z : ℂ} (hb : ‖b‖ < 1) (hz : ‖z‖ ≤ 1) :
    ‖normalizedBlaschkeFactor b z‖ ≤ ‖z - b‖ / (1 - ‖b‖) := by
  have hd : 0 < 1 - ‖b‖ := by linarith
  by_cases hb0 : b = 0
  · subst hb0
    simp only [normalizedBlaschkeFactor, if_pos, norm_zero, sub_zero, div_one, le_refl]
  rw [normalizedBlaschkeFactor, if_neg hb0, blaschkeFactor, norm_mul, norm_neg, norm_div,
    Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.mpr hb0),
    one_mul, norm_div]
  have hden : 1 - ‖b‖ ≤ ‖1 - (starRingEnd ℂ) b * z‖ := by
    have h := norm_sub_norm_le (1 : ℂ) ((starRingEnd ℂ) b * z)
    rw [norm_one, norm_mul, Complex.norm_conj] at h
    have : ‖b‖ * ‖z‖ ≤ ‖b‖ := mul_le_of_le_one_right (norm_nonneg _) hz
    linarith
  exact div_le_div_of_nonneg_left (norm_nonneg _) hd hden

/-- **The Blaschke product cancels each pole with a light factor**:
`|B(z)| ≤ |z − a_n|/(1 − |a_n|)`. -/
theorem norm_infiniteBlaschkeProduct_le (ha : ∀ n, ‖a n‖ < 1)
    (hbl : Summable fun n => 1 - ‖a n‖) {z : ℂ} (hz : ‖z‖ < 1) (n : ℕ) :
    ‖infiniteBlaschkeProduct a z‖ ≤ ‖z - a n‖ / (1 - ‖a n‖) :=
  (norm_infiniteBlaschkeProduct_le_factor ha hbl hz n).trans
    (norm_normalizedBlaschkeFactor_le (ha n) hz.le)

end

end GaloisForLFunctions.HTGeometry
