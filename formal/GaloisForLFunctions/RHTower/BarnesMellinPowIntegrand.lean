import GaloisForLFunctions.RHTower.BarnesMellinIntegrandAnalysis

/-!
# The Mellin integrand of the Euler derivatives

The Euler operator `D = x d/dx` acts on `x^{-w}` by multiplication by `-w`, so the Mellin
integrand of `D^m` applied to the canonical-product sum is

```text
F_m(w) = (-w)^m x^{-w} ζ(-sw) (-π/sin πw) .
```

The extra factor is entire and polynomially bounded on every vertical strip, so it changes neither
the location of the poles nor the exponential decay: every contour estimate carries over with the
polynomial exponent raised by `m`, and every residue is multiplied by `(-p)^m`.
-/

open Complex Filter Set MeasureTheory

namespace RHTower

noncomputable section

/-- The Mellin integrand of the `m`-th Euler derivative. -/
def barnesIntegrandPow (s x : ℝ) (m : ℕ) (w : ℂ) : ℂ := (-w) ^ m * barnesIntegrand s x w

@[simp] theorem barnesIntegrandPow_zero (s x : ℝ) (w : ℂ) :
    barnesIntegrandPow s x 0 w = barnesIntegrand s x w := by
  rw [barnesIntegrandPow, pow_zero, one_mul]

/-- The polynomial weight is bounded by a power of the height on a vertical strip. -/
theorem norm_neg_pow_le {σ₀ σ₁ : ℝ} (m : ℕ) {σ t : ℝ} (h0 : σ₀ ≤ σ) (h1 : σ ≤ σ₁)
    (ht : 1 ≤ |t|) :
    ‖(-((σ : ℂ) + (t : ℂ) * I)) ^ m‖ ≤ (|σ₀| + |σ₁| + 1) ^ m * |t| ^ m := by
  have hnorm : ‖(-((σ : ℂ) + (t : ℂ) * I))‖ = ‖((σ : ℂ) + (t : ℂ) * I)‖ := norm_neg _
  have hre : ((σ : ℂ) + (t : ℂ) * I).re = σ := by simp
  have him : ((σ : ℂ) + (t : ℂ) * I).im = t := by simp
  have hbase : ‖((σ : ℂ) + (t : ℂ) * I)‖ ≤ |σ| + |t| := by
    have h := Complex.norm_le_abs_re_add_abs_im ((σ : ℂ) + (t : ℂ) * I)
    rwa [hre, him] at h
  have hσabs : |σ| ≤ |σ₀| + |σ₁| := by
    rcases le_total σ 0 with hneg | hpos
    · rw [abs_of_nonpos hneg]
      linarith [neg_le_abs σ₀, abs_nonneg σ₁]
    · rw [abs_of_nonneg hpos]
      linarith [le_abs_self σ₁, abs_nonneg σ₀]
  have hstep : ‖(-((σ : ℂ) + (t : ℂ) * I))‖ ≤ (|σ₀| + |σ₁| + 1) * |t| := by
    rw [hnorm]
    refine hbase.trans ?_
    nlinarith [abs_nonneg σ₀, abs_nonneg σ₁, ht]
  calc ‖(-((σ : ℂ) + (t : ℂ) * I)) ^ m‖ = ‖(-((σ : ℂ) + (t : ℂ) * I))‖ ^ m := norm_pow _ _
    _ ≤ ((|σ₀| + |σ₁| + 1) * |t|) ^ m :=
        pow_le_pow_left₀ (norm_nonneg _) hstep m
    _ = (|σ₀| + |σ₁| + 1) ^ m * |t| ^ m := mul_pow _ _ _

/-- **Uniform exponential decay of the weighted integrand.** -/
theorem exists_bound_norm_barnesIntegrandPow {s x : ℝ} (hs : 0 < s) (hx : 0 < x) (m : ℕ)
    (σ₀ σ₁ : ℝ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ σ t : ℝ, σ₀ ≤ σ → σ ≤ σ₁ → 1 + 1 / s ≤ |t| →
      ‖barnesIntegrandPow s x m ((σ : ℂ) + (t : ℂ) * I)‖
        ≤ C * |t| ^ N * Real.exp (-(Real.pi * |t|)) := by
  obtain ⟨C, N, hC0, hC⟩ := exists_bound_norm_barnesIntegrand hs hx σ₀ σ₁
  refine ⟨(|σ₀| + |σ₁| + 1) ^ m * C, m + N, by positivity, ?_⟩
  intro σ t h0 h1 ht
  have hs1 : (0 : ℝ) < 1 / s := by positivity
  have ht1 : (1 : ℝ) ≤ |t| := by linarith
  have hw := norm_neg_pow_le (σ₀ := σ₀) (σ₁ := σ₁) m h0 h1 ht1
  have hb := hC σ t h0 h1 ht
  rw [barnesIntegrandPow, norm_mul]
  have hnn : (0 : ℝ) ≤ C * |t| ^ N * Real.exp (-(Real.pi * |t|)) := by positivity
  calc ‖(-((σ : ℂ) + (t : ℂ) * I)) ^ m‖ * ‖barnesIntegrand s x ((σ : ℂ) + (t : ℂ) * I)‖
      ≤ ((|σ₀| + |σ₁| + 1) ^ m * |t| ^ m) * (C * |t| ^ N * Real.exp (-(Real.pi * |t|))) :=
        mul_le_mul hw hb (norm_nonneg _) (by positivity)
    _ = (|σ₀| + |σ₁| + 1) ^ m * C * |t| ^ (m + N) * Real.exp (-(Real.pi * |t|)) := by
        rw [pow_add]; ring

/-- The weighted integrand is holomorphic wherever the plain one is. -/
theorem differentiableAt_barnesIntegrandPow {s x : ℝ} (hx : 0 < x) (m : ℕ) {w : ℂ}
    (hζ : -(s : ℂ) * w ≠ 1) (hsin : Complex.sin ((Real.pi : ℂ) * w) ≠ 0) :
    DifferentiableAt ℂ (barnesIntegrandPow s x m) w := by
  have h1 : DifferentiableAt ℂ (fun v : ℂ => (-v) ^ m) w :=
    (differentiableAt_id.neg).pow m
  exact h1.mul (differentiableAt_barnesIntegrand hx hζ hsin)

theorem holomorphicOn_barnesIntegrandPow {s x σ₀ σ₁ : ℝ} (hx : 0 < x) (m : ℕ) {p : ℂ}
    (hpoles : ∀ w : ℂ, w ∈ Icc σ₀ σ₁ ×ℂ (univ : Set ℝ) → w ≠ p →
      -(s : ℂ) * w ≠ 1 ∧ Complex.sin ((Real.pi : ℂ) * w) ≠ 0) :
    HolomorphicOn (barnesIntegrandPow s x m) (Icc σ₀ σ₁ ×ℂ (univ : Set ℝ) \ {p}) := by
  intro w hw
  obtain ⟨hstrip, hne⟩ := hw
  obtain ⟨hζ, hsin⟩ := hpoles w hstrip hne
  exact (differentiableAt_barnesIntegrandPow hx m hζ hsin).differentiableWithinAt

theorem continuous_barnesIntegrandPow_vertical {s x σ : ℝ} (hx : 0 < x) (m : ℕ)
    (hζ : -(s : ℝ) * σ ≠ 1) (hsin : Real.sin (Real.pi * σ) ≠ 0) :
    Continuous fun t : ℝ => barnesIntegrandPow s x m ((σ : ℂ) + (t : ℂ) * I) := by
  have hline : Continuous fun t : ℝ => ((σ : ℂ) + (t : ℂ) * I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hpow : Continuous fun t : ℝ => (-((σ : ℂ) + (t : ℂ) * I)) ^ m :=
    (hline.neg).pow m
  exact hpow.mul (continuous_barnesIntegrand_vertical hx hζ hsin)


/-! ### Contour estimates for the weighted integrand -/

theorem eventually_norm_horizontal_pow_le {s x σ₀ σ₁ : ℝ} (hs : 0 < s) (hx : 0 < x) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ y : ℝ, 1 + 1 / s ≤ |y| →
      ‖∫ u in σ₀..σ₁, barnesIntegrandPow s x m ((u : ℂ) + (y : ℂ) * I)‖
        ≤ (D * |σ₁ - σ₀|) * (1 + y ^ (2 : ℕ))⁻¹ := by
  obtain ⟨C, N, hC0, hC⟩ :=
    exists_bound_norm_barnesIntegrandPow hs hx m (min σ₀ σ₁) (max σ₀ σ₁)
  refine ⟨C * Real.exp Real.pi * (((N + 2).factorial : ℝ) / Real.pi ^ (N + 2)), by positivity,
    fun y hy => ?_⟩
  have hbd : ∀ u ∈ Set.uIoc σ₀ σ₁,
      ‖barnesIntegrandPow s x m ((u : ℂ) + (y : ℂ) * I)‖
        ≤ C * |y| ^ N * Real.exp (-(Real.pi * |y|)) := by
    intro u hu
    have hu' : u ∈ Set.uIcc σ₀ σ₁ := Set.uIoc_subset_uIcc hu
    rw [Set.uIcc_eq_union] at hu'
    have hmin : min σ₀ σ₁ ≤ u := by
      rcases hu' with h | h
      · exact le_trans (min_le_left _ _) h.1
      · exact le_trans (min_le_right _ _) h.1
    have hmax : u ≤ max σ₀ σ₁ := by
      rcases hu' with h | h
      · exact le_trans h.2 (le_max_right _ _)
      · exact le_trans h.2 (le_max_left _ _)
    exact hC u y hmin hmax hy
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  refine hint.trans ?_
  have hdom := GaloisForLFunctions.HTGeometry.polyExp_le_inv_one_add_sq hC0 Real.pi_pos N y
  calc C * |y| ^ N * Real.exp (-(Real.pi * |y|)) * |σ₁ - σ₀|
      ≤ (C * Real.exp Real.pi * (((N + 2).factorial : ℝ) / Real.pi ^ (N + 2)))
          * (1 + y ^ (2 : ℕ))⁻¹ * |σ₁ - σ₀| :=
        mul_le_mul_of_nonneg_right hdom (abs_nonneg _)
    _ = (C * Real.exp Real.pi * (((N + 2).factorial : ℝ) / Real.pi ^ (N + 2)) * |σ₁ - σ₀|)
          * (1 + y ^ (2 : ℕ))⁻¹ := by ring

theorem tendsto_horizontal_barnesIntegrandPow_atTop {s x σ₀ σ₁ : ℝ} (hs : 0 < s) (hx : 0 < x)
    (m : ℕ) :
    Filter.Tendsto (fun y : ℝ => ∫ u in σ₀..σ₁, barnesIntegrandPow s x m ((u : ℂ) + (y : ℂ) * I))
      atTop (nhds 0) := by
  obtain ⟨D, hD0, hD⟩ := eventually_norm_horizontal_pow_le (σ₀ := σ₀) (σ₁ := σ₁) hs hx m
  have hg : Filter.Tendsto (fun y : ℝ => (D * |σ₁ - σ₀|) * (1 + y ^ (2 : ℕ))⁻¹) atTop (nhds 0) := by
    simpa using tendsto_inv_one_add_sq_atTop.const_mul (D * |σ₁ - σ₀|)
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [Filter.eventually_ge_atTop (1 + 1 / s)] with y hy
  have hs1 : (0 : ℝ) < 1 / s := by positivity
  have hy0 : (0 : ℝ) ≤ y := by linarith
  exact hD y (by rw [abs_of_nonneg hy0]; exact hy)

theorem tendsto_horizontal_barnesIntegrandPow_atBot {s x σ₀ σ₁ : ℝ} (hs : 0 < s) (hx : 0 < x)
    (m : ℕ) :
    Filter.Tendsto (fun y : ℝ => ∫ u in σ₀..σ₁, barnesIntegrandPow s x m ((u : ℂ) + (y : ℂ) * I))
      atBot (nhds 0) := by
  obtain ⟨D, hD0, hD⟩ := eventually_norm_horizontal_pow_le (σ₀ := σ₀) (σ₁ := σ₁) hs hx m
  have hg : Filter.Tendsto (fun y : ℝ => (D * |σ₁ - σ₀|) * (1 + y ^ (2 : ℕ))⁻¹) atBot (nhds 0) := by
    simpa using tendsto_inv_one_add_sq_atBot.const_mul (D * |σ₁ - σ₀|)
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [Filter.eventually_le_atBot (-(1 + 1 / s))] with y hy
  have hs1 : (0 : ℝ) < 1 / s := by positivity
  refine hD y ?_
  rw [abs_of_nonpos (by linarith)]
  linarith

theorem integrable_barnesIntegrandPow_vertical {s x σ : ℝ} (hs : 0 < s) (hx : 0 < x) (m : ℕ)
    (hζ : -(s : ℝ) * σ ≠ 1) (hsin : Real.sin (Real.pi * σ) ≠ 0) :
    Integrable fun t : ℝ => barnesIntegrandPow s x m ((σ : ℂ) + (t : ℂ) * I) := by
  classical
  set T : ℝ := 1 + 1 / s with hT
  have hT0 : 0 < T := by rw [hT]; positivity
  have hcont := continuous_barnesIntegrandPow_vertical hx m hζ hsin
  obtain ⟨C, N, hC0, hC⟩ := exists_bound_norm_barnesIntegrandPow hs hx m σ σ
  obtain ⟨C₂, hC₂⟩ := (isCompact_Icc (a := -T) (b := T)).exists_bound_of_continuousOn
    hcont.continuousOn
  set K : ℝ := C * Real.exp Real.pi * (((N + 2).factorial : ℝ) / Real.pi ^ (N + 2)) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  set D : ℝ := max K (max C₂ 0 * (1 + T ^ (2 : ℕ))) with hD
  have hD0 : 0 ≤ D := le_trans hK0 (le_max_left _ _)
  refine MeasureTheory.Integrable.mono' (g := fun t : ℝ => D * (1 + t ^ (2 : ℕ))⁻¹)
    (integrable_inv_one_add_sq.const_mul D) hcont.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun t => ?_
  have hden : (0 : ℝ) < 1 + t ^ (2 : ℕ) := by positivity
  rcases le_or_gt T |t| with hbig | hsmall
  · have hb := hC σ t le_rfl le_rfl (by rw [← hT]; exact hbig)
    have hdom := GaloisForLFunctions.HTGeometry.polyExp_le_inv_one_add_sq hC0 Real.pi_pos N t
    refine hb.trans (hdom.trans ?_)
    rw [← hK]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · have hmem : t ∈ Set.Icc (-T) T := ⟨by
      have := abs_lt.mp hsmall
      linarith [this.1], by
      have := abs_lt.mp hsmall
      linarith [this.2]⟩
    have hb := hC₂ t hmem
    have hb' : ‖barnesIntegrandPow s x m ((σ : ℂ) + (t : ℂ) * I)‖ ≤ max C₂ 0 :=
      hb.trans (le_max_left _ _)
    have hsq : 1 + t ^ (2 : ℕ) ≤ 1 + T ^ (2 : ℕ) := by
      have habs : |t| ≤ T := le_of_lt hsmall
      nlinarith [abs_nonneg t, sq_abs t]
    have hstep : max C₂ 0 ≤ D * (1 + t ^ (2 : ℕ))⁻¹ := by
      rw [le_mul_inv_iff₀ hden]
      calc max C₂ 0 * (1 + t ^ (2 : ℕ)) ≤ max C₂ 0 * (1 + T ^ (2 : ℕ)) :=
            mul_le_mul_of_nonneg_left hsq (le_max_right _ _)
        _ ≤ D := le_max_right _ _
    exact hb'.trans hstep

end

end RHTower

