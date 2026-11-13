import Mathlib

/-!
# Sine transforms of decreasing functions

If `f` is continuous, integrable on `(0, ∞)` and strictly decreasing on `[0, ∞)`, then
`∫₀^∞ f(t) sin(yt) dt > 0` for every `y > 0`.  Over each period `[kP, (k+1)P]`, `P = 2π/y`, the
second half-period is the first shifted by `P/2` with the sign of the sine reversed, so the period
integral is `∫_{kP}^{kP+P/2} (f(t) - f(t + P/2)) sin(yt) dt ≥ 0`, strictly positive for `k = 0`;
the partial sums increase to the improper integral.

`integral_Ioi_mul_sin_pos_of_strictAntiOn_Ioi` is the same statement for a function that is only
strictly decreasing on `(0, ∞)`, possibly unbounded at `0` and not continuous.
-/

open Set MeasureTheory Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Over a full period the sine transform folds onto the first half-period:
`∫_a^{a+2π/y} f(t) sin(yt) dt = ∫_a^{a+π/y} (f(t) - f(t + π/y)) sin(yt) dt`. -/
theorem integral_period_mul_sin_eq {f : ℝ → ℝ} (hf : Continuous f) {y : ℝ} (hy : 0 < y)
    (a : ℝ) :
    ∫ t in a..a + 2 * Real.pi / y, f t * Real.sin (y * t) =
      ∫ t in a..a + Real.pi / y, (f t - f (t + Real.pi / y)) * Real.sin (y * t) := by
  set h := Real.pi / y with hh
  have hcont : Continuous fun t => f t * Real.sin (y * t) := by fun_prop
  have e : ∀ t, f (t + h) * Real.sin (y * (t + h)) = -(f (t + h) * Real.sin (y * t)) := by
    intro t
    rw [show y * (t + h) = y * t + Real.pi by rw [hh]; field_simp, Real.sin_add_pi]
    ring
  rw [show a + 2 * Real.pi / y = a + h + h by rw [hh]; ring,
    ← intervalIntegral.integral_add_adjacent_intervals (b := a + h)
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _),
    ← intervalIntegral.integral_comp_add_right (a := a) (b := a + h)
      (fun t => f t * Real.sin (y * t)) h]
  simp only [e, intervalIntegral.integral_neg]
  rw [← sub_eq_add_neg, ← intervalIntegral.integral_sub (hcont.intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t => f (t + h) * Real.sin (y * t)).intervalIntegrable _ _)]
  refine intervalIntegral.integral_congr fun t _ => ?_
  ring

/-- **Positivity of sine transforms of decreasing functions.** If `f` is continuous, integrable on
`(0, ∞)` and strictly decreasing on `[0, ∞)`, then `∫₀^∞ f(t) sin(yt) dt > 0` for `y > 0`. -/
theorem integral_mul_sin_pos_of_strictAntiOn {f : ℝ → ℝ} (hf : Continuous f)
    (hanti : StrictAntiOn f (Ici 0)) (hint : IntegrableOn f (Ioi 0)) {y : ℝ} (hy : 0 < y) :
    0 < ∫ t in Ioi 0, f t * Real.sin (y * t) := by
  set P := 2 * Real.pi / y with hPdef
  set h := Real.pi / y with hhdef
  have hP : 0 < P := by positivity
  have hh : 0 < h := by positivity
  have hcont : Continuous fun t => f t * Real.sin (y * t) := by fun_prop
  have hint' : IntegrableOn (fun t => f t * Real.sin (y * t)) (Ioi 0) := by
    refine hint.norm.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  set I : ℕ → ℝ := fun k => ∫ t in (k * P)..((k + 1) * P), f t * Real.sin (y * t)
  have hdrop : ∀ t, 0 ≤ t → 0 < f t - f (t + h) := fun t ht =>
    sub_pos.mpr (hanti (mem_Ici.mpr ht) (mem_Ici.mpr (by linarith)) (by linarith))
  have hIk : ∀ k, 0 ≤ I k := by
    intro k
    simp only [I]
    rw [show ((k : ℝ) + 1) * P = k * P + 2 * Real.pi / y by rw [hPdef]; ring,
      integral_period_mul_sin_eq hf hy]
    refine intervalIntegral.integral_nonneg (by linarith) fun t ht => mul_nonneg
      (hdrop t (le_trans (by positivity) ht.1)).le ?_
    rw [← Real.sin_sub_nat_mul_two_pi (y * t) k]
    have h1 : (k : ℝ) * P ≤ t := ht.1
    have h2 : t ≤ k * P + h := ht.2
    have hyP : y * P = 2 * Real.pi := by rw [hPdef]; field_simp
    have hyh : y * h = Real.pi := by rw [hhdef]; field_simp
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · have := mul_le_mul_of_nonneg_left h1 hy.le
      nlinarith
    · have := mul_le_mul_of_nonneg_left h2 hy.le
      nlinarith
  have hI0 : 0 < I 0 := by
    simp only [I, Nat.cast_zero, zero_mul, zero_add, one_mul]
    rw [show P = 0 + 2 * Real.pi / y by rw [hPdef]; ring, integral_period_mul_sin_eq hf hy,
      zero_add]
    refine intervalIntegral.intervalIntegral_pos_of_pos_on
      ((by fun_prop : Continuous fun t => (f t - f (t + Real.pi / y)) *
        Real.sin (y * t)).intervalIntegrable _ _) (fun t ht => mul_pos (hdrop t ht.1.le)
          (Real.sin_pos_of_pos_of_lt_pi (mul_pos hy ht.1) ?_)) hh
    have := mul_lt_mul_of_pos_left ht.2 hy
    rwa [mul_div_cancel₀ _ hy.ne'] at this
  have hsum : ∀ n : ℕ, ∫ t in (0 : ℝ)..(n * P), f t * Real.sin (y * t) =
      ∑ k ∈ Finset.range n, I k := by
    intro n
    have := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
      (a := fun k : ℕ => (k : ℝ) * P) (n := n) (fun k _ => hcont.intervalIntegrable _ _)
    simp only [Nat.cast_zero, zero_mul, Nat.cast_succ] at this
    exact this.symm
  have hlim := intervalIntegral_tendsto_integral_Ioi 0 hint'
    (tendsto_natCast_atTop_atTop.atTop_mul_const hP)
  refine lt_of_lt_of_le hI0 (ge_of_tendsto hlim ?_)
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [hsum n]
  calc I 0 = ∑ k ∈ Finset.range 1, I k := by simp
    _ ≤ ∑ k ∈ Finset.range n, I k :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn) fun k _ _ => hIk k

/-- **Positivity of sine transforms of decreasing functions, without continuity.** If `g` is
strictly decreasing on `(0, ∞)` and `g(t) sin(yt)` is integrable there, then
`∫₀^∞ g(t) sin(yt) dt > 0` for `y > 0`; `g` may be unbounded at `0`. The negative part of the
sine is its positive part shifted by `h = π/y`, and it vanishes on `(0, h]`, so the integral is
`∫₀^∞ (g(t) − g(t + h)) sin⁺(yt) dt`. -/
theorem integral_Ioi_mul_sin_pos_of_strictAntiOn_Ioi {g : ℝ → ℝ}
    (hanti : StrictAntiOn g (Ioi 0)) {y : ℝ} (hy : 0 < y)
    (hint : IntegrableOn (fun t => g t * Real.sin (y * t)) (Ioi 0)) :
    0 < ∫ t in Ioi 0, g t * Real.sin (y * t) := by
  set h := Real.pi / y with hh
  have hh0 : 0 < h := by positivity
  have hyh : y * h = Real.pi := by rw [hh]; field_simp
  have hsinm : Measurable fun t : ℝ => Real.sin (y * t) := by fun_prop
  have hpos : MeasurableSet {t : ℝ | 0 < Real.sin (y * t)} :=
    measurableSet_lt measurable_const hsinm
  have hneg : MeasurableSet {t : ℝ | Real.sin (y * t) < 0} :=
    measurableSet_lt hsinm measurable_const
  -- the parts of the integrand on the positive and the negative lobes of the sine
  have hP : IntegrableOn (fun t => g t * max (Real.sin (y * t)) 0) (Ioi 0) := by
    have h1 := hint.indicator hpos
    refine h1.congr_fun (fun t _ => ?_) measurableSet_Ioi
    by_cases hs : 0 < Real.sin (y * t)
    · rw [indicator_of_mem (by exact hs), max_eq_left hs.le]
    · rw [indicator_of_notMem (by exact hs), max_eq_right (not_lt.mp hs), mul_zero]
  have hN : IntegrableOn (fun t => g t * max (-Real.sin (y * t)) 0) (Ioi 0) := by
    have h1 := hint.neg.indicator hneg
    refine h1.congr_fun (fun t _ => ?_) measurableSet_Ioi
    by_cases hs : Real.sin (y * t) < 0
    · rw [indicator_of_mem (by exact hs), max_eq_left (by linarith)]
      simp only [Pi.neg_apply]
      ring
    · rw [indicator_of_notMem (by exact hs), max_eq_right (by linarith [not_lt.mp hs]), mul_zero]
  -- the negative part lives on `(h, ∞)` and is the shifted positive part
  have hNzero : ∀ t ∈ Ioi (0 : ℝ) \ Ioi h, g t * max (-Real.sin (y * t)) 0 = 0 := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have hth : t ≤ h := not_lt.mp ht.2
    have hs : 0 ≤ Real.sin (y * t) := Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
      (by rw [← hyh]; exact mul_le_mul_of_nonneg_left hth hy.le)
    rw [max_eq_right (by linarith), mul_zero]
  have hpre : (fun t : ℝ => t + h) ⁻¹' Ioi h = Ioi 0 := by
    ext t
    simp
  have hshiftfun : ∀ t : ℝ, g (t + h) * max (-Real.sin (y * (t + h))) 0 =
      g (t + h) * max (Real.sin (y * t)) 0 := by
    intro t
    rw [show y * (t + h) = y * t + Real.pi by rw [mul_add, hyh], Real.sin_add_pi, neg_neg]
  have hQ : IntegrableOn (fun t => g (t + h) * max (Real.sin (y * t)) 0) (Ioi 0) := by
    have h1 := ((measurePreserving_add_right volume h).integrableOn_comp_preimage
      (measurableEmbedding_addRight h)).2 (hN.mono_set (Ioi_subset_Ioi hh0.le))
    rw [hpre] at h1
    exact h1.congr_fun (fun t _ => hshiftfun t) measurableSet_Ioi
  have hNQ : ∫ t in Ioi 0, g t * max (-Real.sin (y * t)) 0 =
      ∫ t in Ioi 0, g (t + h) * max (Real.sin (y * t)) 0 := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (Ioi_subset_Ioi hh0.le) hNzero,
      ← (measurePreserving_add_right volume h).setIntegral_preimage_emb
        (measurableEmbedding_addRight h) (fun t => g t * max (-Real.sin (y * t)) 0) (Ioi h), hpre]
    exact setIntegral_congr_fun measurableSet_Ioi fun t _ => hshiftfun t
  -- assemble
  have hsplit : ∫ t in Ioi 0, g t * Real.sin (y * t) =
      ∫ t in Ioi 0, (g t - g (t + h)) * max (Real.sin (y * t)) 0 := by
    have e1 : ∀ t : ℝ, g t * Real.sin (y * t) =
        g t * max (Real.sin (y * t)) 0 - g t * max (-Real.sin (y * t)) 0 := by
      intro t
      rcases le_total 0 (Real.sin (y * t)) with hs | hs
      · rw [max_eq_left hs, max_eq_right (by linarith)]; ring
      · rw [max_eq_right hs, max_eq_left (by linarith)]; ring
    simp only [e1]
    rw [integral_sub hP hN, hNQ, ← integral_sub hP hQ]
    exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring
  rw [hsplit, setIntegral_pos_iff_support_of_nonneg_ae
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_))
    ((hP.sub hQ).congr_fun (fun t _ => by simp only [Pi.sub_apply]; ring) measurableSet_Ioi)]
  · refine lt_of_lt_of_le ?_ (measure_mono (?_ : Ioo 0 h ⊆ _))
    · rw [Real.volume_Ioo, sub_zero]
      exact ENNReal.ofReal_pos.2 hh0
    · intro t ht
      have hs : 0 < Real.sin (y * t) := Real.sin_pos_of_pos_of_lt_pi (mul_pos hy ht.1)
        (by rw [← hyh]; exact mul_lt_mul_of_pos_left ht.2 hy)
      have hg : g (t + h) < g t := hanti (mem_Ioi.2 ht.1) (mem_Ioi.2 (by linarith [ht.1]))
        (by linarith)
      refine ⟨?_, ht.1⟩
      rw [Function.mem_support, max_eq_left hs.le]
      exact (mul_pos (sub_pos.2 hg) hs).ne'
  · have ht0 : 0 < t := ht
    have hg : g (t + h) < g t := hanti (mem_Ioi.2 ht0) (mem_Ioi.2 (by linarith)) (by linarith)
    exact mul_nonneg (sub_pos.2 hg).le (le_max_right _ _)

end GaloisForLFunctions.HTGeometry
