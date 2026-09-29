import Mathlib

/-!
# Bohr envelope bound for cosine series at logarithmic frequencies

For `f(t) = Σ_n a_n cos(t log n)` with `Σ|a_n| < ∞`, the Cesàro means over `[8, T]` of
`f(t)·cos(t log m)` tend to the Bohr coefficient `a_m/2` for `m ≥ 2`, and to `0` for `m = 1`, when
`a_0 = a_1 = 0` (`tendsto_mean_logCosSeries_mul_cos`). The proof is dominated convergence for the
series of interval integrals followed by Tannery's theorem.

**Envelope bound** (`abs_le_four_mul_of_logCosSeries_envelope`). Suppose `f ≥ −ε` on `[8, ∞)` with
`ε ≥ 0` of Cesàro mean `E`. Then `|a_m| ≤ 4E` for every `m ≥ 2`: `f` has mean zero, so
`∫|f| ≤ ∫f + 2∫ε`, and each Bohr coefficient is at most the mean of `|f|`.

This is the averaging step of the singular deficit law for Weil-positive completions:
- `f = Re(−D_w(σ+it))` for the deviation `w = λ − Λ`;
- `ε` is the Poisson-smoothed mass of the off-line pairs and critical atom deficits;
- a nonzero coefficient of `w` forces a linear density of singular modifications.
-/

open Filter Topology MeasureTheory intervalIntegral

noncomputable section

namespace RHTower

/-- The Cesàro mean of `cos(δt)` over `[8, T]` tends to `[δ = 0]`. -/
theorem tendsto_integral_cos_mul_div_eight (δ : ℝ) :
    Tendsto (fun T : ℝ => (∫ t in (8 : ℝ)..T, Real.cos (δ * t)) / T) atTop
      (𝓝 (if δ = 0 then 1 else 0)) := by
  split_ifs with hδ
  · subst hδ
    have h0 : Tendsto (fun T : ℝ => (1 - 8 / T : ℝ)) atTop (𝓝 1) := by
      have := (tendsto_const_nhds (x := (1 : ℝ))).sub
        ((tendsto_const_nhds (x := (8 : ℝ))).div_atTop tendsto_id)
      simpa using this
    refine h0.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    simp only [zero_mul, Real.cos_zero, intervalIntegral.integral_const, smul_eq_mul, mul_one]
    field_simp
  · have hform : ∀ T : ℝ, (∫ t in (8 : ℝ)..T, Real.cos (δ * t)) =
        δ⁻¹ * (Real.sin (δ * T) - Real.sin (δ * 8)) := by
      intro T
      rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hδ, integral_cos,
        smul_eq_mul]
    have hbound : ∀ T : ℝ, |∫ t in (8 : ℝ)..T, Real.cos (δ * t)| ≤ 2 / |δ| := by
      intro T
      rw [hform, abs_mul, abs_inv]
      have h1 : |Real.sin (δ * T) - Real.sin (δ * 8)| ≤ 2 := by
        have := abs_sub (Real.sin (δ * T)) (Real.sin (δ * 8))
        have h2 := Real.abs_sin_le_one (δ * T)
        have h3 := Real.abs_sin_le_one (δ * 8)
        linarith
      have hpos : 0 < |δ| := abs_pos.mpr hδ
      rw [div_eq_mul_inv, mul_comm 2]
      exact mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hpos.le)
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hlim : Tendsto (fun T : ℝ => (2 / |δ|) / T) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ hlim
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hT]
    exact div_le_div_of_nonneg_right (hbound T) hT.le

theorem abs_integral_cos_mul_div_le_one (δ : ℝ) {T : ℝ} (hT : 8 ≤ T) :
    |(∫ t in (8 : ℝ)..T, Real.cos (δ * t)) / T| ≤ 1 := by
  have hT0 : 0 < T := by linarith
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (8 : ℝ)) (b := T)
    (f := fun t => Real.cos (δ * t)) (C := 1) (fun t _ => by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ T - 8)] at h
  rw [abs_div, abs_of_pos hT0, div_le_one hT0]
  linarith

/-- The cosine series `Σ a_n cos(t log n)`. -/
def logCosSeries (a : ℕ → ℝ) (t : ℝ) : ℝ := ∑' n : ℕ, a n * Real.cos (t * Real.log n)

theorem continuous_logCosSeries {a : ℕ → ℝ} (ha : Summable fun n => |a n|) :
    Continuous (logCosSeries a) := by
  refine continuous_tsum (u := fun n => |a n|) (fun n => by fun_prop) ha ?_
  intro n t
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

theorem abs_logCosSeries_le {a : ℕ → ℝ} (ha : Summable fun n => |a n|) (t : ℝ) :
    |logCosSeries a t| ≤ ∑' n, |a n| := by
  have hs : Summable fun n => a n * Real.cos (t * Real.log n) :=
    Summable.of_norm_bounded ha (fun n => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
  calc |logCosSeries a t| = ‖∑' n, a n * Real.cos (t * Real.log n)‖ := rfl
    _ ≤ ∑' n, ‖a n * Real.cos (t * Real.log n)‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' n, |a n| := by
        refine Summable.tsum_le_tsum (fun n => ?_) hs.norm ha
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

/-- The product-to-sum term of `logCosSeries a t · cos(t log m)`. -/
def logCosSeriesProdTerm (a : ℕ → ℝ) (m n : ℕ) (t : ℝ) : ℝ :=
  a n / 2 * (Real.cos ((Real.log n + Real.log m) * t) + Real.cos ((Real.log n - Real.log m) * t))

theorem logCosSeries_mul_cos_eq {a : ℕ → ℝ} (m : ℕ) (t : ℝ) :
    logCosSeries a t * Real.cos (t * Real.log m) = ∑' n, logCosSeriesProdTerm a m n t := by
  rw [logCosSeries, ← tsum_mul_right]
  congr 1
  funext n
  rw [logCosSeriesProdTerm, show (Real.log n + Real.log m) * t = t * Real.log n + t * Real.log m by ring,
    show (Real.log n - Real.log m) * t = t * Real.log n - t * Real.log m by ring,
    Real.cos_add, Real.cos_sub]
  ring

theorem abs_logCosSeriesProdTerm_le (a : ℕ → ℝ) (m n : ℕ) (t : ℝ) :
    |logCosSeriesProdTerm a m n t| ≤ |a n| := by
  rw [logCosSeriesProdTerm, abs_mul, abs_div, abs_two]
  have h1 := Real.abs_cos_le_one ((Real.log n + Real.log m) * t)
  have h2 := Real.abs_cos_le_one ((Real.log n - Real.log m) * t)
  have h3 : |Real.cos ((Real.log n + Real.log m) * t) + Real.cos ((Real.log n - Real.log m) * t)| ≤ 2 :=
    (abs_add_le _ _).trans (by linarith)
  have := mul_le_mul_of_nonneg_left h3 (div_nonneg (abs_nonneg (a n)) (by norm_num : (0 : ℝ) ≤ 2))
  linarith

theorem hasSum_integral_logCosSeriesProdTerm {a : ℕ → ℝ} (ha : Summable fun n => |a n|) (m : ℕ)
    (T : ℝ) :
    HasSum (fun n => ∫ t in (8 : ℝ)..T, logCosSeriesProdTerm a m n t)
      (∫ t in (8 : ℝ)..T, logCosSeries a t * Real.cos (t * Real.log m)) := by
  refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun n _ => |a n|)
    (fun n => (by unfold logCosSeriesProdTerm; fun_prop : Continuous _).aestronglyMeasurable)
    (fun n => Eventually.of_forall fun t _ => by
      rw [Real.norm_eq_abs]; exact abs_logCosSeriesProdTerm_le a m n t)
    (Eventually.of_forall fun t _ => ha)
    (by simp) ?_
  refine Eventually.of_forall fun t _ => ?_
  rw [logCosSeries_mul_cos_eq]
  refine (Summable.of_norm_bounded ha fun n => ?_).hasSum
  rw [Real.norm_eq_abs]; exact abs_logCosSeriesProdTerm_le a m n t

theorem integral_logCosSeriesProdTerm (a : ℕ → ℝ) (m n : ℕ) (T : ℝ) :
    ∫ t in (8 : ℝ)..T, logCosSeriesProdTerm a m n t =
      a n / 2 * ((∫ t in (8 : ℝ)..T, Real.cos ((Real.log n + Real.log m) * t)) +
        ∫ t in (8 : ℝ)..T, Real.cos ((Real.log n - Real.log m) * t)) := by
  unfold logCosSeriesProdTerm
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add]
  · exact (by fun_prop : Continuous _).intervalIntegrable _ _
  · exact (by fun_prop : Continuous _).intervalIntegrable _ _

/-- **Bohr mean of a cosine series against a frequency.** -/
theorem tendsto_mean_logCosSeries_mul_cos {a : ℕ → ℝ} (ha : Summable fun n => |a n|) (m : ℕ) :
    Tendsto (fun T : ℝ => (∫ t in (8 : ℝ)..T, logCosSeries a t * Real.cos (t * Real.log m)) / T)
      atTop (𝓝 (∑' n, a n / 2 * ((if Real.log n + Real.log m = 0 then 1 else 0) +
        (if Real.log n - Real.log m = 0 then 1 else 0)))) := by
  have hrep : ∀ T : ℝ, (∫ t in (8 : ℝ)..T, logCosSeries a t * Real.cos (t * Real.log m)) / T =
      ∑' n, a n / 2 * ((∫ t in (8 : ℝ)..T, Real.cos ((Real.log n + Real.log m) * t)) / T +
        (∫ t in (8 : ℝ)..T, Real.cos ((Real.log n - Real.log m) * t)) / T) := by
    intro T
    have h := ((hasSum_integral_logCosSeriesProdTerm ha m T).div_const T).tsum_eq
    rw [← h]
    congr 1
    funext n
    rw [integral_logCosSeriesProdTerm]
    ring
  simp_rw [hrep]
  refine tendsto_tsum_of_dominated_convergence (bound := fun n => |a n|) ha (fun n => ?_) ?_
  · exact ((tendsto_integral_cos_mul_div_eight _).add (tendsto_integral_cos_mul_div_eight _)).const_mul _
  · filter_upwards [eventually_ge_atTop (8 : ℝ)] with T hT n
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_two]
    have h1 := abs_integral_cos_mul_div_le_one (Real.log n + Real.log m) hT
    have h2 := abs_integral_cos_mul_div_le_one (Real.log n - Real.log m) hT
    have h3 := (abs_add_le _ _).trans (add_le_add h1 h2)
    have := mul_le_mul_of_nonneg_left h3 (div_nonneg (abs_nonneg (a n)) (by norm_num : (0 : ℝ) ≤ 2))
    linarith

theorem bohrLimit_eq_coeff {a : ℕ → ℝ} (ha0 : a 0 = 0) {m : ℕ} (hm : 2 ≤ m) :
    (∑' n, a n / 2 * ((if Real.log n + Real.log m = 0 then (1 : ℝ) else 0) +
      (if Real.log n - Real.log m = 0 then 1 else 0))) = a m / 2 := by
  have hm0 : (0 : ℝ) < Real.log m := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  rw [tsum_eq_single m]
  · have h1 : Real.log (m : ℝ) + Real.log m ≠ 0 := by linarith
    simp [h1]
  · intro n hn
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp [ha0]
    · have hn0 : (0 : ℝ) ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hpos)
      have h1 : Real.log (n : ℝ) + Real.log m ≠ 0 := by linarith
      have h2 : Real.log (n : ℝ) - Real.log m ≠ 0 := by
        intro h
        have heq : Real.log (n : ℝ) = Real.log m := by linarith
        have := Real.log_injOn_pos (Set.mem_Ioi.mpr (by exact_mod_cast hpos))
          (Set.mem_Ioi.mpr (by exact_mod_cast (by omega : 0 < m))) heq
        exact hn (by exact_mod_cast this)
      simp [h1, h2]

theorem bohrLimit_one_eq_zero {a : ℕ → ℝ} (ha0 : a 0 = 0) (ha1 : a 1 = 0) :
    (∑' n, a n / 2 * ((if Real.log n + Real.log ((1 : ℕ) : ℝ) = 0 then (1 : ℝ) else 0) +
      (if Real.log n - Real.log ((1 : ℕ) : ℝ) = 0 then 1 else 0))) = 0 := by
  refine (tsum_congr (fun n => ?_)).trans tsum_zero
  simp only [Nat.cast_one, Real.log_one, add_zero, sub_zero]
  by_cases h : Real.log (n : ℝ) = 0
  · rcases Real.log_eq_zero.mp h with h' | h' | h'
    · have : n = 0 := by exact_mod_cast h'
      subst this; simp [ha0]
    · have : n = 1 := by exact_mod_cast h'
      subst this; simp [ha1]
    · have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
  · simp [h]

/-- **Bohr envelope bound.**  If a cosine series `f(t) = Σ a_n cos(t log n)` with `Σ|a_n| < ∞`
and `a_0 = a_1 = 0` is bounded below by `−ε` on `[8, ∞)`, where `ε ≥ 0` has Cesàro mean `E`, then
every coefficient satisfies `|a_m| ≤ 4E`.

Since `f` has mean zero, `∫|f| = ∫f + 2∫f⁻ ≤ ∫f + 2∫ε`, and the Bohr coefficient
`a_m/2 = lim (1/T)∫ f(t)cos(t log m) dt` is at most the mean of `|f|`. -/
theorem abs_le_four_mul_of_logCosSeries_envelope {a : ℕ → ℝ} (ha : Summable fun n => |a n|)
    (ha0 : a 0 = 0) (ha1 : a 1 = 0) {ε : ℝ → ℝ} (hε0 : ∀ t, 0 ≤ ε t)
    (hεint : ∀ T, IntervalIntegrable ε volume 8 T) {E : ℝ}
    (hE : Tendsto (fun T : ℝ => (∫ t in (8 : ℝ)..T, ε t) / T) atTop (𝓝 E))
    (hf : ∀ t, 8 ≤ t → -ε t ≤ logCosSeries a t) {m : ℕ} (hm : 2 ≤ m) : |a m| ≤ 4 * E := by
  have hcont := continuous_logCosSeries ha
  have hg := tendsto_mean_logCosSeries_mul_cos ha m
  rw [bohrLimit_eq_coeff ha0 hm] at hg
  have hF := tendsto_mean_logCosSeries_mul_cos ha 1
  rw [bohrLimit_one_eq_zero ha0 ha1] at hF
  have hF' : Tendsto (fun T : ℝ => (∫ t in (8 : ℝ)..T, logCosSeries a t) / T) atTop (𝓝 0) := by
    refine hF.congr' (Eventually.of_forall fun T => ?_)
    simp
  have hsum := hF'.add (hE.const_mul 2)
  have hbound : ∀ᶠ T in atTop, |(∫ t in (8 : ℝ)..T, logCosSeries a t * Real.cos (t * Real.log m)) / T|
      ≤ (∫ t in (8 : ℝ)..T, logCosSeries a t) / T + 2 * ((∫ t in (8 : ℝ)..T, ε t) / T) := by
    filter_upwards [eventually_ge_atTop (8 : ℝ)] with T hT
    have hT0 : 0 < T := by linarith
    have hint1 : IntervalIntegrable (fun t => logCosSeries a t * Real.cos (t * Real.log m)) volume 8 T :=
      (hcont.mul (by fun_prop)).intervalIntegrable _ _
    have hint2 : IntervalIntegrable (logCosSeries a) volume 8 T := hcont.intervalIntegrable _ _
    have hpt : ∀ t ∈ Set.Icc (8 : ℝ) T,
        |logCosSeries a t * Real.cos (t * Real.log m)| ≤ logCosSeries a t + 2 * ε t := by
      intro t ht
      have h1 := hf t ht.1
      have h2 := hε0 t
      rw [abs_mul]
      have h3 := Real.abs_cos_le_one (t * Real.log m)
      have h4 : |logCosSeries a t| ≤ logCosSeries a t + 2 * ε t := by
        rcases le_or_gt 0 (logCosSeries a t) with h | h
        · rw [abs_of_nonneg h]; linarith
        · rw [abs_of_neg h]; linarith
      calc |logCosSeries a t| * |Real.cos (t * Real.log m)| ≤ |logCosSeries a t| * 1 :=
            mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
        _ ≤ _ := by linarith
    have hI : |∫ t in (8 : ℝ)..T, logCosSeries a t * Real.cos (t * Real.log m)| ≤
        (∫ t in (8 : ℝ)..T, logCosSeries a t) + 2 * ∫ t in (8 : ℝ)..T, ε t := by
      calc |∫ t in (8 : ℝ)..T, logCosSeries a t * Real.cos (t * Real.log m)|
          ≤ ∫ t in (8 : ℝ)..T, |logCosSeries a t * Real.cos (t * Real.log m)| :=
            intervalIntegral.abs_integral_le_integral_abs hT
        _ ≤ ∫ t in (8 : ℝ)..T, (logCosSeries a t + 2 * ε t) :=
            intervalIntegral.integral_mono_on hT hint1.abs (hint2.add ((hεint T).const_mul 2))
              hpt
        _ = (∫ t in (8 : ℝ)..T, logCosSeries a t) + 2 * ∫ t in (8 : ℝ)..T, ε t := by
            rw [intervalIntegral.integral_add hint2 ((hεint T).const_mul 2),
              intervalIntegral.integral_const_mul]
    rw [abs_div, abs_of_pos hT0]
    rw [div_le_iff₀ hT0]
    have : ((∫ t in (8 : ℝ)..T, logCosSeries a t) / T + 2 * ((∫ t in (8 : ℝ)..T, ε t) / T)) * T =
        (∫ t in (8 : ℝ)..T, logCosSeries a t) + 2 * ∫ t in (8 : ℝ)..T, ε t := by
      field_simp
    rw [this]; exact hI
  have hlim := le_of_tendsto_of_tendsto hg.abs hsum hbound
  rw [zero_add, abs_div, abs_two] at hlim
  linarith

end RHTower
