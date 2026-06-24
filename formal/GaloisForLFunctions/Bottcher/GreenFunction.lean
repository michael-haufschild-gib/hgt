/-
# Böttcher tower — escape-rate / Green's function: the convergence estimate

The Green's function of `Ω_c` with pole at `∞` is `G_c(z) = lim_n 2⁻ⁿ log‖f_c^[n] z‖`
(`= log|φ_c|`, the bridge from `Dynamics` to the period formula `dlogφ_c = ∫(z-ζ)⁻¹dμ_c`
and to `cap(K_c)=1`). Its convergence rests on the one-step estimate

  `|log‖f_c w‖ − 2·log‖w‖| ≤ 2‖c‖/‖w‖²`   (for `2‖c‖ ≤ ‖w‖²`),

which makes `n ↦ 2⁻ⁿ log‖f_c^[n] z‖` Cauchy on the escape set (the bound is summable
in `n` once the orbit grows). This file proves that estimate; the limit construction
and `G_c = 0` on `K_c` build on it.
-/
import GaloisForLFunctions.Bottcher.Dynamics
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Topology

namespace Bottcher

/-- Near `r = 1`, the logarithm is controlled by the deviation: `|log r| ≤ 2|r-1|`
for `r ≥ 1/2`. -/
theorem abs_log_le_two_abs_sub_one {r : ℝ} (hr : 1 / 2 ≤ r) :
    |Real.log r| ≤ 2 * |r - 1| := by
  have hr0 : 0 < r := by linarith
  have hup : Real.log r ≤ r - 1 := Real.log_le_sub_one_of_pos hr0
  have hlow : 1 - r⁻¹ ≤ Real.log r := Real.one_sub_inv_le_log_of_pos hr0
  have hinv : r * r⁻¹ = 1 := mul_inv_cancel₀ hr0.ne'
  by_cases hle : r ≤ 1
  · rw [abs_of_nonpos (show r - 1 ≤ 0 by linarith), abs_le]
    exact ⟨by nlinarith [hlow, hinv, hr0, hle, hr], by linarith [hup, hle]⟩
  · push_neg at hle
    rw [abs_of_pos (show 0 < r - 1 by linarith), abs_le]
    exact ⟨by nlinarith [hlow, hinv, hr0, hle, hr], by linarith [hup, hle]⟩

/-- **One-step Green estimate.** For `w` in the escape regime (`2‖c‖ ≤ ‖w‖²`, `w ≠ 0`),
one quadratic step changes the rescaled log by a summable amount:
`|log‖f_c w‖ − 2·log‖w‖| ≤ 2‖c‖/‖w‖²`. The Cauchy driver of `G_c`'s convergence. -/
theorem log_quadratic_approx {c w : ℂ} (hw : 2 * ‖c‖ ≤ ‖w‖ ^ 2) (hw0 : w ≠ 0) :
    |Real.log ‖quadratic c w‖ - 2 * Real.log ‖w‖| ≤ 2 * ‖c‖ / ‖w‖ ^ 2 := by
  rw [quadratic_apply]
  have hR2 : 0 < ‖w‖ ^ 2 := by positivity
  have hc0 : 0 ≤ ‖c‖ := norm_nonneg c
  have hnw2 : ‖w ^ 2‖ = ‖w‖ ^ 2 := by rw [norm_pow]
  have ha_up : ‖w ^ 2 + c‖ ≤ ‖w‖ ^ 2 + ‖c‖ := by
    calc ‖w ^ 2 + c‖ ≤ ‖w ^ 2‖ + ‖c‖ := norm_add_le _ _
      _ = ‖w‖ ^ 2 + ‖c‖ := by rw [hnw2]
  have ha_low : ‖w‖ ^ 2 - ‖c‖ ≤ ‖w ^ 2 + c‖ := by
    have h := norm_sub_norm_le (w ^ 2) (-c)
    rw [norm_neg, sub_neg_eq_add, hnw2] at h
    exact h
  have ha0 : 0 < ‖w ^ 2 + c‖ := by nlinarith [ha_low, hw, hR2]
  rw [show Real.log ‖w ^ 2 + c‖ - 2 * Real.log ‖w‖
        = Real.log (‖w ^ 2 + c‖ / ‖w‖ ^ 2) from by
      rw [Real.log_div ha0.ne' hR2.ne', Real.log_pow]; push_cast; ring]
  have hr_half : (1 : ℝ) / 2 ≤ ‖w ^ 2 + c‖ / ‖w‖ ^ 2 := by
    rw [le_div_iff₀ hR2]; linarith [ha_low, hw]
  have hr1 : |‖w ^ 2 + c‖ / ‖w‖ ^ 2 - 1| ≤ ‖c‖ / ‖w‖ ^ 2 := by
    rw [div_sub_one hR2.ne', abs_div, abs_of_pos hR2]
    gcongr
    rw [abs_le]; exact ⟨by linarith [ha_up], by linarith [ha_low]⟩
  calc |Real.log (‖w ^ 2 + c‖ / ‖w‖ ^ 2)|
      ≤ 2 * |‖w ^ 2 + c‖ / ‖w‖ ^ 2 - 1| := abs_log_le_two_abs_sub_one hr_half
    _ ≤ 2 * (‖c‖ / ‖w‖ ^ 2) := by linarith [hr1]
    _ = 2 * ‖c‖ / ‖w‖ ^ 2 := by ring

/-- The rescaled log of the orbit, `g_n(z) = 2⁻ⁿ·log‖f_c^[n] z‖`; its limit is `G_c`. -/
noncomputable def greenApprox (c z : ℂ) (n : ℕ) : ℝ :=
  (2 ^ n : ℝ)⁻¹ * Real.log ‖(quadratic c)^[n] z‖

/-- **Telescoping step bound.** Consecutive terms of `g_n` differ by a geometrically
small, summable amount on the escape set: `|g_{n+1} − g_n| ≤ 2⁻⁽ⁿ⁺¹⁾·2‖c‖/‖f_c^[n] z‖²`.
This is the Cauchy criterion driver for `G_c = lim g_n`. -/
theorem greenApprox_step_bound {c z : ℂ} (n : ℕ)
    (hw : 2 * ‖c‖ ≤ ‖(quadratic c)^[n] z‖ ^ 2) (hw0 : (quadratic c)^[n] z ≠ 0) :
    |greenApprox c z (n + 1) - greenApprox c z n|
      ≤ (2 ^ (n + 1) : ℝ)⁻¹ * (2 * ‖c‖ / ‖(quadratic c)^[n] z‖ ^ 2) := by
  unfold greenApprox
  rw [Function.iterate_succ', Function.comp_apply]
  set w := (quadratic c)^[n] z with hwdef
  rw [show (2 ^ (n + 1) : ℝ)⁻¹ * Real.log ‖quadratic c w‖ - (2 ^ n : ℝ)⁻¹ * Real.log ‖w‖
        = (2 ^ (n + 1) : ℝ)⁻¹ * (Real.log ‖quadratic c w‖ - 2 * Real.log ‖w‖) from by
      rw [pow_succ]; field_simp]
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 ^ (n + 1) : ℝ)⁻¹)]
  gcongr
  exact log_quadratic_approx hw hw0

/-- The positive-part rescaled log `g⁺_n(z) = 2⁻ⁿ·log⁺‖f_c^[n] z‖` (`log⁺ = log∘max(·,1)`).
Its limit is the genuine Green's function `G_c ≥ 0`. -/
noncomputable def greenApproxPlus (c z : ℂ) (n : ℕ) : ℝ :=
  (2 ^ n : ℝ)⁻¹ * Real.log (max ‖(quadratic c)^[n] z‖ 1)

/-- `g⁺_n ≥ 0` everywhere. -/
theorem greenApproxPlus_nonneg (c z : ℂ) (n : ℕ) : 0 ≤ greenApproxPlus c z n :=
  mul_nonneg (by positivity) (Real.log_nonneg (le_max_right _ _))

/-- **The Green's function vanishes on `K_c`.** On the filled Julia set the orbit is
bounded, so `g⁺_n(z) → 0`. This is the boundary condition `G_c = 0` on `K_c`. -/
theorem greenApproxPlus_tendsto_zero_of_mem {c z : ℂ} (hz : z ∈ filledJulia c) :
    Tendsto (greenApproxPlus c z) atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ => (2 ^ n : ℝ)⁻¹) atTop (𝓝 0) := by
    simp_rw [← inv_pow]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  refine squeeze_zero (greenApproxPlus_nonneg c z) (fun n => ?_)
    (g := fun n => (2 ^ n : ℝ)⁻¹ * Real.log (max (max 2 ‖c‖) 1)) ?_
  · -- g⁺_n ≤ (2^n)⁻¹ · log(max (max 2‖c‖) 1)
    have hbd : ‖(quadratic c)^[n] z‖ ≤ max 2 ‖c‖ := by
      have h := filledJulia_subset_closedBall c (filledJulia_forward hz n)
      rwa [Metric.mem_closedBall, dist_zero_right] at h
    unfold greenApproxPlus
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact Real.log_le_log (lt_of_lt_of_le one_pos (le_max_right _ _))
      (max_le_max hbd (le_refl 1))
  · simpa using hpow.mul_const (Real.log (max (max 2 ‖c‖) 1))

/-- **Escape regime is stable**: once `‖z‖ > 2` and `‖c‖ ≤ ‖z‖`, every iterate stays in
the one-step-estimate regime (`2‖c‖ ≤ ‖f_c^[n] z‖²`, nonzero), since the orbit grows. -/
theorem escape_regime_stable {c z : ℂ} (hc : ‖c‖ ≤ ‖z‖) (hz : 2 < ‖z‖) (n : ℕ) :
    2 * ‖c‖ ≤ ‖(quadratic c)^[n] z‖ ^ 2 ∧ (quadratic c)^[n] z ≠ 0 := by
  have hg := quadratic_orbit_growth hc hz n
  have hge1 : (1 : ℝ) ≤ (‖z‖ - 1) ^ n := one_le_pow₀ (by linarith)
  have hzn : ‖z‖ ≤ ‖(quadratic c)^[n] z‖ :=
    le_trans (by nlinarith [hge1, norm_nonneg z]) hg
  refine ⟨?_, ?_⟩
  · nlinarith [hzn, hc, hz, norm_nonneg z]
  · intro h; rw [h, norm_zero] at hzn; linarith

/-- **Geometric step bound.** In the escape regime the differences of `g_n` are bounded
by `(‖c‖/‖z‖²)·(1/2)ⁿ` — summable (ratio `1/2`), so `g_n` is Cauchy. The convergence
engine of the Böttcher coordinate. (Uses only `A ≥ ‖z‖`, since `(‖z‖-1)²ⁿ ≥ 1`.) -/
theorem greenApprox_step_geom_bound {c z : ℂ} (hc : ‖c‖ ≤ ‖z‖) (hz : 2 < ‖z‖) (n : ℕ) :
    |greenApprox c z (n + 1) - greenApprox c z n| ≤ ‖c‖ / ‖z‖ ^ 2 * (1 / 2) ^ n := by
  obtain ⟨hreg, hne⟩ := escape_regime_stable hc hz n
  have hz0 : (0 : ℝ) < ‖z‖ := by linarith
  have hz2 : (0 : ℝ) < ‖z‖ ^ 2 := pow_pos hz0 2
  have hge1 : (1 : ℝ) ≤ (‖z‖ - 1) ^ n := one_le_pow₀ (by linarith)
  have hzn : ‖z‖ ≤ ‖(quadratic c)^[n] z‖ :=
    le_trans (by nlinarith [hge1, norm_nonneg z]) (quadratic_orbit_growth hc hz n)
  have hAsq : ‖z‖ ^ 2 ≤ ‖(quadratic c)^[n] z‖ ^ 2 := by nlinarith [hzn, hz0]
  calc |greenApprox c z (n + 1) - greenApprox c z n|
      ≤ (2 ^ (n + 1) : ℝ)⁻¹ * (2 * ‖c‖ / ‖(quadratic c)^[n] z‖ ^ 2) :=
        greenApprox_step_bound n hreg hne
    _ ≤ (2 ^ (n + 1) : ℝ)⁻¹ * (2 * ‖c‖ / ‖z‖ ^ 2) := by gcongr
    _ = ‖c‖ / ‖z‖ ^ 2 * (1 / 2) ^ n := by rw [pow_succ, div_pow, one_pow]; field_simp

/-- **The Green's function exists on the escape set.** For `z` in the immediate escape
regime (`‖z‖ > 2`, `‖c‖ ≤ ‖z‖`), the rescaled logs `g_n(z)` form a Cauchy sequence
(summable geometric differences), so `G_c(z) = lim_n g_n(z)` exists. This is the
analytic core of the Böttcher coordinate `φ_c = exp(G_c + i·conj)`. -/
theorem greenApprox_converges {c z : ℂ} (hc : ‖c‖ ≤ ‖z‖) (hz : 2 < ‖z‖) :
    ∃ L : ℝ, Tendsto (greenApprox c z) atTop (𝓝 L) := by
  have hgeom : Summable (fun n : ℕ => ‖c‖ / ‖z‖ ^ 2 * (1 / 2 : ℝ) ^ n) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hsum : Summable (fun n => greenApprox c z (n + 1) - greenApprox c z n) := by
    apply Summable.of_norm
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hgeom
    rw [Real.norm_eq_abs]
    exact greenApprox_step_geom_bound hc hz n
  refine ⟨greenApprox c z 0 + ∑' n, (greenApprox c z (n + 1) - greenApprox c z n), ?_⟩
  have hcongr : ∀ n, greenApprox c z 0
      + ∑ i ∈ Finset.range n, (greenApprox c z (i + 1) - greenApprox c z i) = greenApprox c z n := by
    intro n
    rw [Finset.sum_range_sub (greenApprox c z) n]; ring
  exact (tendsto_const_nhds.add hsum.hasSum.tendsto_sum_nat).congr hcongr

/-- **Böttcher functional equation (rescaled-log form), per level.**
`g_n(f_c z) = 2·g_{n+1}(z)`. Passing to the limit gives `G_c(f_c z) = 2·G_c(z)`, i.e.
`φ_c(z²+c) = φ_c(z)²` — the defining relation of the Böttcher coordinate. -/
theorem greenApprox_quadratic (c z : ℂ) (n : ℕ) :
    greenApprox c (quadratic c z) n = 2 * greenApprox c z (n + 1) := by
  unfold greenApprox
  rw [← Function.iterate_succ_apply, pow_succ]
  field_simp

/-- The Green's function `G_c(z) = lim_n g_n(z)` (the escape rate; `= log|φ_c|`). -/
noncomputable def greenLimit (c z : ℂ) : ℝ := limUnder atTop (greenApprox c z)

/-- On the escape set, `g_n(z) → G_c(z)`. -/
theorem greenApprox_tendsto {c z : ℂ} (hc : ‖c‖ ≤ ‖z‖) (hz : 2 < ‖z‖) :
    Tendsto (greenApprox c z) atTop (𝓝 (greenLimit c z)) := by
  obtain ⟨L, hL⟩ := greenApprox_converges hc hz
  have : greenLimit c z = L := hL.limUnder_eq
  rw [this]; exact hL

/-- **Böttcher functional equation** `G_c(f_c z) = 2·G_c(z)` on the escape set
(i.e. `φ_c(z²+c) = φ_c(z)²`), obtained by passing `g_n(f_c z) = 2·g_{n+1}(z)` to the limit. -/
theorem greenLimit_quadratic {c z : ℂ} (hc : ‖c‖ ≤ ‖z‖) (hz : 2 < ‖z‖) :
    greenLimit c (quadratic c z) = 2 * greenLimit c z := by
  have hlt := quadratic_norm_lt hc hz
  have hfz_z : 2 < ‖quadratic c z‖ := lt_trans hz hlt
  have hfz_c : ‖c‖ ≤ ‖quadratic c z‖ := le_trans hc (le_of_lt hlt)
  have h1 : Tendsto (fun n => greenApprox c (quadratic c z) n) atTop
      (𝓝 (greenLimit c (quadratic c z))) := greenApprox_tendsto hfz_c hfz_z
  have h2 : Tendsto (fun n => 2 * greenApprox c z (n + 1)) atTop (𝓝 (2 * greenLimit c z)) :=
    ((greenApprox_tendsto hc hz).comp (tendsto_add_atTop_nat 1)).const_mul 2
  rw [funext (greenApprox_quadratic c z)] at h1
  exact tendsto_nhds_unique h1 h2

/-- Explicit telescoping representation `G_c(z) = g_0(z) + ∑ₙ (g_{n+1}-g_n)`. -/
theorem greenLimit_eq_tsum {c z : ℂ} (hc : ‖c‖ ≤ ‖z‖) (hz : 2 < ‖z‖) :
    greenLimit c z
      = greenApprox c z 0 + ∑' n, (greenApprox c z (n + 1) - greenApprox c z n) := by
  have hgeom : Summable (fun n : ℕ => ‖c‖ / ‖z‖ ^ 2 * (1 / 2 : ℝ) ^ n) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hsum : Summable (fun n => greenApprox c z (n + 1) - greenApprox c z n) := by
    apply Summable.of_norm
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hgeom
    rw [Real.norm_eq_abs]; exact greenApprox_step_geom_bound hc hz n
  have h2 : Tendsto (greenApprox c z) atTop
      (𝓝 (greenApprox c z 0 + ∑' n, (greenApprox c z (n + 1) - greenApprox c z n))) := by
    have hcongr : ∀ n, greenApprox c z 0
        + ∑ i ∈ Finset.range n, (greenApprox c z (i + 1) - greenApprox c z i) = greenApprox c z n := by
      intro n; rw [Finset.sum_range_sub (greenApprox c z) n]; ring
    exact (tendsto_const_nhds.add hsum.hasSum.tendsto_sum_nat).congr hcongr
  exact tendsto_nhds_unique (greenApprox_tendsto hc hz) h2

/-- **Lower bound** `G_c(z) ≥ log‖z‖ − 2‖c‖/‖z‖²` on the escape set (finite-sum / squeeze). -/
theorem greenLimit_lower_bound {c z : ℂ} (hc : ‖c‖ ≤ ‖z‖) (hz : 2 < ‖z‖) :
    Real.log ‖z‖ - 2 * ‖c‖ / ‖z‖ ^ 2 ≤ greenLimit c z := by
  have hgs : ∀ n, ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ k ≤ 2 := by
    intro n
    rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
    have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n := by positivity
    rw [div_le_iff_of_neg (by norm_num : (1 / 2 : ℝ) - 1 < 0)]; nlinarith [this]
  have hpern : ∀ n, Real.log ‖z‖ - 2 * ‖c‖ / ‖z‖ ^ 2 ≤ greenApprox c z n := by
    intro n
    have htel : greenApprox c z n = greenApprox c z 0
        + ∑ k ∈ Finset.range n, (greenApprox c z (k + 1) - greenApprox c z k) := by
      rw [Finset.sum_range_sub (greenApprox c z) n]; ring
    have h0 : greenApprox c z 0 = Real.log ‖z‖ := by simp [greenApprox]
    have hsb : |∑ k ∈ Finset.range n, (greenApprox c z (k + 1) - greenApprox c z k)|
        ≤ 2 * ‖c‖ / ‖z‖ ^ 2 := by
      calc |∑ k ∈ Finset.range n, (greenApprox c z (k + 1) - greenApprox c z k)|
          ≤ ∑ k ∈ Finset.range n, |greenApprox c z (k + 1) - greenApprox c z k| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ Finset.range n, ‖c‖ / ‖z‖ ^ 2 * (1 / 2 : ℝ) ^ k :=
            Finset.sum_le_sum (fun k _ => greenApprox_step_geom_bound hc hz k)
        _ = ‖c‖ / ‖z‖ ^ 2 * ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ k := by rw [← Finset.mul_sum]
        _ ≤ ‖c‖ / ‖z‖ ^ 2 * 2 := by gcongr; exact hgs n
        _ = 2 * ‖c‖ / ‖z‖ ^ 2 := by ring
    rw [htel, h0]; linarith [(abs_le.mp hsb).1]
  exact ge_of_tendsto (greenApprox_tendsto hc hz) (Filter.Eventually.of_forall hpern)

/-- **`G_c > 0` deep in the basin** (`‖z‖ > 3`): the Green's function is strictly positive,
i.e. `|φ_c(z)| > 1`. Combined with the functional equation this gives `G_c > 0` on all of
`Ω_c` (orbit escapes ⟹ some iterate has `‖·‖ > 3`). -/
theorem greenLimit_pos {c z : ℂ} (hc : ‖c‖ ≤ ‖z‖) (hz : 3 < ‖z‖) : 0 < greenLimit c z := by
  have hz0 : (0 : ℝ) < ‖z‖ := by linarith
  have hlb := greenLimit_lower_bound hc (by linarith : 2 < ‖z‖)
  have hcb : 2 * ‖c‖ / ‖z‖ ^ 2 ≤ 2 / ‖z‖ := by
    have h2 : 2 * ‖z‖ / ‖z‖ ^ 2 = 2 / ‖z‖ := by rw [pow_two]; field_simp
    calc 2 * ‖c‖ / ‖z‖ ^ 2 ≤ 2 * ‖z‖ / ‖z‖ ^ 2 := by gcongr
      _ = 2 / ‖z‖ := h2
  have hlog : 1 - 1 / ‖z‖ ≤ Real.log ‖z‖ := by
    have := Real.one_sub_inv_le_log_of_pos hz0; rwa [inv_eq_one_div] at this
  have hkey : 2 / ‖z‖ < 1 - 1 / ‖z‖ := by
    rw [lt_sub_iff_add_lt, ← add_div, show (2 : ℝ) + 1 = 3 by norm_num]
    exact (div_lt_one hz0).mpr hz
  linarith [hlb, hcb, hlog, hkey]

/-- In the escape regime the orbit never drops below the start: `‖z‖ ≤ ‖f_c^[n] z‖`. -/
theorem norm_le_orbit {c z : ℂ} (hc : ‖c‖ ≤ ‖z‖) (hz : 2 < ‖z‖) (n : ℕ) :
    ‖z‖ ≤ ‖(quadratic c)^[n] z‖ := by
  have hge1 : (1 : ℝ) ≤ (‖z‖ - 1) ^ n := one_le_pow₀ (by linarith)
  exact le_trans (by nlinarith [hge1, norm_nonneg z]) (quadratic_orbit_growth hc hz n)

/-- **Iterated functional equation** `G_c(f_c^[N] z) = 2^N · G_c(z)` on the escape set. -/
theorem greenLimit_iterate {c z : ℂ} (hc : ‖c‖ ≤ ‖z‖) (hz : 2 < ‖z‖) (N : ℕ) :
    greenLimit c ((quadratic c)^[N] z) = 2 ^ N * greenLimit c z := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hn := norm_le_orbit hc hz n
    rw [Function.iterate_succ', Function.comp_apply,
        greenLimit_quadratic (le_trans hc hn) (lt_of_lt_of_le hz hn), ih, pow_succ]
    ring

/-- **`G_c > 0` on the whole escape regime** (`‖z‖ > 2`, `‖c‖ ≤ ‖z‖`): the orbit grows
past radius `3`, where `G_c > 0`, and `G_c(z) = G_c(f^[N]z)/2^N > 0`. -/
theorem greenLimit_pos_escape {c z : ℂ} (hc : ‖c‖ ≤ ‖z‖) (hz : 2 < ‖z‖) :
    0 < greenLimit c z := by
  have hz0 : (0 : ℝ) < ‖z‖ := by linarith
  obtain ⟨N, hN⟩ : ∃ N, (3 : ℝ) < ‖z‖ * (‖z‖ - 1) ^ N := by
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (3 / ‖z‖) (show (1 : ℝ) < ‖z‖ - 1 by linarith)
    exact ⟨N, by rw [mul_comm]; exact (div_lt_iff₀ hz0).mp hN⟩
  have h3 : (3 : ℝ) < ‖(quadratic c)^[N] z‖ := lt_of_lt_of_le hN (quadratic_orbit_growth hc hz N)
  have hposN : 0 < greenLimit c ((quadratic c)^[N] z) :=
    greenLimit_pos (le_trans hc (norm_le_orbit hc hz N)) h3
  rw [greenLimit_iterate hc hz N] at hposN
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  exact (mul_pos_iff_of_pos_left h2N).mp hposN

/-- **Pullback representation on the basin.** For `z ∉ K_c`, some iterate `f^[N]z` is in
the escape regime and `G_c(z) = 2⁻ᴺ·G_c(f^[N]z)`. -/
theorem greenLimit_eq_pullback {c z : ℂ} (hz : z ∉ filledJulia c) :
    ∃ N, ‖c‖ ≤ ‖(quadratic c)^[N] z‖ ∧ 2 < ‖(quadratic c)^[N] z‖ ∧
      greenLimit c z = (2 ^ N : ℝ)⁻¹ * greenLimit c ((quadratic c)^[N] z) := by
  obtain ⟨N, hN⟩ := exists_orbit_gt hz (max 2 ‖c‖)
  have hN2 : 2 < ‖(quadratic c)^[N] z‖ := lt_of_le_of_lt (le_max_left _ _) hN
  have hNc : ‖c‖ ≤ ‖(quadratic c)^[N] z‖ := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hN)
  refine ⟨N, hNc, hN2, ?_⟩
  have htends : Tendsto (greenApprox c z) atTop
      (𝓝 ((2 ^ N : ℝ)⁻¹ * greenLimit c ((quadratic c)^[N] z))) := by
    rw [← tendsto_add_atTop_iff_nat N]
    have hrel : ∀ m, greenApprox c z (m + N)
        = (2 ^ N : ℝ)⁻¹ * greenApprox c ((quadratic c)^[N] z) m := by
      intro m; unfold greenApprox
      rw [Function.iterate_add_apply, pow_add]; field_simp
    simp_rw [hrel]
    exact (greenApprox_tendsto hNc hN2).const_mul _
  exact htends.limUnder_eq

/-- **The Green's function is positive exactly on the basin.** `G_c > 0` on `Ω_c = ℂ∖K_c`
(and `= 0` on `K_c`): the defining sign property of the Green's function. -/
theorem greenLimit_pos_basin {c z : ℂ} (hz : z ∉ filledJulia c) : 0 < greenLimit c z := by
  obtain ⟨N, hNc, hN2, heq⟩ := greenLimit_eq_pullback hz
  rw [heq]
  exact mul_pos (by positivity) (greenLimit_pos_escape hNc hN2)

/-- **Green-function asymptotic** `|G_c(z) − log‖z‖| ≤ 2‖c‖/‖z‖²` on the escape set.
Hence `G_c(z) = log‖z‖ + o(1)` as `z → ∞`: the Robin constant of `K_c` is `0`, so
`cap(K_c) = 1` — the bridge from the Green function to the Tier-2 capacity theory. -/
theorem greenLimit_abs_sub_log {c z : ℂ} (hc : ‖c‖ ≤ ‖z‖) (hz : 2 < ‖z‖) :
    |greenLimit c z - Real.log ‖z‖| ≤ 2 * ‖c‖ / ‖z‖ ^ 2 := by
  have hgs : ∀ n, ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ k ≤ 2 := by
    intro n
    rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
    have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n := by positivity
    rw [div_le_iff_of_neg (by norm_num : (1 / 2 : ℝ) - 1 < 0)]; nlinarith [this]
  have hpern : ∀ n, |greenApprox c z n - Real.log ‖z‖| ≤ 2 * ‖c‖ / ‖z‖ ^ 2 := by
    intro n
    have h0 : greenApprox c z 0 = Real.log ‖z‖ := by simp [greenApprox]
    have htel : greenApprox c z n - Real.log ‖z‖
        = ∑ k ∈ Finset.range n, (greenApprox c z (k + 1) - greenApprox c z k) := by
      rw [Finset.sum_range_sub (greenApprox c z) n, h0]
    rw [htel]
    calc |∑ k ∈ Finset.range n, (greenApprox c z (k + 1) - greenApprox c z k)|
        ≤ ∑ k ∈ Finset.range n, |greenApprox c z (k + 1) - greenApprox c z k| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range n, ‖c‖ / ‖z‖ ^ 2 * (1 / 2 : ℝ) ^ k :=
          Finset.sum_le_sum (fun k _ => greenApprox_step_geom_bound hc hz k)
      _ = ‖c‖ / ‖z‖ ^ 2 * ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ k := by rw [← Finset.mul_sum]
      _ ≤ ‖c‖ / ‖z‖ ^ 2 * 2 := by gcongr; exact hgs n
      _ = 2 * ‖c‖ / ‖z‖ ^ 2 := by ring
  have htends : Tendsto (fun n => |greenApprox c z n - Real.log ‖z‖|) atTop
      (𝓝 |greenLimit c z - Real.log ‖z‖|) := ((greenApprox_tendsto hc hz).sub_const _).abs
  exact le_of_tendsto htends (Filter.Eventually.of_forall hpern)

/-- The modulus of the Böttcher coordinate, `|φ_c(z)| = exp(G_c(z))`. -/
noncomputable def bottcherModulus (c z : ℂ) : ℝ := Real.exp (greenLimit c z)

/-- `|φ_c| > 1` on the basin `Ω_c` (the Böttcher coordinate maps `Ω_c` into `{|w|>1}`). -/
theorem one_lt_bottcherModulus {c z : ℂ} (hz : z ∉ filledJulia c) :
    1 < bottcherModulus c z :=
  Real.one_lt_exp_iff.mpr (greenLimit_pos_basin hz)

/-- **Böttcher functional equation, modulus form**: `|φ_c(z²+c)| = |φ_c(z)|²`. -/
theorem bottcherModulus_quadratic {c z : ℂ} (hc : ‖c‖ ≤ ‖z‖) (hz : 2 < ‖z‖) :
    bottcherModulus c (quadratic c z) = bottcherModulus c z ^ 2 := by
  unfold bottcherModulus
  rw [greenLimit_quadratic hc hz, two_mul, Real.exp_add, ← pow_two]

/-- The genuine Green's function of `Ω_c` with pole at `∞`: `0` on `K_c`, `G_c` on `Ω_c`. -/
noncomputable def greenFunctionDyn (c z : ℂ) : ℝ :=
  haveI := Classical.propDecidable (z ∈ filledJulia c)
  if z ∈ filledJulia c then 0 else greenLimit c z

/-- The Green's function is non-negative. -/
theorem greenFunctionDyn_nonneg (c z : ℂ) : 0 ≤ greenFunctionDyn c z := by
  unfold greenFunctionDyn
  by_cases h : z ∈ filledJulia c
  · rw [if_pos h]
  · rw [if_neg h]; exact (greenLimit_pos_basin h).le

/-- **`{G_c = 0} = K_c`**: the Green's function vanishes exactly on the filled Julia set.
The complete sign characterization (with `greenLimit_pos_basin`). -/
theorem greenFunctionDyn_eq_zero_iff (c z : ℂ) :
    greenFunctionDyn c z = 0 ↔ z ∈ filledJulia c := by
  unfold greenFunctionDyn
  by_cases h : z ∈ filledJulia c
  · rw [if_pos h]; exact iff_of_true rfl h
  · rw [if_neg h]
    exact ⟨fun h0 => absurd h0 (ne_of_gt (greenLimit_pos_basin h)), fun hk => absurd hk h⟩

end Bottcher
