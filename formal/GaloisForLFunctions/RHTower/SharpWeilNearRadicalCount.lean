import GaloisForLFunctions.RHTower.PlateauTrigonometricTests

/-!
# The near radical of the level-`L` Weil form has at least `(2 - η)e^{2L}` dimensions

**Theorem** (`zeta_weil_near_radical_sharp_count`, unconditional). For every `0 < η ≤ 1` and all
large `L`, the Hodge-class tests at level `L` contain a subspace `V` with
`dim V ≥ (2 - η)e^{2L}` and `‖W(f,f)‖ ≤ exp(-η²e^{2L}/(300L)) ∫|f|²` on `V`.

The constant `2` is the count of tiny eigenvalues observed numerically by Connes and Consani:
`2e^{2L}` is the Shannon number of `[-L, L] × [-T, T]` minus the number of zeros below `T`,
maximised at the Landau height `T = 2πe^{2L}`.

Construction (`sharpCount_at_level`). With `σ = η/8`, `ℓ = L - σ`, `T = 2πe^{2ℓ}`,
`Δ = πηe^{2L}/(8L)` and `N = ⌊σΔ/(8e)⌋`:

* the plateau `b = 1_{[-(ℓ+σ/2), ℓ+σ/2]} ⋆ B_{σ/4N}^{⋆N} ⋆ β_{σ/4}` is `C^∞`, equal to `1` on
  `[-ℓ, ℓ]`, supported in `[-L, L]`, and `|b̂(w)| ≤ 2e^{L/2}e^{-N}Δ/(Re w)²` for `|Re w| ≥ Δ`
  (`levelPlateau_spec`);
* the tests `b(u) Σ_{|k|≤k₀} c_k e^{ikπu/ℓ}`, `k₀ = ⌊(T - Δ)ℓ/π⌋`, are constrained to vanish at
  every zero with `|Im ρ| ≤ T` and at `±i/2`; the number of constraints is
  `≤ 2N(0,T) + O(1) = (T/π)(2ℓ - 1) + O(L²)` (`ZetaZeroCountUpperBound`);
* on the constrained space only zeros above `T` contribute to `W`, each with both factors
  `≤ ‖c‖₁ · 2e^{L/2}e^{-N}Δ/(1 + |t| - T)²` (`norm_W_trigTest_le`), while
  `∫|f|² ≥ 2ℓ‖c‖²` (`two_mul_sum_le_integral_trigTest`).

The dimension is `2e^{2ℓ} - 2Δℓ/π - O(L²) ≥ (2 - η)e^{2L}` (`sharpCount_dim_arith`), and the
ratio is `e^{O(L)}e^{-2N} ≤ exp(-η²e^{2L}/(300L))` (`sharpCount_margin_arith`).
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real
open Zeta23

namespace RHTower

noncomputable section

/-- **Far-field decay of the plateau.** If `e^{h/2}/(hΔ) ≤ e^{-1}` and `n ≥ 1`, then on the strip,
for `|Re w| ≥ Δ`: `|b̂(w)| ≤ 2e^{(A+r)/2} e^{-n} Δ/(Re w)²`. -/
theorem norm_paperFT_boxPlateau_far_le {A h r Δ : ℝ} (hA : 0 ≤ A) (hh : 0 < h) (hr : 0 < r)
    {n : ℕ} (hn : 1 ≤ n) (hΔ : 0 < Δ) (hq : Real.exp (h / 2) / (h * Δ) ≤ Real.exp (-1))
    {w : ℂ} (hw : |w.im| ≤ 1 / 2) (hwre : Δ ≤ |w.re|) :
    ‖paperFT (boxPlateau A h n r) w‖ ≤
      2 * Real.exp ((A + r) / 2) * Real.exp (-n) * Δ / w.re ^ 2 := by
  have hX : 0 < |w.re| := lt_of_lt_of_le hΔ hwre
  have hw0 : w ≠ 0 := fun h0 => by rw [h0] at hX; simp at hX
  have hXn : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
  have hn0 : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hmain := norm_paperFT_boxPlateau_le hA hh hr n hw0
  set y := |w.im| with hy
  set X := |w.re| with hXdef
  have e1 : Real.exp (A * y) ≤ Real.exp (A / 2) := Real.exp_le_exp.mpr (by nlinarith)
  have e2 : Real.exp (r * y) ≤ Real.exp (r / 2) := Real.exp_le_exp.mpr (by nlinarith)
  have e3 : Real.exp (h * y) ≤ Real.exp (h / 2) := Real.exp_le_exp.mpr (by nlinarith)
  have hratio : Real.exp (h * y) / (h * ‖w‖) ≤ Real.exp (-1) * (Δ / X) := by
    calc Real.exp (h * y) / (h * ‖w‖) ≤ Real.exp (h / 2) / (h * X) := by
          apply div_le_div₀ (Real.exp_pos _).le e3 (by positivity)
          exact mul_le_mul_of_nonneg_left hXn hh.le
      _ = Real.exp (h / 2) / (h * Δ) * (Δ / X) := by field_simp
      _ ≤ Real.exp (-1) * (Δ / X) := by gcongr
  have hΔX : Δ / X ≤ 1 := (div_le_one hX).mpr hwre
  have hΔX0 : 0 ≤ Δ / X := by positivity
  have hpow : (Real.exp (h * y) / (h * ‖w‖)) ^ n ≤ Real.exp (-n) * (Δ / X) := by
    calc (Real.exp (h * y) / (h * ‖w‖)) ^ n ≤ (Real.exp (-1) * (Δ / X)) ^ n :=
          pow_le_pow_left₀ (by positivity) hratio n
      _ = Real.exp (-1) ^ n * (Δ / X) ^ n := mul_pow _ _ _
      _ ≤ Real.exp (-n) * (Δ / X) := by
          rw [← Real.exp_nat_mul, show (n : ℝ) * -1 = -n by ring]
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          calc (Δ / X) ^ n ≤ (Δ / X) ^ 1 := pow_le_pow_of_le_one hΔX0 hΔX hn
            _ = Δ / X := pow_one _
  have hinv : 1 / ‖w‖ ≤ 1 / X := one_div_le_one_div_of_le hX hXn
  have hsq : w.re ^ 2 = X ^ 2 := (sq_abs w.re).symm
  rw [hsq]
  calc ‖paperFT (boxPlateau A h n r) w‖
      ≤ 2 * Real.exp (A * y) / ‖w‖ * (Real.exp (h * y) / (h * ‖w‖)) ^ n * Real.exp (r * y) :=
        hmain
    _ = 2 * Real.exp (A * y) * (1 / ‖w‖) * (Real.exp (h * y) / (h * ‖w‖)) ^ n *
          Real.exp (r * y) := by ring
    _ ≤ 2 * Real.exp (A / 2) * (1 / X) * (Real.exp (-n) * (Δ / X)) * Real.exp (r / 2) := by
        gcongr
    _ = 2 * Real.exp ((A + r) / 2) * Real.exp (-n) * Δ / X ^ 2 := by
        rw [show (A + r) / 2 = A / 2 + r / 2 by ring, Real.exp_add]
        field_simp

/-- Polynomials lose against `e^{2L}`. -/
theorem eventually_mul_pow_four_le_exp {K : ℝ} (hK : 0 < K) (c : ℝ) :
    ∀ᶠ L in atTop, c * (1 + L) ^ 4 ≤ K * Real.exp (2 * L) := by
  have ht : Tendsto (fun L : ℝ => Real.exp (2 * L) / (2 * L) ^ 4) atTop atTop :=
    (Real.tendsto_exp_div_pow_atTop 4).comp (tendsto_id.const_mul_atTop two_pos)
  filter_upwards [ht.eventually_ge_atTop (|c| / K), eventually_ge_atTop (1 : ℝ)] with L hL hL1
  have hpos : 0 < (2 * L) ^ 4 := by positivity
  rw [div_le_div_iff₀ hK hpos] at hL
  have h1 : (1 + L) ^ 4 ≤ (2 * L) ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
  have h2 : c * (1 + L) ^ 4 ≤ |c| * (2 * L) ^ 4 :=
    (mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)).trans
      (mul_le_mul_of_nonneg_left h1 (abs_nonneg c))
  linarith

/-! ## The two counts -/

theorem log_two_pi_lt_two : Real.log (2 * π) < 2 := by
  rw [Real.log_lt_iff_lt_exp (by positivity)]
  have h1 := Real.pi_lt_d2
  have h2 : (7 : ℝ) < Real.exp 2 := by
    have := Real.add_one_le_exp (1 : ℝ)
    have h3 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have := Real.exp_one_gt_d9
    nlinarith
  linarith

/-- **Dimension arithmetic.** With `ℓ = L - η/8`, `T = 2πe^{2ℓ}`, `Δ = πηe^{2L}/(8L)` and
`k > (T - Δ)ℓ/π - 1`: `2k - 1 - (2(F(T) + C log²T) + c₀) ≥ (2 - η)e^{2L}`. -/
theorem sharpCount_dim_arith {η L ℓ T Δ k CR c₀ : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) (hL : 1 ≤ L)
    (hℓ : ℓ = L - η / 8) (hT : T = 2 * π * Real.exp (2 * ℓ))
    (hΔ : Δ = π * η * Real.exp (2 * L) / (8 * L)) (hk : (T - Δ) * ℓ / π - 1 < k)
    (hCR : 0 ≤ CR)
    (hC1 : 3 + c₀ + 2 * CR * (2 + 2 * L) ^ 2 ≤ η / 4 * Real.exp (2 * L)) :
    (2 - η) * Real.exp (2 * L) ≤
      2 * k - 1 - (2 * (zeroCountMain T + CR * Real.log T ^ 2) + c₀) := by
  have hpi := Real.pi_pos
  have hℓpos : 0 < ℓ := by rw [hℓ]; linarith
  have hlogT : Real.log (T / (2 * π)) = 2 * ℓ := by
    rw [hT, show 2 * π * Real.exp (2 * ℓ) / (2 * π) = Real.exp (2 * ℓ) by field_simp,
      Real.log_exp]
  have hF : zeroCountMain T = Real.exp (2 * ℓ) * (2 * ℓ - 1) := by
    unfold zeroCountMain; rw [hlogT, hT]; field_simp
  have hlogT' : Real.log T = Real.log (2 * π) + 2 * ℓ := by
    rw [hT, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
  have hlog2pi := log_two_pi_lt_two
  have hlog2pi0 : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have hlogle : Real.log T ^ 2 ≤ (2 + 2 * L) ^ 2 := by
    have h0 : 0 ≤ Real.log T := by rw [hlogT']; linarith
    have h1 : Real.log T ≤ 2 + 2 * L := by rw [hlogT', hℓ]; linarith
    exact pow_le_pow_left₀ h0 h1 2
  have hE : Real.exp (2 * L) * (1 - η / 4) ≤ Real.exp (2 * ℓ) := by
    have := Real.add_one_le_exp (-(η / 4))
    rw [show 2 * ℓ = 2 * L + (-(η / 4)) by rw [hℓ]; ring, Real.exp_add]
    have hpos := Real.exp_pos (2 * L)
    nlinarith
  have hΔℓ : 2 * Δ * ℓ / π ≤ η / 4 * Real.exp (2 * L) := by
    rw [hΔ]
    have hℓL : ℓ ≤ L := by rw [hℓ]; linarith
    have hEpos := Real.exp_pos (2 * L)
    rw [div_le_iff₀ hpi]
    have : 2 * (π * η * Real.exp (2 * L) / (8 * L)) * ℓ =
        π * η * Real.exp (2 * L) * ℓ / (4 * L) := by field_simp; ring
    rw [this, div_le_iff₀ (by positivity)]
    have : π * η * Real.exp (2 * L) * ℓ ≤ π * η * Real.exp (2 * L) * L :=
      mul_le_mul_of_nonneg_left hℓL (by positivity)
    nlinarith
  have hkT : 2 * k ≥ 2 * ((T - Δ) * ℓ / π) - 2 := by linarith
  have hTℓ : 2 * (T * ℓ / π) = 4 * ℓ * Real.exp (2 * ℓ) := by rw [hT]; field_simp; ring
  have hsplit : 2 * ((T - Δ) * ℓ / π) = 2 * (T * ℓ / π) - 2 * Δ * ℓ / π := by ring
  have hCRl : CR * Real.log T ^ 2 ≤ CR * (2 + 2 * L) ^ 2 := mul_le_mul_of_nonneg_left hlogle hCR
  rw [hF]
  nlinarith

theorem pi_div_e_margin : 13 / 3000 ≤ π / (256 * Real.exp 1) := by
  have h1 := Real.pi_gt_d4
  have h2 := Real.exp_one_lt_d9
  have he := Real.exp_pos 1
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  nlinarith

/-- **Margin arithmetic.** With `N > ηΔ/(64e) - 1`, `k ≤ (T - Δ)ℓ/π` and `A + r ≤ L`:
`(2k+1)(2e^{(A+r)/2}e^{-N}Δ)² · 48A₀ log(T+3)/(2ℓ) ≤ exp(-η²e^{2L}/(300L))`. -/
theorem sharpCount_margin_arith {η L ℓ T Δ k N A₀ A r : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hL : 1 ≤ L) (hℓ : ℓ = L - η / 8) (hT : T = 2 * π * Real.exp (2 * ℓ))
    (hΔ : Δ = π * η * Real.exp (2 * L) / (8 * L)) (hk : k ≤ (T - Δ) * ℓ / π)
    (hN : η / 8 * Δ / (8 * Real.exp 1) - 1 < N) (hAr : A + r ≤ L) (hA₀ : 1 ≤ A₀)
    (hC2 : Real.log (960 * A₀ * L * (3 + 2 * L)) + 7 * L + 2 ≤
      η ^ 2 * Real.exp (2 * L) / (1000 * L)) :
    (2 * k + 1) * (2 * Real.exp ((A + r) / 2) * Real.exp (-N) * Δ) ^ 2 *
        (48 * A₀ * Real.log (T + 3)) / (2 * ℓ) ≤
      Real.exp (-(η ^ 2 * Real.exp (2 * L) / (300 * L))) := by
  have hpi := Real.pi_pos
  have hpi4 := Real.pi_lt_d2
  have hE := Real.exp_pos (2 * L)
  have hE1 : 1 ≤ Real.exp (2 * L) := Real.one_le_exp (by linarith)
  have hℓpos : 7 / 8 ≤ ℓ := by rw [hℓ]; linarith
  have hℓL : ℓ ≤ L := by rw [hℓ]; linarith
  have hΔ0 : 0 ≤ Δ := by rw [hΔ]; positivity
  have hΔle : Δ ≤ Real.exp (2 * L) := by
    rw [hΔ, div_le_iff₀ (by positivity)]
    have : π * η ≤ 8 * L := by nlinarith
    nlinarith
  have hTle : T ≤ 2 * π * Real.exp (2 * L) := by
    rw [hT]; gcongr
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  have hk2 : 2 * k + 1 ≤ 5 * L * Real.exp (2 * L) := by
    have h1 : k ≤ T * ℓ / π := by
      refine hk.trans ?_
      apply div_le_div_of_nonneg_right _ hpi.le
      nlinarith
    have h2 : T * ℓ / π ≤ 2 * L * Real.exp (2 * L) := by
      rw [div_le_iff₀ hpi]
      have : T * ℓ ≤ (2 * π * Real.exp (2 * L)) * L :=
        mul_le_mul hTle hℓL (by linarith) (by positivity)
      nlinarith
    nlinarith
  have hlog : Real.log (T + 3) ≤ 3 + 2 * L := by
    have h1 : T + 3 ≤ 10 * Real.exp (2 * L) := by nlinarith
    have h2 : Real.log (T + 3) ≤ Real.log (10 * Real.exp (2 * L)) :=
      Real.log_le_log (by linarith) h1
    rw [Real.log_mul (by norm_num) hE.ne', Real.log_exp] at h2
    have h3 : Real.log 10 < 3 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have := Real.exp_one_gt_d9
      have h4 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add, ← Real.exp_add]; norm_num
      nlinarith
    linarith
  have hlog0 : 0 ≤ Real.log (T + 3) := Real.log_nonneg (by linarith)
  have hB : (2 * Real.exp ((A + r) / 2) * Real.exp (-N) * Δ) ^ 2 ≤
      4 * Real.exp L * Real.exp (-(2 * N)) * Real.exp (2 * L) ^ 2 := by
    have e1 : (2 * Real.exp ((A + r) / 2) * Real.exp (-N) * Δ) ^ 2 =
        4 * Real.exp (A + r) * Real.exp (-(2 * N)) * Δ ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
      push_cast; ring_nf
    rw [e1]
    have : Real.exp (A + r) ≤ Real.exp L := Real.exp_le_exp.mpr hAr
    gcongr
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = 960 * A₀ * L * (3 + 2 * L) := ⟨_, rfl⟩
  have hQpos : 0 < Q := by rw [hQ]; positivity
  have hmain : (2 * k + 1) * (2 * Real.exp ((A + r) / 2) * Real.exp (-N) * Δ) ^ 2 *
      (48 * A₀ * Real.log (T + 3)) / (2 * ℓ) ≤
      Q * Real.exp (7 * L) * Real.exp (-(2 * N)) := by
    rw [div_le_iff₀ (by linarith)]
    have hA0 : 0 ≤ A₀ := by linarith
    have h1 : (2 * k + 1) * (2 * Real.exp ((A + r) / 2) * Real.exp (-N) * Δ) ^ 2 *
        (48 * A₀ * Real.log (T + 3)) ≤ (5 * L * Real.exp (2 * L)) *
          (4 * Real.exp L * Real.exp (-(2 * N)) * Real.exp (2 * L) ^ 2) *
          (48 * A₀ * (3 + 2 * L)) := by
      gcongr
    have h7 : Real.exp (7 * L) = Real.exp (2 * L) * Real.exp L * Real.exp (2 * L) ^ 2 := by
      rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
    have h2 : (5 * L * Real.exp (2 * L)) *
          (4 * Real.exp L * Real.exp (-(2 * N)) * Real.exp (2 * L) ^ 2) *
          (48 * A₀ * (3 + 2 * L)) = Q * Real.exp (7 * L) * Real.exp (-(2 * N)) := by
      rw [h7, hQ]; ring
    have h3 : Q * Real.exp (7 * L) * Real.exp (-(2 * N)) ≤
        Q * Real.exp (7 * L) * Real.exp (-(2 * N)) * (2 * ℓ) := by
      have : 0 ≤ Q * Real.exp (7 * L) * Real.exp (-(2 * N)) := by positivity
      nlinarith
    linarith
  refine hmain.trans ?_
  have hexp : Q * Real.exp (7 * L) * Real.exp (-(2 * N)) =
      Real.exp (Real.log Q + 7 * L - 2 * N) := by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_add, Real.exp_log hQpos]
  rw [hexp]
  apply Real.exp_le_exp.mpr
  have hNΔ : 2 * N > π * η ^ 2 * Real.exp (2 * L) / (256 * Real.exp 1 * L) - 2 := by
    have e : η / 8 * Δ / (8 * Real.exp 1) =
        π * η ^ 2 * Real.exp (2 * L) / (512 * Real.exp 1 * L) := by
      rw [hΔ]; field_simp; ring
    rw [e] at hN
    have e2 : π * η ^ 2 * Real.exp (2 * L) / (256 * Real.exp 1 * L) =
        2 * (π * η ^ 2 * Real.exp (2 * L) / (512 * Real.exp 1 * L)) := by
      field_simp; ring
    rw [e2]; linarith
  have hmarg := pi_div_e_margin
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = η ^ 2 * Real.exp (2 * L) / L := ⟨_, rfl⟩
  have hG0 : 0 ≤ G := by rw [hG]; positivity
  have e3 : π * η ^ 2 * Real.exp (2 * L) / (256 * Real.exp 1 * L) = π / (256 * Real.exp 1) * G := by
    rw [hG]; field_simp
  have e4 : η ^ 2 * Real.exp (2 * L) / (1000 * L) = G / 1000 := by rw [hG]; field_simp
  have e5 : η ^ 2 * Real.exp (2 * L) / (300 * L) = G / 300 := by rw [hG]; field_simp
  rw [e3] at hNΔ; rw [e4] at hC2; rw [e5]
  rw [← hQ] at hC2
  have : 13 / 3000 * G ≤ π / (256 * Real.exp 1) * G := mul_le_mul_of_nonneg_right hmarg hG0
  linarith

/-! ## The plateau at level `L` -/

/-- The plateau used at level `L` and its properties: with `σ = η/8`, `ℓ = L - σ`,
`N = ⌊σΔ/(8e)⌋`, `h = σ/(4N)`, the plateau `b = boxPlateau (ℓ + σ/2) h N (σ/4)` is `C²`, equal to
`1` on `[-ℓ, ℓ]`, zero for `|u| ≥ L`, and `|b̂(w)| ≤ 2e^{(A+r)/2}e^{-N}Δ/(Re w)²` for
`|Re w| ≥ Δ` in the strip. -/
theorem levelPlateau_spec {η L Δ : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) (hL : 1 ≤ L) (hΔ0 : 0 < Δ)
    {N : ℕ} (hN1 : 1 ≤ N) (hNle : (N : ℝ) ≤ η / 8 * Δ / (8 * Real.exp 1)) :
    ContDiff ℝ 2 (boxPlateau (L - η / 8 + η / 8 / 2) (η / 8 / (4 * N)) N (η / 8 / 4)) ∧
    (∀ u, |u| ≤ L - η / 8 →
      boxPlateau (L - η / 8 + η / 8 / 2) (η / 8 / (4 * N)) N (η / 8 / 4) u = 1) ∧
    (∀ u, L ≤ |u| →
      boxPlateau (L - η / 8 + η / 8 / 2) (η / 8 / (4 * N)) N (η / 8 / 4) u = 0) ∧
    Integrable (boxPlateau (L - η / 8 + η / 8 / 2) (η / 8 / (4 * N)) N (η / 8 / 4)) ∧
    ∀ w : ℂ, |w.im| ≤ 1 / 2 → Δ ≤ |w.re| →
      ‖paperFT (boxPlateau (L - η / 8 + η / 8 / 2) (η / 8 / (4 * N)) N (η / 8 / 4)) w‖ ≤
        2 * Real.exp ((L - η / 8 + η / 8 / 2 + η / 8 / 4) / 2) * Real.exp (-N) * Δ / w.re ^ 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hσ : 0 < η / 8 := by positivity
  have hh : 0 < η / 8 / (4 * N) := by positivity
  have hr : 0 < η / 8 / 4 := by positivity
  have hA : 0 ≤ L - η / 8 + η / 8 / 2 := by linarith
  have hNh : (N : ℝ) * (η / 8 / (4 * N)) = η / 8 / 4 := by field_simp
  have hC : ContDiff ℝ 2 (boxPlateau (L - η / 8 + η / 8 / 2) (η / 8 / (4 * N)) N (η / 8 / 4)) :=
    contDiff_boxPlateau hr N
  have h0 : ∀ u, L ≤ |u| →
      boxPlateau (L - η / 8 + η / 8 / 2) (η / 8 / (4 * N)) N (η / 8 / 4) u = 0 := by
    intro u hu
    exact boxPlateau_eq_zero hh hr N (by rw [hNh]; linarith)
  refine ⟨hC, fun u hu => boxPlateau_eq_one hh hr N (by rw [hNh]; linarith), h0, ?_, ?_⟩
  · refine (hC.continuous).integrable_of_hasCompactSupport ?_
    exact hasCompactSupport_of_support_subset_abs (Λ := L) fun u hu => by
      by_contra hc; push Not at hc; exact hu (h0 u hc.le)
  · intro w hw hwre
    refine norm_paperFT_boxPlateau_far_le hA hh hr hN1 hΔ0 ?_ hw hwre
    have he := Real.exp_pos 1
    have hhΔ : 2 * Real.exp 1 ≤ η / 8 / (4 * N) * Δ := by
      have : (N : ℝ) * (8 * Real.exp 1) ≤ η / 8 * Δ := by
        rw [le_div_iff₀ (by positivity)] at hNle; linarith
      rw [show η / 8 / (4 * N) * Δ = (η / 8 * Δ) / (4 * N) by ring, le_div_iff₀ (by positivity)]
      nlinarith
    have hexp2 : Real.exp (η / 8 / (4 * N) / 2) ≤ 2 := by
      have hsmall : η / 8 / (4 * N) / 2 ≤ Real.log 2 := by
        have h1 : η / 8 / (4 * N) ≤ 1 / 32 := by
          rw [div_le_iff₀ (by positivity)]; nlinarith
        have := Real.log_two_gt_d9
        linarith
      calc Real.exp (η / 8 / (4 * N) / 2) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hsmall
        _ = 2 := Real.exp_log (by norm_num)
    rw [div_le_iff₀ (by positivity)]
    have hinv : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; norm_num
    calc Real.exp (η / 8 / (4 * N) / 2) ≤ 2 := hexp2
      _ = Real.exp (-1) * (2 * Real.exp 1) := by linear_combination (-2) * hinv
      _ ≤ Real.exp (-1) * (η / 8 / (4 * N) * Δ) := by gcongr

/-! ## The near radical at level `L` -/

/-- The constraint map: the values of `f̂_c` at the low zeros and at `±i/2`. -/
def lowZeroConstraint (b : ℝ → ℂ) (ℓ T : ℝ) (k₀ : ℕ) [Fintype (lowZeros T)] :
    (Fin (2 * k₀ + 1) → ℂ) →ₗ[ℂ] ((lowZeros T → ℂ) × (ℂ × ℂ)) where
  toFun c := (fun ρ => ∑ j, c j * paperFT b (gammaOf (ρ : ℂ) + trigFreq ℓ k₀ j),
    ∑ j, c j * paperFT b (I / 2 + trigFreq ℓ k₀ j),
    ∑ j, c j * paperFT b (-(I / 2) + trigFreq ℓ k₀ j))
  map_add' c d := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, Prod.mk_add_mk]; rfl
  map_smul' a c := by
    ext ρ <;> simp [Finset.mul_sum, mul_assoc]

/-- **The near radical at a fixed level.** Under the explicit size conditions `(C1)–(C5)` on `L`,
the Hodge-class tests at level `L` contain a subspace of dimension `≥ (2 - η)e^{2L}` on which
`‖W(f,f)‖ ≤ exp(-η²e^{2L}/(300L)) ∫|f|²`. -/
theorem sharpCount_at_level {η L A₀ CR T₁ : ℝ} {c₀ : ℕ} (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hL : 1 ≤ L) (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (zetaZeroConfig.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    (hCR : 0 ≤ CR) (hcount : ∀ T : ℝ, T₁ ≤ T →
      (zetaZeroConfig.N 0 T : ℝ) ≤ zeroCountMain T + CR * Real.log T ^ 2)
    (hlow : ∀ T : ℝ, 0 ≤ T → (lowZeros T).ncard ≤ 2 * zetaZeroConfig.N 0 T + c₀)
    (hC1 : 3 + c₀ + 2 * CR * (2 + 2 * L) ^ 2 ≤ η / 4 * Real.exp (2 * L))
    (hC2 : Real.log (960 * A₀ * L * (3 + 2 * L)) + 7 * L + 2 ≤
      η ^ 2 * Real.exp (2 * L) / (1000 * L))
    (hC3 : 1 ≤ π * η ^ 2 * Real.exp (2 * L) / (512 * Real.exp 1 * L))
    (hC4 : 1 ≤ π * η * Real.exp (2 * L) / (8 * L))
    (hC5 : T₁ ≤ 2 * π * Real.exp (2 * (L - η / 8))) :
    ∃ V : Submodule ℂ (ℝ → ℂ), FiniteDimensional ℂ V ∧
      (2 - η) * Real.exp (2 * L) ≤ (Module.finrank ℂ V : ℝ) ∧
      (∀ f ∈ V, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-L) L ∧ paperFT f (I / 2) = 0 ∧
        paperFT f (-(I / 2)) = 0) ∧
      ∀ f ∈ V, ‖zetaZeroConfig.W f f‖ ≤
        Real.exp (-(η ^ 2 * Real.exp (2 * L) / (300 * L))) * ∫ u, ‖f u‖ ^ 2 := by
  have hpi := Real.pi_pos
  have he := Real.exp_pos 1
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = L - η / 8 := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = 2 * π * Real.exp (2 * ℓ) := ⟨_, rfl⟩
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : ℝ, Δ = π * η * Real.exp (2 * L) / (8 * L) := ⟨_, rfl⟩
  have hℓpos : 0 < ℓ := by rw [hℓ]; linarith
  have hΔ1 : 1 ≤ Δ := by rw [hΔ]; exact hC4
  have hΔ0 : 0 < Δ := by linarith
  -- the number of box smoothings
  have hNeq : η / 8 * Δ / (8 * Real.exp 1) =
      π * η ^ 2 * Real.exp (2 * L) / (512 * Real.exp 1 * L) := by
    rw [hΔ]; field_simp; ring
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = ⌊η / 8 * Δ / (8 * Real.exp 1)⌋₊ := ⟨_, rfl⟩
  have hN1 : 1 ≤ N := by
    rw [hNdef]; exact Nat.le_floor (by rw [hNeq]; exact_mod_cast hC3)
  have hNle : (N : ℝ) ≤ η / 8 * Δ / (8 * Real.exp 1) := by
    rw [hNdef]; exact Nat.floor_le (by positivity)
  have hNgt : η / 8 * Δ / (8 * Real.exp 1) - 1 < N := by
    have := Nat.lt_floor_add_one (η / 8 * Δ / (8 * Real.exp 1)); rw [← hNdef] at this; linarith
  -- the plateau
  obtain ⟨hbC, hb1, hb0, hbint, hdec⟩ := levelPlateau_spec hη0 hη1 hL hΔ0 hN1 hNle
  set b := boxPlateau (L - η / 8 + η / 8 / 2) (η / 8 / (4 * N)) N (η / 8 / 4) with hbdef
  rw [← hℓ] at hb1
  have hbs : ∀ u, L < |u| → b u = 0 := fun u hu => hb0 u hu.le
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ,
      B = 2 * Real.exp ((L - η / 8 + η / 8 / 2 + η / 8 / 4) / 2) * Real.exp (-N) * Δ := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hdec' : ∀ w : ℂ, |w.im| ≤ 1 / 2 → Δ ≤ |w.re| → ‖paperFT b w‖ ≤ B / w.re ^ 2 :=
    fun w h1 h2 => by rw [hBdef]; exact hdec w h1 h2
  -- the frequencies
  have hTΔ : Δ ≤ T := by
    have hE := Real.exp_pos (2 * L)
    have h1 : Real.exp (2 * L) / 2 ≤ Real.exp (2 * ℓ) := by
      have := Real.add_one_le_exp (-(η / 4))
      rw [hℓ, show 2 * (L - η / 8) = 2 * L + (-(η / 4)) by ring, Real.exp_add]
      nlinarith
    have h2 : Δ ≤ π * Real.exp (2 * L) / 8 := by
      rw [hΔ, div_le_div_iff₀ (by positivity) (by norm_num)]
      have : π * η * Real.exp (2 * L) ≤ π * Real.exp (2 * L) * L := by
        have := mul_le_mul_of_nonneg_left (show η ≤ L by linarith)
          (by positivity : (0 : ℝ) ≤ π * Real.exp (2 * L))
        linarith
      linarith
    have h3 : π * Real.exp (2 * L) ≤ T := by
      rw [hT]
      have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * π)
      linarith
    have : 0 ≤ π * Real.exp (2 * L) := by positivity
    linarith
  obtain ⟨k₀, hk₀def⟩ : ∃ k₀ : ℕ, k₀ = ⌊(T - Δ) * ℓ / π⌋₊ := ⟨_, rfl⟩
  have hk₀le : (k₀ : ℝ) ≤ (T - Δ) * ℓ / π := by
    have hTΔ' : 0 ≤ T - Δ := by linarith
    rw [hk₀def]; exact Nat.floor_le (by positivity)
  have hk₀gt : (T - Δ) * ℓ / π - 1 < k₀ := by
    have := Nat.lt_floor_add_one ((T - Δ) * ℓ / π); rw [← hk₀def] at this; linarith
  have hΩ : k₀ * π / ℓ + Δ ≤ T := by
    have : (k₀ : ℝ) * π / ℓ ≤ T - Δ := by
      rw [div_le_iff₀ hℓpos]
      rw [le_div_iff₀ hpi] at hk₀le; linarith
    linarith
  -- the constraint map and the subspace
  haveI : Fintype (lowZeros T) := (lowZeros_finite T).fintype
  set Λ := lowZeroConstraint b ℓ T k₀ with hΛdef
  have hΛ : ∀ c, Λ c = (fun ρ : lowZeros T => paperFT (trigTest b ℓ k₀ c) (gammaOf (ρ : ℂ)),
      paperFT (trigTest b ℓ k₀ c) (I / 2), paperFT (trigTest b ℓ k₀ c) (-(I / 2))) := by
    intro c
    simp only [hΛdef, lowZeroConstraint, LinearMap.coe_mk, AddHom.coe_mk,
      paperFT_trigTest hbint hbs]
  set Φ := trigTestMap b ℓ k₀ with hΦdef
  have hΦinj : Function.Injective Φ :=
    trigTestMap_injective hℓpos hbC.continuous hbs hb1 k₀
  refine ⟨(LinearMap.ker Λ).map Φ, inferInstance, ?_, ?_, ?_⟩
  · -- dimension count
    have hequiv := Submodule.equivMapOfInjective Φ hΦinj (LinearMap.ker Λ)
    rw [← hequiv.finrank_eq]
    have hrn := LinearMap.finrank_range_add_finrank_ker Λ
    have hcod : Module.finrank ℂ ((lowZeros T → ℂ) × (ℂ × ℂ)) = (lowZeros T).ncard + 2 := by
      rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
        Module.finrank_self, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    have hrange : Module.finrank ℂ (LinearMap.range Λ) ≤ (lowZeros T).ncard + 2 := by
      rw [← hcod]; exact Submodule.finrank_le _
    have hdim : Module.finrank ℂ (Fin (2 * k₀ + 1) → ℂ) = 2 * k₀ + 1 := by simp
    rw [hdim] at hrn
    have hker : ((2 * k₀ + 1 : ℕ) : ℝ) - ((lowZeros T).ncard + 2 : ℕ) ≤
        (Module.finrank ℂ (LinearMap.ker Λ) : ℝ) := by
      have : 2 * k₀ + 1 ≤ (lowZeros T).ncard + 2 + Module.finrank ℂ (LinearMap.ker Λ) := by
        omega
      have h' : ((2 * k₀ + 1 : ℕ) : ℝ) ≤ ((lowZeros T).ncard + 2 : ℕ) +
          (Module.finrank ℂ (LinearMap.ker Λ) : ℝ) := by exact_mod_cast this
      linarith
    have hT0 : 0 ≤ T := by rw [hT]; positivity
    have hlowT := hlow T hT0
    have hTT₁ : T₁ ≤ T := by rw [hT, hℓ]; exact hC5
    have hcnt := hcount T hTT₁
    have hlowR : ((lowZeros T).ncard : ℝ) ≤
        2 * (zeroCountMain T + CR * Real.log T ^ 2) + c₀ := by
      have : ((lowZeros T).ncard : ℝ) ≤ 2 * (zetaZeroConfig.N 0 T : ℝ) + c₀ := by
        exact_mod_cast hlowT
      linarith
    have harith := sharpCount_dim_arith (k := (k₀ : ℝ)) (c₀ := (c₀ : ℝ)) hη0 hη1 hL hℓ hT hΔ
      hk₀gt hCR (by exact_mod_cast hC1)
    push_cast at hker
    linarith
  · rintro f ⟨c, hc, rfl⟩
    have hΛc : Λ c = 0 := hc
    rw [hΛ] at hΛc
    obtain ⟨-, h23⟩ := Prod.mk_eq_zero.mp hΛc
    obtain ⟨h2, h3⟩ := Prod.mk_eq_zero.mp h23
    exact ⟨contDiff_trigTest hbC ℓ k₀ c, tsupport_trigTest hb0 ℓ k₀ c, h2, h3⟩
  · rintro f ⟨c, hc, rfl⟩
    have hΛc : Λ c = 0 := hc
    rw [hΛ] at hΛc
    have hzero : ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.im| ≤ T →
        paperFT (trigTest b ℓ k₀ c) (gammaOf ρ) = 0 := by
      intro ρ hρ hρT
      have h1 := congrFun (Prod.mk_eq_zero.mp hΛc).1 ⟨ρ, hρ, hρT⟩
      simpa using h1
    have hW := norm_W_trigTest_le hA₀ hloc hbint hbs hℓpos hΩ hΔ1 hB0 hdec' c hzero
    have hbulk := two_mul_sum_le_integral_trigTest hℓpos hbC.continuous hbs hb1 k₀ c
    have hCS : (∑ j, ‖c j‖) ^ 2 ≤ (2 * k₀ + 1 : ℝ) * ∑ j, ‖c j‖ ^ 2 := by
      have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin (2 * k₀ + 1))))
        (f := fun j => ‖c j‖)
      rw [Finset.card_univ, Fintype.card_fin] at h
      have e : (((2 * k₀ + 1 : ℕ) : ℝ)) = 2 * k₀ + 1 := by push_cast; ring
      rw [e] at h
      exact h
    have hAr : L - η / 8 + η / 8 / 2 + η / 8 / 4 ≤ L := by linarith
    have hmarg := sharpCount_margin_arith (η := η) (L := L) (ℓ := ℓ) (T := T) (Δ := Δ)
      (k := (k₀ : ℝ)) (N := (N : ℝ)) (A₀ := A₀)
      (A := L - η / 8 + η / 8 / 2) (r := η / 8 / 4) hη0 hη1 hL hℓ hT hΔ hk₀le hNgt
      hAr hA₀ hC2
    have hmarg' : (2 * k₀ + 1 : ℝ) * B ^ 2 * (48 * A₀ * Real.log (T + 3)) / (2 * ℓ) ≤
        Real.exp (-(η ^ 2 * Real.exp (2 * L) / (300 * L))) := by
      rw [hBdef]; exact hmarg
    set I₂ := ∫ u, ‖trigTest b ℓ k₀ c u‖ ^ 2 with hI₂
    have hI0 : 0 ≤ I₂ := integral_nonneg fun _ => by positivity
    have hS0 : 0 ≤ ∑ j, ‖c j‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    have hlogT0 : 0 ≤ 48 * A₀ * Real.log (T + 3) := by
      have : 0 ≤ Real.log (T + 3) := Real.log_nonneg (by rw [hT]; have := Real.exp_pos (2 * ℓ); nlinarith)
      have : 0 ≤ A₀ := by linarith
      positivity
    show ‖zetaZeroConfig.W (Φ c) (Φ c)‖ ≤ _
    have hΦc : Φ c = trigTest b ℓ k₀ c := rfl
    rw [hΦc]
    calc ‖zetaZeroConfig.W (trigTest b ℓ k₀ c) (trigTest b ℓ k₀ c)‖
        ≤ ((∑ j, ‖c j‖) * B) ^ 2 * (48 * A₀ * Real.log (T + 3)) := hW
      _ = (∑ j, ‖c j‖) ^ 2 * B ^ 2 * (48 * A₀ * Real.log (T + 3)) := by ring
      _ ≤ ((2 * k₀ + 1 : ℝ) * ∑ j, ‖c j‖ ^ 2) * B ^ 2 * (48 * A₀ * Real.log (T + 3)) := by
          gcongr
      _ ≤ ((2 * k₀ + 1 : ℝ) * (I₂ / (2 * ℓ))) * B ^ 2 * (48 * A₀ * Real.log (T + 3)) := by
          have hS' : ∑ j, ‖c j‖ ^ 2 ≤ I₂ / (2 * ℓ) := by
            rw [le_div_iff₀ (by positivity)]; linarith
          have hk0 : (0 : ℝ) ≤ 2 * k₀ + 1 := by positivity
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hS' hk0) (sq_nonneg B)) hlogT0
      _ = ((2 * k₀ + 1 : ℝ) * B ^ 2 * (48 * A₀ * Real.log (T + 3)) / (2 * ℓ)) * I₂ := by
          ring
      _ ≤ Real.exp (-(η ^ 2 * Real.exp (2 * L) / (300 * L))) * I₂ :=
          mul_le_mul_of_nonneg_right hmarg' hI0

/-! ## The size conditions for large `L` -/

theorem sharpCount_cond1 {η L CR c : ℝ} (hL : 1 ≤ L) (hCR : 0 ≤ CR) (hc : 0 ≤ c)
    (h : (3 + c + 8 * CR) * (1 + L) ^ 4 ≤ η / 4 * Real.exp (2 * L)) :
    3 + c + 2 * CR * (2 + 2 * L) ^ 2 ≤ η / 4 * Real.exp (2 * L) := by
  have hp1 : 1 ≤ (1 + L) ^ 4 := one_le_pow₀ (by linarith)
  have hp2 : (1 + L) ^ 2 ≤ (1 + L) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have e : 2 * CR * (2 + 2 * L) ^ 2 = 8 * CR * (1 + L) ^ 2 := by ring
  have h8 : 8 * CR * (1 + L) ^ 2 ≤ 8 * CR * (1 + L) ^ 4 :=
    mul_le_mul_of_nonneg_left hp2 (by linarith)
  have h3 : 3 + c ≤ (3 + c) * (1 + L) ^ 4 := by nlinarith
  rw [e]; nlinarith

theorem sharpCount_cond2 {η L A₀ : ℝ} (hL : 1 ≤ L) (hA₀ : 1 ≤ A₀)
    (h : 1000 * (4800 * A₀ + 12) * (1 + L) ^ 4 ≤ η ^ 2 * Real.exp (2 * L)) :
    Real.log (960 * A₀ * L * (3 + 2 * L)) + 7 * L + 2 ≤
      η ^ 2 * Real.exp (2 * L) / (1000 * L) := by
  have hA0 : 0 ≤ A₀ := by linarith
  rw [le_div_iff₀ (by positivity)]
  have hlog : Real.log (960 * A₀ * L * (3 + 2 * L)) ≤ 960 * A₀ * L * (3 + 2 * L) := by
    have := Real.log_le_sub_one_of_pos (x := 960 * A₀ * L * (3 + 2 * L)) (by positivity)
    linarith
  have hp4 : L * L * L ≤ (1 + L) ^ 4 := by nlinarith
  have hp5 : L * L ≤ (1 + L) ^ 4 := by nlinarith
  have h' : 960 * A₀ * L * (3 + 2 * L) * L ≤ 4800 * A₀ * (L * L * L) := by
    have h5 : 3 + 2 * L ≤ 5 * L := by linarith
    have := mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ 960 * A₀ * L * L)
    nlinarith
  have h'' : (7 * L + 2) * L ≤ 9 * (L * L) := by nlinarith
  have hA : 4800 * A₀ * (L * L * L) ≤ 4800 * A₀ * (1 + L) ^ 4 :=
    mul_le_mul_of_nonneg_left hp4 (by positivity)
  have hpoly : (960 * A₀ * L * (3 + 2 * L) + 7 * L + 2) * (1000 * L) ≤
      1000 * (4800 * A₀ + 12) * (1 + L) ^ 4 := by nlinarith
  have hmono : (Real.log (960 * A₀ * L * (3 + 2 * L)) + 7 * L + 2) * (1000 * L) ≤
      (960 * A₀ * L * (3 + 2 * L) + 7 * L + 2) * (1000 * L) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity); linarith
  linarith

theorem sharpCount_cond3 {η L : ℝ} (hL : 1 ≤ L)
    (h : 512 * 3 * (1 + L) ^ 4 ≤ π * η ^ 2 * Real.exp (2 * L)) :
    1 ≤ π * η ^ 2 * Real.exp (2 * L) / (512 * Real.exp 1 * L) := by
  have he3 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  rw [le_div_iff₀ (by positivity), one_mul]
  have hp : L ≤ (1 + L) ^ 4 := by
    have := le_self_pow₀ (show (1 : ℝ) ≤ 1 + L by linarith) (show (4 : ℕ) ≠ 0 by norm_num)
    linarith
  have : 512 * Real.exp 1 * L ≤ 512 * 3 * (1 + L) ^ 4 := by
    have := mul_le_mul he3 hp (by linarith) (by norm_num)
    linarith
  linarith

theorem sharpCount_cond4 {η L : ℝ} (hL : 1 ≤ L)
    (h : 8 * (1 + L) ^ 4 ≤ π * η * Real.exp (2 * L)) :
    1 ≤ π * η * Real.exp (2 * L) / (8 * L) := by
  rw [le_div_iff₀ (by positivity), one_mul]
  have hp : L ≤ (1 + L) ^ 4 := by
    have := le_self_pow₀ (show (1 : ℝ) ≤ 1 + L by linarith) (show (4 : ℕ) ≠ 0 by norm_num)
    linarith
  linarith

theorem sharpCount_cond5 {η L T₁ : ℝ} (hL : 1 ≤ L) (hη1 : η ≤ 1) (hT₁ : 0 ≤ T₁)
    (h : T₁ * (1 + L) ^ 4 ≤ π * Real.exp (2 * L)) :
    T₁ ≤ 2 * π * Real.exp (2 * (L - η / 8)) := by
  have hpi := Real.pi_pos
  have hE := Real.exp_pos (2 * L)
  have hh : Real.exp (2 * L) / 2 ≤ Real.exp (2 * (L - η / 8)) := by
    have := Real.add_one_le_exp (-(η / 4))
    rw [show 2 * (L - η / 8) = 2 * L + (-(η / 4)) by ring, Real.exp_add]
    nlinarith
  have hp1 : 1 ≤ (1 + L) ^ 4 := one_le_pow₀ (by linarith)
  have h1 : T₁ ≤ T₁ * (1 + L) ^ 4 := le_mul_of_one_le_right hT₁ hp1
  have h2 := mul_le_mul_of_nonneg_left hh (by positivity : (0 : ℝ) ≤ 2 * π)
  have h3 : 2 * π * (Real.exp (2 * L) / 2) = π * Real.exp (2 * L) := by ring
  linarith

/-! ## The sharp near-radical count -/

/-- **The near radical of the level-`L` Weil form of `ζ` has at least `(2 - η)e^{2L}`
dimensions.** For every `0 < η ≤ 1` and all large `L`, the Hodge-class tests at level `L`
(`C²`, supported in `[-L, L]`, `f̂(±i/2) = 0`) contain a subspace `V` with
`dim V ≥ (2 - η)e^{2L}` and `‖W(f,f)‖ ≤ exp(-η²e^{2L}/(300L)) ∫|f|²` on `V`.

So at least `(2 - η)e^{2L}` eigenvalues of the level-`L` Weil form lie below
`exp(-η²e^{2L}/(300L))`: the constant `2` of the Connes–Consani count. The tests are
`b(u) Σ_{|k| ≤ k₀} c_k e^{ikπu/ℓ}` with a box-smoothed plateau `b`, constrained to vanish at every
zero of height `≤ T = 2πe^{2ℓ}`, `ℓ = L - η/8`. The dimension is the Shannon number
`2Tℓ/π` minus the zero count `2N(T) = (T/π)(2ℓ - 1) + O(L²)`, which is `2e^{2ℓ}`. -/
theorem zeta_weil_near_radical_sharp_count :
    ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∃ V : Submodule ℂ (ℝ → ℂ), FiniteDimensional ℂ V ∧
        (2 - η) * Real.exp (2 * L) ≤ (Module.finrank ℂ V : ℝ) ∧
        (∀ f ∈ V, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-L) L ∧ paperFT f (I / 2) = 0 ∧
          paperFT f (-(I / 2)) = 0) ∧
        ∀ f ∈ V, ‖zetaZeroConfig.W f f‖ ≤
          Real.exp (-(η ^ 2 * Real.exp (2 * L) / (300 * L))) * ∫ u, ‖f u‖ ^ 2 := by
  intro η hη0 hη1
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  obtain ⟨CR, T₁, hCR, hT₁, hcount⟩ := zeroCount_upper
  obtain ⟨c₀, hlow⟩ := ncard_lowZeros_le
  have hpi := Real.pi_pos
  have e1 := eventually_mul_pow_four_le_exp (K := η / 4) (by positivity) (3 + c₀ + 8 * CR)
  have e2 := eventually_mul_pow_four_le_exp (K := η ^ 2) (by positivity)
    (1000 * (4800 * A₀ + 12))
  have e3 := eventually_mul_pow_four_le_exp (K := π * η ^ 2) (by positivity) (512 * 3)
  have e4 := eventually_mul_pow_four_le_exp (K := π * η) (by positivity) 8
  have e5 := eventually_mul_pow_four_le_exp (K := π) hpi T₁
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.mp
    ((((((eventually_ge_atTop (1 : ℝ)).and e1).and e2).and e3).and e4).and e5)
  refine ⟨L₀, fun L hL => ?_⟩
  obtain ⟨⟨⟨⟨⟨hL1, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := hL₀ L hL
  exact sharpCount_at_level hη0 hη1 hL1 hA₀ hloc hCR hcount hlow
    (sharpCount_cond1 hL1 hCR (Nat.cast_nonneg _) h1) (sharpCount_cond2 hL1 hA₀ h2)
    (sharpCount_cond3 hL1 h3) (sharpCount_cond4 hL1 h4)
    (sharpCount_cond5 hL1 hη1 (by linarith) h5)

end

end RHTower
