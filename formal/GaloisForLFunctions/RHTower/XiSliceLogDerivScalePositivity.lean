import GaloisForLFunctions.RHTower.XiSliceLogDerivArcTail

/-!
# Slice positivity from log-derivative scale data

Let `ZetaLogDerivScaleData t R B` hold with `0 < R ≤ 1/16`, `u = log t ≥ 10⁷` and
`0 ≤ B ≤ u/10⁹`. The slice product has no zero on `R/2 < Re w < 3/2`, `|Im w| < 12R`; the Stirling
comparison holds with `C = 3 + B` on the saddle disc `|w − Rs| ≤ R/4`, `R ≤ Rs ≤ 5R`; the arc beyond
`θ₁ = 10⁻⁴` is at most `exp(−Rs log t/(2·10⁹))` (`ZetaLogDerivScaleData.norm_sliceArc_le`). The
strip saddle (`xiSliceCoeff_pos_of_saddle_strip`) then gives `c_{2k}(t) > 0` for every order `k` with
`R log t ≤ k ≤ 2R log t` and `k ≥ k₁`, an absolute constant
(`exists_xiSliceCoeff_pos_of_logDerivScaleData`).

Unlike the `|ζ|`-bound scale data, no lower bound on `k` in terms of `log log t` enters: the Stirling
constant is `3 + B` with `B ≤ (log t)/10⁹`, independent of the scale.
-/

noncomputable section

open Complex Real Metric Set
open scoped ComplexOrder

namespace RHTower

/-- The zero-free set of the slice variable: `R/2 < Re w < 3/2`, `|Im w| < 12R`. -/
def logDerivSliceSet (R : ℝ) : Set ℂ :=
  {w | R / 2 < w.re} ∩ {w | w.re < 3 / 2} ∩ {w | -(12 * R) < w.im} ∩ {w | w.im < 12 * R}

theorem isOpen_logDerivSliceSet (R : ℝ) : IsOpen (logDerivSliceSet R) := by
  unfold logDerivSliceSet
  exact (((isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)).inter
    (isOpen_lt continuous_const Complex.continuous_im)).inter
    (isOpen_lt Complex.continuous_im continuous_const)

theorem mem_logDerivSliceSet {R : ℝ} {w : ℂ} :
    w ∈ logDerivSliceSet R ↔ R / 2 < w.re ∧ w.re < 3 / 2 ∧ -(12 * R) < w.im ∧ w.im < 12 * R := by
  unfold logDerivSliceSet
  simp only [mem_inter_iff, mem_setOf_eq]
  tauto

theorem slicePoint_mem_logDerivZeroFreeBox {t R : ℝ} {w : ℂ} (hw : w ∈ logDerivSliceSet R) :
    1 / 2 + w + (t : ℂ) * I ∈ logDerivZeroFreeBox t R := by
  rw [mem_logDerivSliceSet] at hw
  unfold logDerivZeroFreeBox
  simp only [mem_inter_iff, mem_setOf_eq, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  norm_num
  exact ⟨⟨⟨by linarith, by linarith⟩, by linarith⟩, by linarith⟩

theorem conj_mem_logDerivSliceSet {R : ℝ} {w : ℂ} (hw : w ∈ logDerivSliceSet R) :
    (starRingEnd ℂ) w ∈ logDerivSliceSet R := by
  rw [mem_logDerivSliceSet] at hw ⊢
  simp only [Complex.conj_re, Complex.conj_im]
  exact ⟨hw.1, hw.2.1, by linarith, by linarith⟩

namespace ZetaLogDerivScaleData

variable {t R B : ℝ}

/-- **Zero-free slice product.** -/
theorem xiSliceProduct_ne_zero (h : ZetaLogDerivScaleData t R B) (hR : 0 < R) {w : ℂ}
    (hw : w ∈ logDerivSliceSet R) : xiSliceProduct t w ≠ 0 := by
  unfold xiSliceProduct
  have e : (1 / 2 : ℂ) - w + (t : ℂ) * I = 1 - (1 / 2 + w - (t : ℂ) * I) := by ring
  refine mul_ne_zero (h.xi_ne_zero hR (slicePoint_mem_logDerivZeroFreeBox hw)) ?_
  rw [e, xi_one_sub, ZetaScaleData.conj_slicePoint', xi_conj]
  exact (map_ne_zero _).mpr
    (h.xi_ne_zero hR (slicePoint_mem_logDerivZeroFreeBox (conj_mem_logDerivSliceSet hw)))

theorem slicePoint_mem_logDerivBox {w : ℂ} (h1 : 3 * R / 4 ≤ w.re)
    (h2 : w.re ≤ 6 * R) (h3 : |w.im| ≤ 6 * R) :
    1 / 2 + w + (t : ℂ) * I ∈ logDerivBox t R := by
  rw [mem_logDerivBox]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  norm_num
  exact ⟨by linarith, by linarith, by simpa using h3⟩

/-- **Stirling comparison for both points of the slice.** -/
theorem stirling_slice (h : ZetaLogDerivScaleData t R B) (hR : 0 < R) (hR16 : R ≤ 1 / 16)
    (ht : 8 ≤ t) {w : ℂ} (h1 : 3 * R / 4 ≤ w.re) (h2 : w.re ≤ 6 * R) (h3 : |w.im| ≤ 6 * R) :
    ‖_root_.logDeriv xi (1 / 2 + w + (t : ℂ) * I) - Complex.log ((1 / 2 + w + (t : ℂ) * I) / 2) / 2‖
        ≤ 3 + B
      ∧ ‖_root_.logDeriv xi (1 / 2 + w - (t : ℂ) * I) -
          Complex.log ((1 / 2 + w - (t : ℂ) * I) / 2) / 2‖ ≤ 3 + B := by
  refine ⟨h.stirling_box hR hR16 ht (slicePoint_mem_logDerivBox h1 h2 h3), ?_⟩
  have hc := h.stirling_box hR hR16 ht (s := 1 / 2 + (starRingEnd ℂ) w + (t : ℂ) * I)
    (slicePoint_mem_logDerivBox (w := (starRingEnd ℂ) w) (by simpa using h1)
      (by simpa using h2) (by simpa using h3))
  have hre : 0 < (1 / 2 + (starRingEnd ℂ) w + (t : ℂ) * I).re := by
    simp; linarith
  rw [ZetaScaleData.conj_slicePoint', norm_logDeriv_xi_sub_half_log_conj hre]
  exact hc

/-- The Stirling hypothesis on the saddle disc `|w − Rs| ≤ R/4`, `R ≤ Rs ≤ 5R`. -/
theorem xiSliceStirling (h : ZetaLogDerivScaleData t R B) (hR : 0 < R) (hR16 : R ≤ 1 / 16)
    (ht : 8 ≤ t) {Rs : ℝ} (hRs1 : R ≤ Rs) (hRs5 : Rs ≤ 5 * R) :
    XiSliceStirling t (3 + B) (closedBall (Rs : ℂ) (R / 4)) := by
  intro w hw
  rw [mem_closedBall, dist_eq_norm] at hw
  have hre := abs_le.mp ((Complex.abs_re_le_norm (w - Rs)).trans hw)
  have him := (Complex.abs_im_le_norm (w - Rs)).trans hw
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    sub_zero] at hre him
  exact h.stirling_slice hR hR16 ht (by linarith) (by linarith) (by linarith)

theorem closedBall_subset_logDerivSliceSet {Rs : ℝ} (hR : 0 < R) (hR16 : R ≤ 1 / 16)
    (hRs1 : R ≤ Rs) (hRs5 : Rs ≤ 5 * R) :
    closedBall (Rs : ℂ) (R / 4) ⊆ logDerivSliceSet R := by
  intro w hw
  rw [mem_closedBall, dist_eq_norm] at hw
  have hre := abs_le.mp ((Complex.abs_re_le_norm (w - Rs)).trans hw)
  have him := abs_le.mp ((Complex.abs_im_le_norm (w - Rs)).trans hw)
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    sub_zero] at hre him
  rw [mem_logDerivSliceSet]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

end ZetaLogDerivScaleData

namespace ZetaLogDerivScaleData

variable {t R B : ℝ}

/-- **The saddle radius** lies in `[R, 5R]`. -/
theorem saddle_radius (h : ZetaLogDerivScaleData t R B) (hR : 0 < R) (hR16 : R ≤ 1 / 16)
    (ht : 48 ≤ t) (hu : 10000 ≤ Real.log t) (hBu : B ≤ Real.log t / 10 ^ 8) {k : ℕ}
    (hk1 : R * Real.log t ≤ k) (hk2 : (k : ℝ) ≤ 2 * R * Real.log t) :
    ∃ Rs : ℝ, R ≤ Rs ∧ Rs ≤ 5 * R
      ∧ (HTGeometry.scaledLogDeriv (xiSliceProduct t) Rs).re = 2 * (k : ℝ) := by
  have ht0 : 0 < t := by linarith
  obtain ⟨b1, b2, -, -⟩ := scale_budget (C := 3 + B) (by linarith) hu
  have hIcc : ∀ R' ∈ Icc R (5 * R), (R' : ℂ) ∈ logDerivSliceSet R := by
    intro R' hR'
    rw [mem_logDerivSliceSet]
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨by linarith [hR'.1], by linarith [hR'.2], by linarith, by linarith⟩
  have hEreal : ∀ R' ∈ Icc R (5 * R), ‖_root_.logDeriv xi (1 / 2 + (R' : ℂ) + (t : ℂ) * I)
      - Complex.log ((1 / 2 + (R' : ℂ) + (t : ℂ) * I) / 2) / 2‖ ≤ 3 + B := by
    intro R' hR'
    exact (h.stirling_slice hR hR16 (by linarith) (w := (R' : ℂ)) (by simp; linarith [hR'.1])
      (by simp; linarith [hR'.2]) (by simp; linarith)).1
  have hlog2 : Real.log (t / 2) = Real.log t - Real.log 2 := by
    rw [Real.log_div ht0.ne' (by norm_num)]
  have hlo : R * (Real.log t + 2 * (3 + B)) ≤ 2 * (k : ℝ) := by nlinarith
  have hhi : 2 * (k : ℝ) ≤ 5 * R * (Real.log (t / 2) - 2 * (3 + B)) := by
    rw [hlog2]; nlinarith
  obtain ⟨Rs, ⟨hRa, hRb⟩, hsad⟩ := exists_saddle_radius_strip (by linarith) hR.le (by linarith)
    (by linarith) (fun w hw => h.xiSliceProduct_ne_zero hR hw) hIcc hEreal hlo hhi
  exact ⟨Rs, hRa, hRb, hsad⟩

/-- **Slope and disc constant.** -/
theorem saddle_slope_disc (h : ZetaLogDerivScaleData t R B) (hR : 0 < R) (hR16 : R ≤ 1 / 16)
    (ht : 48 ≤ t) (hu : 10000 ≤ Real.log t) (hB : 0 ≤ B) (hBu : B ≤ Real.log t / 10 ^ 8)
    {Rs : ℝ} (hRa : R ≤ Rs) (hRb : Rs ≤ 5 * R) :
    9 / 10 * Real.log t ≤ (deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) Rs).re
      ∧ (deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) Rs).re ≤ 2 * Real.log t
      ∧ xiSliceDiscConstantStrip (R / 4) (3 + B) t Rs ≤ 2 * (R / 4) * Real.log t := by
  have ht0 : 0 < t := by linarith
  set C := 3 + B with hCdef
  have hC0 : 0 ≤ C := by linarith
  obtain ⟨-, -, b3, b4⟩ := scale_budget (C := C) (by linarith) hu
  have hball := closedBall_subset_logDerivSliceSet hR hR16 hRa hRb
  have hS := h.xiSliceStirling hR hR16 (by linarith) hRa hRb
  obtain ⟨hF₁lo, hF₁hi⟩ := xiSlice_saddleSlope_bounds_strip (isOpen_logDerivSliceSet R)
    (fun w hw => h.xiSliceProduct_ne_zero hR hw) hball
    (by positivity : 0 < R / 4) (by linarith) (by linarith) (by linarith) (by linarith) hS
  have hq0 : 0 ≤ Real.log 4 + Real.pi + 4 * C := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); positivity
  have hRq : Rs * (Real.log 4 + Real.pi + 4 * C) / (R / 4) ≤
      20 * (Real.log 4 + Real.pi + 4 * C) := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hlog2 : Real.log (t / 2) = Real.log t - Real.log 2 := by
    rw [Real.log_div ht0.ne' (by norm_num)]
  rw [hlog2] at hF₁lo
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨by linarith, by linarith, ?_⟩
  unfold xiSliceDiscConstantStrip
  have e : Real.log (3 * t / 2) = Real.log (3 / 2) + Real.log t := by
    rw [show 3 * t / 2 = 3 / 2 * t by ring, Real.log_mul (by norm_num) ht0.ne']
  rw [e]
  have h3 : Rs * (Real.log 4 + Real.pi + 4 * C) ≤ 5 * R * (Real.log 4 + Real.pi + 4 * C) :=
    mul_le_mul_of_nonneg_right hRb hq0
  have h4 := mul_le_mul_of_nonneg_left b4 hR.le
  nlinarith

/-- **The size of `Rs log t`**: `k ≤ Rs log t ≤ 4k`. -/
theorem saddle_scale (h : ZetaLogDerivScaleData t R B) (hR : 0 < R) (hR16 : R ≤ 1 / 16)
    (ht : 48 ≤ t) (hu : 10000 ≤ Real.log t) (hBu : B ≤ Real.log t / 10 ^ 8) {k : ℕ} {Rs : ℝ}
    (hRa : R ≤ Rs) (hRb : Rs ≤ 5 * R)
    (hsad : (HTGeometry.scaledLogDeriv (xiSliceProduct t) Rs).re = 2 * (k : ℝ)) :
    (k : ℝ) ≤ Rs * Real.log t ∧ Rs * Real.log t ≤ 4 * k := by
  have ht0 : 0 < t := by linarith
  obtain ⟨b1, -, -, -⟩ := scale_budget (C := 3 + B) (by linarith) hu
  have hS := h.xiSliceStirling hR hR16 (by linarith) hRa hRb
  have hSR := (hS Rs (mem_closedBall_self (by positivity))).1
  obtain ⟨-, hLlo, hLhi⟩ := xiSliceLogDeriv_real_bounds_strip (by linarith) (by linarith)
    (by linarith) hSR
  have hRU : (Rs : ℂ) ∈ logDerivSliceSet R :=
    closedBall_subset_logDerivSliceSet hR hR16 hRa hRb (mem_closedBall_self (by positivity))
  have hsad' : Rs * (xiSliceLogDeriv t Rs).re = 2 * (k : ℝ) := by
    rw [← hsad, scaledLogDeriv_xiSliceProduct_of_ne (h.xiSliceProduct_ne_zero hR hRU)]
    simp [Complex.mul_re]
  have hlog2 : Real.log (t / 2) = Real.log t - Real.log 2 := by
    rw [Real.log_div ht0.ne' (by norm_num)]
  rw [hlog2] at hLlo
  have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hRs0 : 0 < Rs := by linarith
  constructor
  · have : (xiSliceLogDeriv t Rs).re ≤ 2 * Real.log t := by linarith
    nlinarith
  · have : Real.log t / 2 ≤ (xiSliceLogDeriv t Rs).re := by linarith
    nlinarith

/-- The tail in terms of the order: `|S(θ)| ≤ exp(−k/(2·10⁹))` for `10⁻⁴ ≤ θ ≤ π/2`. -/
theorem tail_le_order (h : ZetaLogDerivScaleData t R B) (hR : 0 < R) (hR16 : R ≤ 1 / 16)
    (ht : 64 ≤ t) (hu : 10 ^ 7 ≤ Real.log t) (hB : 0 ≤ B) (hBu : B ≤ Real.log t / 10 ^ 9)
    {k : ℕ} {Rs : ℝ} (hRa : R ≤ Rs) (hRb : Rs ≤ 5 * R) (hRsk : (k : ℝ) ≤ Rs * Real.log t) :
    ∀ θ : ℝ, 1 / (1000 * 10) ≤ θ → θ ≤ Real.pi / 2 →
      ‖sliceArc t Rs k θ‖ ≤ Real.exp (-(1 / (2 * 10 ^ 9)) * k) := by
  intro θ hθ hθπ
  have ht0 : 0 < t := by linarith
  have hlog2 : Real.log (t / 2) = Real.log t - Real.log 2 := by
    rw [Real.log_div ht0.ne' (by norm_num)]
  have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hsmall : 80 * (4 + B) ≤ 1 / (1000 * 10) * Real.log (t / 2) := by
    rw [hlog2]; nlinarith
  refine (h.norm_sliceArc_le hR hR16 ht hB k hRa hRb (by norm_num) (by norm_num) hθ hθπ
    hsmall).trans (Real.exp_le_exp.mpr ?_)
  have hX : Real.log t / 2 ≤ Real.log (t / 2) := by rw [hlog2]; linarith
  have hRs0 : 0 < Rs := by linarith
  have h1 : Rs * (Real.log t / 2) ≤ Rs * Real.log (t / 2) := mul_le_mul_of_nonneg_left hX hRs0.le
  nlinarith

end ZetaLogDerivScaleData

/-- **Positivity from log-derivative scale data.** There is `k₁` such that `c_{2k}(t) > 0` whenever
`ZetaLogDerivScaleData t R B` holds with `0 < R ≤ 1/16`, `t ≥ 64`, `log t ≥ 10⁷`,
`0 ≤ B ≤ (log t)/10⁹`, `R log t ≤ k ≤ 2R log t` and `k ≥ k₁`. -/
theorem exists_xiSliceCoeff_pos_of_logDerivScaleData :
    ∃ k₁ : ℝ, 1 ≤ k₁ ∧ ∀ t R B : ℝ, ∀ k : ℕ, ZetaLogDerivScaleData t R B → 0 < R →
      R ≤ 1 / 16 → 64 ≤ t → 10 ^ 7 ≤ Real.log t → 0 ≤ B → B ≤ Real.log t / 10 ^ 9 →
      R * Real.log t ≤ k → (k : ℝ) ≤ 2 * R * Real.log t → k₁ ≤ k →
      0 < xiSliceCoeff t (2 * k) := by
  have e1 := (tendsto_order.1 tendsto_rpow_half_mul_exp_neg_fifth_root).2 50 (by norm_num)
  have e3 := (tendsto_order.1 (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 5))).2
    (1 / (1000 * 10)) (by norm_num)
  have e4 := (tendsto_order.1 (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 5))).2
    (3 / (2 * (1 + 128 * 10))) (by norm_num)
  obtain ⟨Λ₀, hΛ₀⟩ := Filter.eventually_atTop.mp (e1.and (e3.and e4))
  have e5 := (tendsto_order.1 (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2)
    (1 / (2 * 10 ^ 9)) (by norm_num))).2 (1 / (10 * Real.pi)) (by positivity)
  obtain ⟨K₅, hK₅⟩ := Filter.eventually_atTop.mp e5
  refine ⟨max (max Λ₀ K₅) 1, le_max_right _ _, ?_⟩
  intro t R B k h hR hR16 ht hu hB hBu hk1 hk2 hk₁
  have hkΛ : Λ₀ ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk₁
  have hkK : K₅ ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk₁
  have hk1' : (1 : ℝ) ≤ k := le_trans (le_max_right _ _) hk₁
  have hu0 : 0 < Real.log t := by linarith
  have hu4 : 10000 ≤ Real.log t := by linarith
  have hBu8 : B ≤ Real.log t / 10 ^ 8 := by
    have : Real.log t / 10 ^ 9 ≤ Real.log t / 10 ^ 8 :=
      div_le_div_of_nonneg_left hu0.le (by norm_num) (by norm_num)
    linarith
  obtain ⟨Rs, hRa, hRb, hsad⟩ := h.saddle_radius hR hR16 (by linarith) hu4 hBu8 hk1 hk2
  obtain ⟨hF₁lo, hF₁hi, hKd⟩ := h.saddle_slope_disc hR hR16 (by linarith) hu4 hB hBu8 hRa hRb
  obtain ⟨hRsk, hRsk4⟩ := h.saddle_scale hR hR16 (by linarith) hu4 hBu8 hRa hRb hsad
  have htail := h.tail_le_order hR hR16 ht hu hB hBu hRa hRb hRsk
  obtain ⟨hE1, hE3, hE4⟩ := hΛ₀ (Rs * Real.log t) (by linarith)
  have hΛpos : 0 < Rs * Real.log t := by linarith
  have hEt : Real.pi / 2 * Real.exp (-(1 / (2 * 10 ^ 9)) * k)
      ≤ (Rs * Real.log t) ^ (-(1 / 2) : ℝ) / 10 := by
    have hk0 : (0 : ℝ) < k := by linarith
    have hmono : (4 * (k : ℝ)) ^ (-(1 / 2) : ℝ) ≤ (Rs * Real.log t) ^ (-(1 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hΛpos hRsk4 (by norm_num)
    have h4k : (4 * (k : ℝ)) ^ (-(1 / 2) : ℝ) = 1 / (2 * (k : ℝ) ^ (1 / 2 : ℝ)) := by
      rw [Real.rpow_neg (by positivity), Real.mul_rpow (by norm_num) hk0.le,
        show (4 : ℝ) ^ (1 / 2 : ℝ) = 2 by
          rw [← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]]
      field_simp
    have h5 := (hK₅ k hkK).le
    have hsq : 0 < (k : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hk0 _
    rw [h4k] at hmono
    have key : Real.pi / 2 * Real.exp (-(1 / (2 * 10 ^ 9)) * k)
        ≤ 1 / (2 * (k : ℝ) ^ (1 / 2 : ℝ)) / 10 := by
      rw [div_div, le_div_iff₀ (by positivity)]
      have e : Real.pi / 2 * Real.exp (-(1 / (2 * 10 ^ 9)) * k) * (2 * (k : ℝ) ^ (1 / 2 : ℝ) * 10)
          = 10 * Real.pi * ((k : ℝ) ^ (1 / 2 : ℝ) * Real.exp (-(1 / (2 * 10 ^ 9)) * k)) := by ring
      rw [e]
      have hpos : 0 < 10 * Real.pi := by positivity
      calc 10 * Real.pi * ((k : ℝ) ^ (1 / 2 : ℝ) * Real.exp (-(1 / (2 * 10 ^ 9)) * k))
          ≤ 10 * Real.pi * (1 / (10 * Real.pi)) := mul_le_mul_of_nonneg_left h5 hpos.le
        _ = 1 := by field_simp
    linarith
  exact xiSliceCoeff_pos_of_saddle_strip (isOpen_logDerivSliceSet R)
    (fun w hw => h.xiSliceProduct_ne_zero hR hw)
    (ZetaLogDerivScaleData.closedBall_subset_logDerivSliceSet hR hR16 hRa hRb)
    (h.xiSliceStirling hR hR16 (by linarith) hRa hRb) (by linarith) (by positivity) (by linarith)
    (by linarith : 2 * (R / 4) ≤ 5 * R) (by field_simp; ring) (by linarith) hu0
    (by linarith) hRb (by linarith) hsad hF₁lo hF₁hi hKd htail (by linarith) hE1 hE3 hE4 hEt

end RHTower
