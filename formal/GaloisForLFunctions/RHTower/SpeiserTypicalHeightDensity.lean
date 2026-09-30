import GaloisForLFunctions.RHTower.XiSliceBoundedOrderExponentialRate
import GaloisForLFunctions.RHTower.CompletedSplitRightHalfPlane
import GaloisForLFunctions.RHTower.SmoothAFEZetaChiShiftDerivative
import GaloisForLFunctions.RHTower.ZetaChiDisplacedCriticalRatioOscillatoryIntegral
import GaloisForLFunctions.RHTower.HardyZPhaseAsymptotic

/-!
# Speiser's criterion at typical heights

Speiser: RH ⇔ `ζ'` has no zeros in `0 < Re s < 1/2`. This module proves the typical-height form at
the scale `R = κ/log T`.

At a height `t` with log-derivative scale data `ZetaLogDerivScaleData t R B`
(`|ζ'/ζ| ≤ B` on the right box `1/2 + 3R/4 ≤ Re ≤ 1/2 + 6R`, `|Im − t| ≤ 6R`, and no zeros of
`ζ` near it), every point `s` of the mirrored left box `1/2 − 6R ≤ Re s ≤ 1/2 − 3R/4`,
`|Im s − t| ≤ 6R`, has `ζ(s) ≠ 0` and `ζ'(s) ≠ 0` as soon as `B + 1 < log(Im s/2π)`
(`riemannZeta_ne_zero_and_deriv_ne_zero_leftBox`). By reflection,
`ζ'/ζ(s) = χ'/χ(s) − ζ'/ζ(1 − s)`, where `|ζ'/ζ(1 − s)| = |ζ'/ζ(1 − s̄)| ≤ B` and
`Re χ'/χ(s) ≤ −log(Im s/2π) + 1`. The last bound holds because `χ'/χ` on the critical line is minus
twice the Riemann–Siegel phase rate, and the horizontal displacement costs `O(1/t)`.

With the exponential scale-data theorem at level `(log T)/2`, the heights `t ∈ [T, 2T]` near which
`ζ'` vanishes somewhere in the left box at scale `R` have measure
`≤ C T (2e^{−κ/120000} + κ²e^{−κ/16} + e^{−κ/30}) + C T^{1/2}`
(`exists_volume_deriv_riemannZeta_eq_zero_leftBox_le`).

Summing over the dyadic scales `R_j = 2^{j−J}/24`, `j ≤ J`, whose left boxes tile
`1/4 ≤ Re s ≤ 1/2 − κ/log T`, gives the rate `C T e^{−cκ}` for the heights near which `ζ'` has a zero
anywhere in that range (`exists_volume_deriv_riemannZeta_eq_zero_near_line_le`).
-/

noncomputable section

open Complex Set MeasureTheory Filter

namespace RHTower

/-- `Re χ'/χ(1/2 − d + iτ) ≤ −log(τ/2π) + 1` for `0 < d ≤ 1/4`, `τ ≥ 100`. -/
theorem re_logDeriv_zetaChi_displaced_le {d τ : ℝ} (hd : 0 < d) (hd4 : d ≤ 1 / 4)
    (hτ : 100 ≤ τ) :
    (logDeriv zetaChi (displacedLinePt d τ)).re ≤ -Real.log (τ / (2 * Real.pi)) + 1 := by
  have hτ0 : 0 < τ := by linarith
  have h1 := norm_logDeriv_zetaChi_displaced_sub_critical_le hd hd4 (by linarith : 4 ≤ τ)
  have h2 := logDeriv_zetaChi_displacedLinePt_zero_eq τ
  have h3 := gammaHardyPhaseRate_ge_log_conductor hτ0
  have hre := (Complex.re_le_norm _).trans h1
  rw [Complex.sub_re, h2, Complex.ofReal_re] at hre
  have hπ := Real.pi_lt_d2
  have hsmall1 : 2 * (16 / τ ^ 2 + 2 * Real.pi / τ) ≤ 1 / 2 := by
    have : 16 / τ ^ 2 ≤ 16 / 10000 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num); nlinarith
    have : 2 * Real.pi / τ ≤ 2 * 3.15 / 100 := by
      rw [div_le_div_iff₀ hτ0 (by norm_num)]; nlinarith
    linarith
  have hsmall2 : 2 / τ ^ 2 + Real.pi / (2 * τ) ≤ 1 / 4 := by
    have : 2 / τ ^ 2 ≤ 2 / 10000 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num); nlinarith
    have : Real.pi / (2 * τ) ≤ 3.15 / 200 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  linarith

/-- **Nonvanishing of `ζ` and `ζ'` on the mirrored left box.** -/
theorem riemannZeta_ne_zero_and_deriv_ne_zero_leftBox {t R B : ℝ}
    (hdata : ZetaLogDerivScaleData t R B) (hR : 0 < R) (hR24 : R ≤ 1 / 24) (ht : 101 ≤ t)
    {s : ℂ} (h1 : 1 / 2 - 6 * R ≤ s.re) (h2 : s.re ≤ 1 / 2 - 3 * R / 4) (h3 : |s.im - t| ≤ 6 * R)
    (hB : B + 1 < Real.log (s.im / (2 * Real.pi))) :
    riemannZeta s ≠ 0 ∧ deriv riemannZeta s ≠ 0 := by
  have hsim : 100 ≤ s.im := by have := abs_le.mp h3; linarith
  set w : ℂ := 1 - (starRingEnd ℂ) s with hw
  have hwre : w.re = 1 - s.re := by rw [hw]; simp
  have hwim : w.im = s.im := by rw [hw]; simp
  have hw1 : (starRingEnd ℂ) w = 1 - s := by rw [hw]; simp
  -- `w` lies in the right box
  have hw0 : riemannZeta w ≠ 0 := by
    intro h0
    have := hdata.zeroFree w h0 (by rw [hwre]; linarith)
    rw [hwim, hwre] at this
    linarith
  have h1s : riemannZeta (1 - s) ≠ 0 := by
    rw [← hw1, riemannZeta_conj]
    exact (map_ne_zero _).mpr hw0
  have hζs : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_reflect (by linarith) (by linarith) h1s
  refine ⟨hζs, ?_⟩
  have hBw : ‖logDeriv riemannZeta w‖ ≤ B :=
    hdata.logDeriv w (by rw [hwre]; linarith) (by rw [hwre]; linarith) (by rw [hwim]; exact h3)
  have hB1s : ‖logDeriv riemannZeta (1 - s)‖ ≤ B := by
    rw [← hw1, logDeriv_riemannZeta_conj, Complex.norm_conj]; exact hBw
  -- the reflection formula
  have hs0 : 0 < s.re := by linarith
  have hs1 : s.re < 1 := by linarith
  have hrefl := logDeriv_riemannZeta_add_reflect_of_strip hs0 hs1 hζs h1s
  have hpoles : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := div_two_ne_neg_nat_of_re_pos hs0
  have hpoles' : ∀ m : ℕ, (1 - s) / 2 ≠ -(m : ℂ) := div_two_ne_neg_nat_of_re_pos (by simp; linarith)
  have hchi := logDeriv_zetaChi_off_poles hpoles hpoles'
  have hL : logDeriv riemannZeta s = logDeriv zetaChi s - logDeriv riemannZeta (1 - s) := by
    rw [hchi]; linear_combination hrefl
  -- `s` as a displaced line point
  set d := 1 / 2 - s.re with hd
  have hsd : s = displacedLinePt d s.im := by
    apply Complex.ext
    · rw [displacedLinePt_re, hd]; ring
    · simp [displacedLinePt]
  have hχ := re_logDeriv_zetaChi_displaced_le (d := d) (τ := s.im) (by rw [hd]; linarith)
    (by rw [hd]; linarith) hsim
  rw [← hsd] at hχ
  have hre : (logDeriv riemannZeta s).re < 0 := by
    rw [hL, Complex.sub_re]
    have := (abs_le.mp ((Complex.abs_re_le_norm _).trans hB1s)).1
    linarith
  intro hd0
  have : logDeriv riemannZeta s = 0 := by rw [logDeriv_apply, hd0, zero_div]
  rw [this, Complex.zero_re] at hre
  exact lt_irrefl 0 hre

/-- **Speiser at typical heights.** There are `C` and `κ₁ ≥ 1` such that for all large `T` and
every scale `0 < R ≤ 1/24` with `κ = R log T ≥ κ₁`, the heights `t ∈ [T, 2T]` near which `ζ'`
vanishes somewhere on the left box `1/2 − 6R ≤ Re s ≤ 1/2 − 3R/4`, `|Im s − t| ≤ 6R`, have measure
`≤ C T (2e^{−κ/120000} + κ²e^{−κ/16} + e^{−κ/30}) + C T^{1/2}`. -/
theorem exists_volume_deriv_riemannZeta_eq_zero_leftBox_le :
    ∃ C κ₁ : ℝ, 0 < C ∧ 1 ≤ κ₁ ∧ ∀ᶠ T in atTop, ∀ R : ℝ, 0 < R → R ≤ 1 / 24 →
      κ₁ ≤ R * Real.log T →
      volume {t | t ∈ Icc T (2 * T) ∧ ∃ s : ℂ, 1 / 2 - 6 * R ≤ s.re ∧
          s.re ≤ 1 / 2 - 3 * R / 4 ∧ |s.im - t| ≤ 6 * R ∧ deriv riemannZeta s = 0} ≤
        ENNReal.ofReal (C * T * (Real.exp (-(R * Real.log T / 120000)) / (1 / 2) +
          ((R * Real.log T) ^ 2 * Real.exp (-(R * Real.log T / 16)) +
            Real.exp (-(R * Real.log T * (1 / 2) / 15)))) + C * T ^ ((1 : ℝ) / 2)) := by
  obtain ⟨C, κ₁, hC, hκ₁, hev⟩ := exists_volume_not_zetaLogDerivScaleData_le_exp
    (ε := 1 / 2) (by norm_num) (by norm_num)
  refine ⟨C, κ₁, hC, hκ₁, ?_⟩
  have hL := Real.tendsto_log_atTop.eventually_ge_atTop (2 * Real.log (4 * Real.pi) + 4)
  filter_upwards [hev, hL, eventually_ge_atTop (102 : ℝ)] with T hTev hLT hT102
  intro R hR hR24 hκ
  refine le_trans (measure_mono ?_) (hTev R hR (by linarith) hκ)
  rintro t ⟨ht, s, h1, h2, h3, hd⟩
  refine ⟨ht, fun hdata => ?_⟩
  have ht101 : 101 ≤ t := by linarith [ht.1]
  have hsim : t - 6 * R ≤ s.im := by have := abs_le.mp h3; linarith
  have hB : 1 / 2 * Real.log T + 1 < Real.log (s.im / (2 * Real.pi)) := by
    have hT0 : 0 < T := by linarith
    have hsT : T / 2 ≤ s.im := by linarith [ht.1]
    have h4 : Real.log (T / (4 * Real.pi)) ≤ Real.log (s.im / (2 * Real.pi)) := by
      apply Real.log_le_log (by positivity)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [Real.pi_pos]
    rw [Real.log_div hT0.ne' (by positivity)] at h4
    linarith
  exact (riemannZeta_ne_zero_and_deriv_ne_zero_leftBox hdata hR hR24 ht101 h1 h2 h3 hB).2 hd

/-- The dyadic grid pinned at `1/24`: with `J = log₂ ⌊L/(8κ)⌋₊` and `κ₀ = L/(24·2^J)`, one has
`κ/6 ≤ κ₀ ≤ 4κ/3` and `J ≤ ⌊L⌋₊` whenever `1 ≤ κ ≤ L/4`. -/
theorem speiser_grid_facts {L κ : ℝ} (hκ : 1 ≤ κ) (hκL : κ ≤ L / 4) :
    κ / 6 ≤ L / (24 * 2 ^ Nat.log 2 ⌊L / (8 * κ)⌋₊) ∧
      L / (24 * 2 ^ Nat.log 2 ⌊L / (8 * κ)⌋₊) ≤ 4 * κ / 3 ∧
      Nat.log 2 ⌊L / (8 * κ)⌋₊ ≤ ⌊L⌋₊ := by
  have hκ0 : 0 < κ := by linarith
  have hL : 0 < L := by linarith
  set n := ⌊L / (8 * κ)⌋₊ with hn
  set J := Nat.log 2 n with hJ
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · have hJ0 : J = 0 := by rw [hJ, h0, Nat.log_zero_right]
    have hlt : L / (8 * κ) < 1 := Nat.floor_eq_zero.mp (by rw [← hn]; exact h0)
    rw [div_lt_one (by positivity)] at hlt
    rw [hJ0, pow_zero, mul_one]
    refine ⟨?_, ?_, Nat.zero_le _⟩
    · rw [le_div_iff₀ (by norm_num)]; linarith
    · rw [div_le_iff₀ (by norm_num)]; linarith
  · have hle : 2 ^ J ≤ n := Nat.pow_log_le_self 2 hpos.ne'
    have hlt : n + 1 ≤ 2 ^ (J + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
    have hnL : (n : ℝ) ≤ L / (8 * κ) := Nat.floor_le (by positivity)
    have hnL' : L / (8 * κ) < n + 1 := Nat.lt_floor_add_one _
    have hle' : (2 : ℝ) ^ J ≤ n := by exact_mod_cast hle
    have hlt' : (n : ℝ) + 1 ≤ 2 ^ (J + 1) := by exact_mod_cast hlt
    have h2J : (0 : ℝ) < 2 ^ J := by positivity
    have hA : 8 * κ * 2 ^ J ≤ L := by
      have := hle'.trans hnL
      rw [le_div_iff₀ (by positivity)] at this; linarith
    have hB : L < 16 * κ * 2 ^ J := by
      have := hnL'.trans_le hlt'
      rw [div_lt_iff₀ (by positivity), pow_succ] at this; linarith
    refine ⟨?_, ?_, ?_⟩
    · rw [le_div_iff₀ (by positivity)]; nlinarith
    · rw [div_le_iff₀ (by positivity)]; nlinarith
    · have h1 : J < 2 ^ J := Nat.lt_two_pow_self
      have h2 : n ≤ ⌊L⌋₊ := Nat.floor_le_floor (by
        rw [div_le_iff₀ (by positivity)]; nlinarith)
      omega

/-- On the grid `R_j = 2^j κ₀/L`, `j ≤ J`, with top scale `1/24`, every distance
`d ∈ [3κ₀/(4L), 1/4]` lies in some window `[3R_j/4, 6R_j]`. -/
theorem exists_speiser_grid_scale {L κ₀ d : ℝ} {J : ℕ} (hL : 0 < L) (hκ₀ : 0 < κ₀)
    (htop : 2 ^ J * κ₀ / L = 1 / 24) (hd1 : 3 * (κ₀ / L) / 4 ≤ d) (hd2 : d ≤ 1 / 4) :
    ∃ j ≤ J, 3 * (2 ^ j * κ₀ / L) / 4 ≤ d ∧ d ≤ 6 * (2 ^ j * κ₀ / L) := by
  classical
  have hex : ∃ j, d ≤ 6 * (2 ^ j * κ₀ / L) := ⟨J, by rw [htop]; linarith⟩
  refine ⟨Nat.find hex, Nat.find_min' hex (by rw [htop]; linarith), ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0, pow_zero, one_mul]; exact hd1
  · obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hnot := not_le.mp (Nat.find_min hex (show k < Nat.find hex by omega))
    rw [hk, pow_succ]
    have e : 3 * (2 ^ k * 2 * κ₀ / L) / 4 = 6 * (2 ^ k * κ₀ / L) / 4 := by ring
    have : 0 ≤ 6 * (2 ^ k * κ₀ / L) := by positivity
    rw [e]; linarith

/-- Covering of the near-line left region by the left boxes of the grid `2^j κ₀/log T`, `j ≤ J`:
outside the union of the failures of the scale data, `ζ'` has no zero in
`1/4 ≤ Re s ≤ 1/2 − κ/log T` within `κ/log T` of the height. -/
theorem deriv_near_line_subset_scales {T κ ε κ₀ : ℝ} {J : ℕ} (hT : 102 ≤ T)
    (hLT : 2 * Real.log (4 * Real.pi) + 4 ≤ Real.log T) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2)
    (hκ₀ : 0 < κ₀) (htop : 2 ^ J * κ₀ / Real.log T = 1 / 24) (hg1 : κ / 6 ≤ κ₀)
    (hg2 : κ₀ ≤ 4 * κ / 3) :
    {t | t ∈ Icc T (2 * T) ∧ ∃ s : ℂ, 1 / 4 ≤ s.re ∧ s.re ≤ 1 / 2 - κ / Real.log T ∧
        |s.im - t| ≤ κ / Real.log T ∧ deriv riemannZeta s = 0} ⊆
      ⋃ j ∈ Finset.range (J + 1), {t | t ∈ Icc T (2 * T) ∧
        ¬ ZetaLogDerivScaleData t (2 ^ j * κ₀ / Real.log T) (ε * Real.log T)} := by
  have hT0 : 0 < T := by linarith
  have hlog4π : 0 < Real.log (4 * Real.pi) := Real.log_pos (by nlinarith [Real.pi_gt_three])
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log T := ⟨_, rfl⟩
  rw [← hLdef] at hLT htop ⊢
  have hL0 : 0 < L := by linarith
  rintro t ⟨ht, s, h1, h2, h3, hd⟩
  have hd1 : 3 * (κ₀ / L) / 4 ≤ 1 / 2 - s.re := by
    have : κ₀ / L ≤ 4 * κ / 3 / L := div_le_div_of_nonneg_right hg2 hL0.le
    have e : 3 * (4 * κ / 3 / L) / 4 = κ / L := by ring
    linarith
  obtain ⟨j, hjJ, hj1, hj2⟩ := exists_speiser_grid_scale hL0 hκ₀ htop hd1 (by linarith)
  refine Set.mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr (by omega), ht, fun hdata => ?_⟩
  have hRj : 2 ^ j * κ₀ / L ≤ 1 / 24 := by
    rw [← htop]
    have : (2 : ℝ) ^ j ≤ 2 ^ J := pow_le_pow_right₀ (by norm_num) hjJ
    gcongr
  have hRlow : κ / L ≤ 6 * (2 ^ j * κ₀ / L) := by
    have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    rw [← mul_div_assoc, div_le_div_iff_of_pos_right hL0]
    nlinarith
  have hsim : T / 2 ≤ s.im := by
    have := abs_le.mp h3
    have hKL : κ / L ≤ 1 / 4 := by linarith
    linarith [ht.1]
  have hB : ε * L + 1 < Real.log (s.im / (2 * Real.pi)) := by
    have h4 : Real.log (T / (4 * Real.pi)) ≤ Real.log (s.im / (2 * Real.pi)) := by
      apply Real.log_le_log (by positivity)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [Real.pi_pos]
    rw [Real.log_div hT0.ne' (by positivity), ← hLdef] at h4
    have : ε * L ≤ L / 2 := by nlinarith
    linarith
  exact (riemannZeta_ne_zero_and_deriv_ne_zero_leftBox hdata (by positivity) hRj
    (by linarith [ht.1]) (by linarith) (by linarith) (h3.trans hRlow) hB).2 hd

/-- Summation of the scale-data failures over the grid `2^j κ₀/log T`, `j ≤ J ≤ ⌊log T⌋₊`. -/
theorem volume_speiser_scales_le {C T ε κ₀ κ₁ E : ℝ} {J : ℕ} (hT1 : 1 < T) (hC : 0 < C)
    (hε : 0 < ε) (hε4 : ε ≤ 1 / 4000) (hκ₀1 : κ₁ ≤ κ₀) (hκ₀ε : 1 ≤ ε / 30 * κ₀)
    (hJ : J ≤ ⌊Real.log T⌋₊) (hRj : ∀ j ≤ J, 2 ^ j * κ₀ / Real.log T ≤ 1 / 16) (hE0 : 0 < E)
    (hEκ : Real.exp (-(κ₀ * (ε / 30))) ≤ E)
    (hTlog : 4 * C / E * (Real.log T + 3) ^ 1 ≤ Real.exp (1 / 2 * Real.log T))
    (hTev : ∀ R : ℝ, 0 < R → R ≤ 1 / 16 → κ₁ ≤ R * Real.log T →
      volume {t | t ∈ Icc T (2 * T) ∧ ¬ ZetaLogDerivScaleData t R (ε * Real.log T)} ≤
        ENNReal.ofReal (C * T * (Real.exp (-(R * Real.log T / 120000)) / ε +
          ((R * Real.log T) ^ 2 * Real.exp (-(R * Real.log T / 16)) +
            Real.exp (-(R * Real.log T * ε / 15)))) + C * T ^ ((1 : ℝ) / 2))) :
    volume (⋃ j ∈ Finset.range (J + 1), {t | t ∈ Icc T (2 * T) ∧
        ¬ ZetaLogDerivScaleData t (2 ^ j * κ₀ / Real.log T) (ε * Real.log T)}) ≤
      ENNReal.ofReal ((2 * (C * (1 / ε + 2049)) + 1 / 4) * T * E) := by
  have hT0 : 0 < T := by linarith
  set A0 : ℝ := C * (1 / ε + 2049) with hA0
  have hA00 : 0 ≤ A0 := by positivity
  set A : ℝ := A0 * Real.exp (-(κ₀ * (ε / 30))) with hA
  have hA0' : 0 ≤ A := by positivity
  have hscale : ∀ j ∈ Finset.range (J + 1), volume {t | t ∈ Icc T (2 * T) ∧
      ¬ ZetaLogDerivScaleData t (2 ^ j * κ₀ / Real.log T) (ε * Real.log T)} ≤
      ENNReal.ofReal (A * T * (1 / 2) ^ j / 1 + C * T ^ ((1 : ℝ) / 2)) := fun j hj => by
    have := volume_dyadic_scale_exp_le j hT1 hC hε hε4 hκ₀1 hκ₀ε
      (hRj j (by have := Finset.mem_range.mp hj; omega)) hTev
    rw [hA, hA0]
    exact this
  have hsum := sum_scale_bounds_le (⌊Real.log T⌋₊ + 1) hA0' hC.le hT0.le
    (show (0 : ℝ) < 1 by norm_num) (Finset.range (J + 1))
    (Finset.range_subset_range.mpr (by omega))
  have hfirst : 2 * A * T / 1 ≤ 2 * A0 * T * E := by
    rw [div_one, hA]
    have := mul_le_mul_of_nonneg_left hEκ (show 0 ≤ 2 * A0 * T by positivity)
    linarith
  have hsecond := count_term_le hC.le hE0 hT1 hTlog
  have e1 : 2 * A0 * T * E + E * T / 4 = (2 * A0 + 1 / 4) * T * E := by ring
  calc volume (⋃ j ∈ Finset.range (J + 1), {t | t ∈ Icc T (2 * T) ∧
          ¬ ZetaLogDerivScaleData t (2 ^ j * κ₀ / Real.log T) (ε * Real.log T)})
      ≤ ∑ j ∈ Finset.range (J + 1), volume {t | t ∈ Icc T (2 * T) ∧
          ¬ ZetaLogDerivScaleData t (2 ^ j * κ₀ / Real.log T) (ε * Real.log T)} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ Finset.range (J + 1),
          ENNReal.ofReal (A * T * (1 / 2) ^ j / 1 + C * T ^ ((1 : ℝ) / 2)) :=
        Finset.sum_le_sum hscale
    _ = ENNReal.ofReal (∑ j ∈ Finset.range (J + 1),
          (A * T * (1 / 2) ^ j / 1 + C * T ^ ((1 : ℝ) / 2))) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun j _ => by positivity]
    _ ≤ ENNReal.ofReal ((2 * A0 + 1 / 4) * T * E) :=
        ENNReal.ofReal_le_ofReal (by linarith)

/-- **Speiser near the line, exponential rate.** There are `C, c > 0` such that for every `κ` and
all large `T`, the heights `t ∈ [T, 2T]` within `κ/log T` of a zero of `ζ'` in
`1/4 ≤ Re s ≤ 1/2 − κ/log T` have measure at most `C T e^{−cκ}`. -/
theorem exists_volume_deriv_riemannZeta_eq_zero_near_line_le :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ κ : ℝ, ∀ᶠ T in atTop,
      volume {t | t ∈ Icc T (2 * T) ∧ ∃ s : ℂ, 1 / 4 ≤ s.re ∧ s.re ≤ 1 / 2 - κ / Real.log T ∧
          |s.im - t| ≤ κ / Real.log T ∧ deriv riemannZeta s = 0} ≤
        ENNReal.ofReal (C * T * Real.exp (-(c * κ))) := by
  set ε : ℝ := 1 / 10 ^ 9 with hε
  have hε0 : 0 < ε := by norm_num
  have hε4 : ε ≤ 1 / 4000 := by norm_num
  obtain ⟨C, κ₁, hC, hκ₁, hev⟩ := exists_volume_not_zetaLogDerivScaleData_le_exp hε0 (by norm_num)
  set c : ℝ := ε / 180 with hc
  have hc0 : 0 < c := by positivity
  set κ₂ : ℝ := max (6 * κ₁) (180 / ε) with hκ₂
  set A0 : ℝ := C * (1 / ε + 2049) with hA0
  have hA00 : 0 ≤ A0 := by positivity
  set Cf : ℝ := 2 * A0 + 2 + Real.exp (c * κ₂) with hCf
  refine ⟨Cf, c, by positivity, hc0, ?_⟩
  intro κ
  set E := Real.exp (-(c * κ)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  by_cases hsmall : κ < κ₂
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT1
    refine ((measure_mono (fun t ht => ht.1)).trans ?_).trans (ENNReal.ofReal_le_ofReal
      (show T ≤ Cf * T * E from ?_))
    · rw [Real.volume_Icc]; exact ENNReal.ofReal_le_ofReal (by linarith)
    have h1 : 1 ≤ Real.exp (c * κ₂) * E := by
      rw [hE, ← Real.exp_add]
      apply Real.one_le_exp
      have := mul_le_mul_of_nonneg_left hsmall.le hc0.le
      linarith
    have h2 : Real.exp (c * κ₂) ≤ Cf := by rw [hCf]; linarith
    have h3 : 1 ≤ Cf * E := h1.trans (mul_le_mul_of_nonneg_right h2 hE0.le)
    nlinarith
  have hκ₂κ := not_lt.mp hsmall
  have hκ6 : 6 * κ₁ ≤ κ := (le_max_left _ _).trans hκ₂κ
  have hκε : 180 / ε ≤ κ := (le_max_right _ _).trans hκ₂κ
  have hκ1 : 1 ≤ κ := by linarith
  have hlog := eventually_mul_log_add_pow_le_exp 1 (4 * C / E) (show (0 : ℝ) < 1 / 2 by norm_num)
  have hLev := Real.tendsto_log_atTop.eventually_ge_atTop (2 * Real.log (4 * Real.pi) + 4)
  filter_upwards [hev, hlog, hLev, eventually_ge_atTop (102 : ℝ)] with T hTev hTlog hLT hT102
  have hlog4π : 0 < Real.log (4 * Real.pi) := Real.log_pos (by nlinarith [Real.pi_gt_three])
  have hL0 : 0 < Real.log T := by linarith
  by_cases hbig : Real.log T / 4 < κ
  · refine le_trans (measure_mono (t := ∅) ?_) (by rw [measure_empty]; exact zero_le)
    rintro t ⟨-, s, h1, h2, -⟩
    have : κ / Real.log T ≤ 1 / 4 := by linarith
    rw [div_le_iff₀ hL0] at this
    linarith
  obtain ⟨hg1, hg2, hgJ⟩ := speiser_grid_facts hκ1 (not_lt.mp hbig)
  obtain ⟨J, hJ⟩ : ∃ J, J = Nat.log 2 ⌊Real.log T / (8 * κ)⌋₊ := ⟨_, rfl⟩
  rw [← hJ] at hg1 hg2 hgJ
  obtain ⟨κ₀, hκ₀def⟩ : ∃ κ₀, κ₀ = Real.log T / (24 * 2 ^ J) := ⟨_, rfl⟩
  rw [← hκ₀def] at hg1 hg2
  have hκ₀pos : 0 < κ₀ := by rw [hκ₀def]; positivity
  have htop : 2 ^ J * κ₀ / Real.log T = 1 / 24 := by rw [hκ₀def]; field_simp
  have hκ₀1 : κ₁ ≤ κ₀ := by linarith
  have hκ₀ε : 1 ≤ ε / 30 * κ₀ := by
    have h : 30 / ε ≤ κ₀ := by
      have : 180 / ε / 6 = 30 / ε := by ring
      linarith
    rw [div_le_iff₀ hε0] at h
    linarith
  have hRj : ∀ j ≤ J, 2 ^ j * κ₀ / Real.log T ≤ 1 / 16 := fun j hj => by
    have : (2 : ℝ) ^ j ≤ 2 ^ J := pow_le_pow_right₀ (by norm_num) hj
    have : 2 ^ j * κ₀ / Real.log T ≤ 2 ^ J * κ₀ / Real.log T := by gcongr
    linarith
  have hEκ : Real.exp (-(κ₀ * (ε / 30))) ≤ E := by
    rw [hE]; apply Real.exp_le_exp.mpr
    rw [hc]
    have : ε / 180 * κ = κ / 6 * (ε / 30) := by ring
    nlinarith
  refine (measure_mono (deriv_near_line_subset_scales hT102 hLT hε0 (by norm_num) hκ₀pos htop
    hg1 hg2)).trans ((volume_speiser_scales_le (by linarith) hC hε0 hε4 hκ₀1 hκ₀ε hgJ hRj hE0
    hEκ hTlog hTev).trans (ENNReal.ofReal_le_ofReal ?_))
  have hle : 2 * A0 + 1 / 4 ≤ Cf := by
    have : 2 * A0 + 2 ≤ Cf := by rw [hCf]; exact le_add_of_nonneg_right (Real.exp_pos _).le
    linarith
  have hT0 : 0 < T := by linarith
  have hTE : 0 ≤ T * E := by positivity
  have e1 : (2 * A0 + 1 / 4) * T * E = (2 * A0 + 1 / 4) * (T * E) := by ring
  have e2 : Cf * T * E = Cf * (T * E) := by ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right hle hTE

end RHTower
