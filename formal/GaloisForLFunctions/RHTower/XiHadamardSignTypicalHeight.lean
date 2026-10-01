import GaloisForLFunctions.RHTower.SpeiserTypicalHeightDensity
import GaloisForLFunctions.RHTower.SpeiserLocalDisk
import GaloisForLFunctions.RHTower.LateralWindingFloor

/-!
# The Hadamard sign `Re(ξ'/ξ) > 0` near the line at typical heights

RH is equivalent to `Re(ξ'/ξ)(s) ≥ 0` on `Re s > 1/2`. On the strip `ξ = archFactor · ζ`, so
`ξ'/ξ = archFactor'/archFactor + ζ'/ζ`, and the archimedean part has real part at least the winding
floor `stripFloor σ τ ≈ ½ log(τ/2π)` (`stripWindingRate_ge`). Hence at a height `t` with scale data
`ZetaLogDerivScaleData t R B`, every `s` in the right box `1/2 + 3R/4 ≤ Re s ≤ 1/2 + 6R`,
`|Im s − t| ≤ 6R` with `B < stripFloor (Re s) (Im s)` has `ξ(s) ≠ 0` and `Re(ξ'/ξ)(s) > 0`
(`xi_ne_zero_and_re_logDeriv_pos_rightBox`).

On the dyadic grid pinned at `R = 1/24`, the exponential scale-data theorem gives: there are
`C, c > 0` such that for every `κ` and all large `T`, the heights `t ∈ [T, 2T]` within `κ/log T` of a
point `s` with `1/2 + κ/log T ≤ Re s ≤ 3/4` where the Hadamard sign fails have measure
`≤ C T e^{−cκ}` (`exists_volume_hadamardSign_fail_near_line_le`).
-/

noncomputable section

open Complex Set MeasureTheory Filter

namespace RHTower

/-- The winding floor exceeds `log(τ/2π)/2 − 1/25` for `τ ≥ 50` and `σ ≥ 0`. -/
theorem stripFloor_ge_half_log_sub {σ τ : ℝ} (hσ0 : 0 ≤ σ) (hτ : 50 ≤ τ) :
    Real.log (τ / (2 * Real.pi)) / 2 - 1 / 25 ≤ stripFloor σ τ := by
  unfold stripFloor
  have hτ0 : 0 < τ := by linarith
  have hπ := Real.pi_lt_d2
  have h1 : 4 / τ ^ (2 : ℕ) ≤ 4 / 2500 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num); nlinarith
  have h2 : Real.pi / τ ≤ 3.15 / 50 := by
    rw [div_le_div_iff₀ hτ0 (by norm_num)]; nlinarith [Real.pi_pos]
  have h3 : (1 - σ) / τ ^ (2 : ℕ) ≤ 1 / 2500 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  linarith

/-- **Hadamard sign on the right box.** -/
theorem xi_ne_zero_and_re_logDeriv_pos_rightBox {t R B : ℝ}
    (hdata : ZetaLogDerivScaleData t R B) (hR : 0 < R) (hR16 : R ≤ 1 / 16)
    {s : ℂ} (h1 : 1 / 2 + 3 * R / 4 ≤ s.re) (h2 : s.re ≤ 1 / 2 + 6 * R) (h3 : |s.im - t| ≤ 6 * R)
    (hs : 0 < s.im) (hB : B < stripFloor s.re s.im) :
    xi s ≠ 0 ∧ 0 < (logDeriv xi s).re := by
  have hre0 : 0 < s.re := by linarith
  have hre1 : s.re < 1 := by linarith
  have hζ : riemannZeta s ≠ 0 := by
    intro h0
    have := hdata.zeroFree s h0 (by linarith)
    linarith
  obtain ⟨hxi, hlog⟩ := logDeriv_xi_eq_archFactor_add_of_strip hre0 hre1 hζ
  refine ⟨hxi, ?_⟩
  have hsP : s = stripPt s.re s.im := by
    apply Complex.ext <;> simp [stripPt]
  have harch : stripFloor s.re s.im ≤ (logDeriv archFactor s).re := by
    have := stripWindingRate_ge hre0 hre1.le hs
    rw [stripWindingRate, stripWinding, ← hsP] at this
    rw [logDeriv_apply, (hasDerivAt_archFactor_of_re_pos hre0).deriv]
    exact this
  have hBs : ‖logDeriv riemannZeta s‖ ≤ B := hdata.logDeriv s (by linarith) h2 h3
  have hζre := (abs_le.mp ((Complex.abs_re_le_norm _).trans hBs)).1
  rw [hlog, Complex.add_re]
  linarith

/-- Covering of the near-line right region by the right boxes of the grid `2^j κ₀/log T`,
`j ≤ J`: outside the union of the scale-data failures, the Hadamard sign holds on
`1/2 + κ/log T ≤ Re s ≤ 3/4` within `κ/log T` of the height. -/
theorem hadamardSign_fail_subset_scales {T κ ε κ₀ : ℝ} {J : ℕ} (hT : 102 ≤ T)
    (hLT : 2 * Real.log (4 * Real.pi) + 4 ≤ Real.log T) (hε0 : 0 < ε) (hε : ε ≤ 1 / 4)
    (hκ₀ : 0 < κ₀) (htop : 2 ^ J * κ₀ / Real.log T = 1 / 24) (hg1 : κ / 6 ≤ κ₀)
    (hg2 : κ₀ ≤ 4 * κ / 3) :
    {t | t ∈ Icc T (2 * T) ∧ ∃ s : ℂ, 1 / 2 + κ / Real.log T ≤ s.re ∧ s.re ≤ 3 / 4 ∧
        |s.im - t| ≤ κ / Real.log T ∧ ¬ (xi s ≠ 0 ∧ 0 < (logDeriv xi s).re)} ⊆
      ⋃ j ∈ Finset.range (J + 1), {t | t ∈ Icc T (2 * T) ∧
        ¬ ZetaLogDerivScaleData t (2 ^ j * κ₀ / Real.log T) (ε * Real.log T)} := by
  have hT0 : 0 < T := by linarith
  have hlog4π : 0 < Real.log (4 * Real.pi) := Real.log_pos (by nlinarith [Real.pi_gt_three])
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log T := ⟨_, rfl⟩
  rw [← hLdef] at hLT htop ⊢
  have hL0 : 0 < L := by linarith
  rintro t ⟨ht, s, h1, h2, h3, hfail⟩
  have hd1 : 3 * (κ₀ / L) / 4 ≤ s.re - 1 / 2 := by
    have : κ₀ / L ≤ 4 * κ / 3 / L := div_le_div_of_nonneg_right hg2 hL0.le
    have e : 3 * (4 * κ / 3 / L) / 4 = κ / L := by ring
    linarith
  obtain ⟨j, hjJ, hj1, hj2⟩ := exists_speiser_grid_scale hL0 hκ₀ htop hd1 (by linarith)
  refine Set.mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr (by omega), ht, fun hdata => hfail ?_⟩
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
  have hB : ε * L < stripFloor s.re s.im := by
    have hfl := stripFloor_ge_half_log_sub (σ := s.re) (τ := s.im) (by linarith) (by linarith)
    have h4 : Real.log (T / (4 * Real.pi)) ≤ Real.log (s.im / (2 * Real.pi)) := by
      apply Real.log_le_log (by positivity)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [Real.pi_pos]
    rw [Real.log_div hT0.ne' (by positivity), ← hLdef] at h4
    have : ε * L ≤ L / 4 := by nlinarith
    linarith
  exact xi_ne_zero_and_re_logDeriv_pos_rightBox hdata (by positivity) (hRj.trans (by norm_num))
    (by linarith) (by linarith) (h3.trans hRlow) (by linarith) hB

/-- **Hadamard sign near the line, exponential rate.** There are `C, c > 0` such that for every `κ`
and all large `T`, the heights `t ∈ [T, 2T]` within `κ/log T` of a point `s` with
`1/2 + κ/log T ≤ Re s ≤ 3/4` and `ξ(s) = 0` or `Re(ξ'/ξ)(s) ≤ 0` have measure at most
`C T e^{−cκ}`. -/
theorem exists_volume_hadamardSign_fail_near_line_le :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ κ : ℝ, ∀ᶠ T in atTop,
      volume {t | t ∈ Icc T (2 * T) ∧ ∃ s : ℂ, 1 / 2 + κ / Real.log T ≤ s.re ∧ s.re ≤ 3 / 4 ∧
          |s.im - t| ≤ κ / Real.log T ∧ ¬ (xi s ≠ 0 ∧ 0 < (logDeriv xi s).re)} ≤
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
  refine (measure_mono (hadamardSign_fail_subset_scales hT102 hLT hε0 (by norm_num) hκ₀pos htop
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
