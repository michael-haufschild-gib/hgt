import GaloisForLFunctions.RHTower.XiSliceSaddleStrip
import GaloisForLFunctions.RHTower.ZetaTypicalHeightLogDeriv

/-!
# Slice positivity at orders `≥ η log t` for almost every height

Let `c_n(t)` be the Taylor coefficients of `g_t(x) = ξ(½+x+it) ξ(½−x+it)` at `x = 0`. For every
`η > 0` and `δ > 0`, for all large `T`, the heights `t ∈ [T, 2T]` at which `c_{2k}(t) ≤ 0` for some
order `k ≥ η log t` form a set of measure at most `δT`
(`eventually_volume_xiSliceCoeff_nonpos_le`).

At a typical height (`zetaTypicalHeight η ε T t`, with `ε = η⁴/10⁸`) the saddle method of
`XiSliceSaddleStrip` runs with the saddle disc inside the critical strip:

* the slice product has no zero on `|w − 3/2| < 3/2 − η/4`, since `ζ` has none on the
  corresponding disc about `2 + it`;
* the Stirling comparison for `ξ'/ξ` holds with `C = 3 + 24(ε log T + 9)/η²` on
  `|w − 3/2| ≤ 3/2 − η`, from the typical bound for `ζ'/ζ`;
* on the arc, `|ζ| ≤ T^ε + 2` and at the saddle point `|ζ| ≥ e^{−12(ε log T + 9)/η}/3`, so the
  circle-decay law bounds the arc beyond the core by a negative power of `t`.

Orders `k ≥ ½ log t` are covered at every height by `exists_xiSliceCoeff_pos_above_quarter_log`.
-/

open Complex Real Metric MeasureTheory Set
open scoped ComplexOrder

namespace RHTower

noncomputable section

theorem xi_ne_zero_of_riemannZeta_ne_zero_offReal {s : ℂ} (him : s.im ≠ 0)
    (hζ : riemannZeta s ≠ 0) : xi s ≠ 0 := by
  rw [xi_eq_four_factors_offReal him]
  have hs0 : s ≠ 0 := by intro h; rw [h] at him; simp at him
  have hs1 : s - 1 ≠ 0 := by
    intro h; rw [sub_eq_zero.mp h] at him; simp at him
  have hπ : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
    refine Complex.cpow_ne_zero_iff.mpr ?_
    simp [Real.pi_ne_zero]
  have hΓ : Complex.Gamma (s / 2) ≠ 0 := by
    refine Complex.Gamma_ne_zero fun m h => him ?_
    have := congrArg Complex.im h
    simp at this
    linarith
  exact mul_ne_zero (div_ne_zero (mul_ne_zero hs0 hs1) two_ne_zero)
    (mul_ne_zero hπ (mul_ne_zero hΓ hζ))

namespace zetaTypicalHeight

variable {η ε T t : ℝ}

theorem norm_sub_two_add (w : ℂ) (t : ℝ) :
    ‖1 / 2 + w + (t : ℂ) * I - (2 + (t : ℂ) * I)‖ = ‖w - 3 / 2‖ := by
  congr 1; ring

theorem conj_slicePoint (w : ℂ) (t : ℝ) :
    1 / 2 + w - (t : ℂ) * I = (starRingEnd ℂ) (1 / 2 + (starRingEnd ℂ) w + (t : ℂ) * I) := by
  apply Complex.ext <;> simp; ring

theorem norm_conj_sub_three_halves (w : ℂ) :
    ‖(starRingEnd ℂ) w - 3 / 2‖ = ‖w - 3 / 2‖ := by
  have h32 : (starRingEnd ℂ) (3 / 2 : ℂ) = 3 / 2 := by
    rw [map_div₀, Complex.conj_ofNat, Complex.conj_ofNat]
  rw [← Complex.norm_conj, map_sub, Complex.conj_conj, h32]

/-- **Zero-free slice product at a typical height.** -/
theorem xiSliceProduct_ne_zero (h : zetaTypicalHeight η ε T t) (hη0 : 0 < η) (hT : 8 ≤ T)
    {w : ℂ} (hw : w ∈ ball (3 / 2 : ℂ) (3 / 2 - η / 4)) : xiSliceProduct t w ≠ 0 := by
  obtain ⟨-, hne, -, -⟩ := h.disc_hypotheses hη0 hT
  have ht := h.1
  have key : ∀ v : ℂ, ‖v - 3 / 2‖ < 3 / 2 - η / 4 → xi (1 / 2 + v + (t : ℂ) * I) ≠ 0 := by
    intro v hv
    have hmem : 1 / 2 + v + (t : ℂ) * I ∈ ball (2 + (t : ℂ) * I) (3 / 2 - η / 4) := by
      rw [mem_ball, dist_eq_norm, norm_sub_two_add]; exact hv
    have him : (1 / 2 + v + (t : ℂ) * I).im ≠ 0 := by
      have h1 := (abs_le.mp ((Complex.abs_im_le_norm (v - 3 / 2)).trans hv.le))
      simp only [Complex.sub_im] at h1
      norm_num at h1
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      norm_num
      intro h0
      linarith [ht.1]
    exact xi_ne_zero_of_riemannZeta_ne_zero_offReal him (hne _ hmem)
  rw [mem_ball, dist_eq_norm] at hw
  unfold xiSliceProduct
  have e : (1 / 2 : ℂ) - w + (t : ℂ) * I = 1 - (1 / 2 + w - (t : ℂ) * I) := by ring
  refine mul_ne_zero (key w hw) ?_
  rw [e, xi_one_sub, conj_slicePoint, xi_conj]
  exact (map_ne_zero _).mpr (key _ (by rw [norm_conj_sub_three_halves]; exact hw))

/-- **Stirling comparison at a typical height.** On `|w − 3/2| ≤ 3/2 − η`, both points
`½ + w ± it` satisfy `|ξ'/ξ(s) − ½ log(s/2)| ≤ 3 + 24(ε log T + 9)/η²`. -/
theorem stirling_le (h : zetaTypicalHeight η ε T t) (hη0 : 0 < η) (hη1 : η ≤ 1) (hT : 8 ≤ T)
    (hε : 0 ≤ ε) {w : ℂ} (hw : ‖w - 3 / 2‖ ≤ 3 / 2 - η) :
    ‖logDeriv xi (1 / 2 + w + (t : ℂ) * I) - Complex.log ((1 / 2 + w + (t : ℂ) * I) / 2) / 2‖
        ≤ 3 + 24 * (ε * Real.log T + 9) / η ^ 2
      ∧ ‖logDeriv xi (1 / 2 + w - (t : ℂ) * I) - Complex.log ((1 / 2 + w - (t : ℂ) * I) / 2) / 2‖
        ≤ 3 + 24 * (ε * Real.log T + 9) / η ^ 2 := by
  have ht := h.1
  have plus : ∀ v : ℂ, ‖v - 3 / 2‖ ≤ 3 / 2 - η →
      0 < (1 / 2 + v + (t : ℂ) * I).re ∧
      ‖logDeriv xi (1 / 2 + v + (t : ℂ) * I) - Complex.log ((1 / 2 + v + (t : ℂ) * I) / 2) / 2‖
        ≤ 3 + 24 * (ε * Real.log T + 9) / η ^ 2 := by
    intro v hv
    have h1 := abs_le.mp ((Complex.abs_re_le_norm (v - 3 / 2)).trans hv)
    have h2 := abs_le.mp ((Complex.abs_im_le_norm (v - 3 / 2)).trans hv)
    simp only [Complex.sub_re, Complex.sub_im] at h1 h2
    norm_num at h1 h2
    have hre : (1 / 2 + v + (t : ℂ) * I).re = 1 / 2 + v.re := by simp
    have him : (1 / 2 + v + (t : ℂ) * I).im = v.im + t := by simp
    have hre0 : 0 < (1 / 2 + v + (t : ℂ) * I).re := by rw [hre]; linarith
    refine ⟨hre0, ?_⟩
    have hs : ‖1 / 2 + v + (t : ℂ) * I - (2 + (t : ℂ) * I)‖ ≤ 3 / 2 - η := by
      rw [norm_sub_two_add]; exact hv
    have hB := h.norm_logDeriv_le hη0 hη1 hT hε hs
    have him0 : (1 / 2 + v + (t : ℂ) * I).im ≠ 0 := by rw [him]; linarith [ht.1]
    have hs4 : 4 ≤ ‖1 / 2 + v + (t : ℂ) * I‖ := by
      refine le_trans ?_ (Complex.abs_im_le_norm _)
      rw [him, abs_of_pos (by linarith [ht.1])]; linarith [ht.1]
    have hζ : riemannZeta (1 / 2 + v + (t : ℂ) * I) ≠ 0 :=
      h.ne_zero (by rw [hre]; linarith) (by rw [him]; rw [abs_le]; constructor <;> linarith)
    have := norm_logDeriv_xi_sub_half_log_le_of_zeta hre0 him0 hs4 hζ hB
    linarith
  refine ⟨(plus w hw).2, ?_⟩
  have hc := plus ((starRingEnd ℂ) w) (by rw [norm_conj_sub_three_halves]; exact hw)
  rw [conj_slicePoint, norm_logDeriv_xi_sub_half_log_conj hc.1]
  exact hc.2

/-- The Stirling hypothesis on the saddle disc `|w − R| ≤ η` for `2η ≤ R ≤ 5/4`. -/
theorem xiSliceStirling (h : zetaTypicalHeight η ε T t) (hη0 : 0 < η) (hη8 : η ≤ 1 / 8)
    (hT : 8 ≤ T) (hε : 0 ≤ ε) {R : ℝ} (hR : 2 * η ≤ R) (hR1 : R ≤ 5 / 4) :
    XiSliceStirling t (3 + 24 * (ε * Real.log T + 9) / η ^ 2) (closedBall (R : ℂ) η) := by
  intro w hw
  refine h.stirling_le hη0 (by linarith) hT hε ?_
  rw [mem_closedBall, dist_eq_norm] at hw
  calc ‖w - 3 / 2‖ = ‖(w - R) + ((R : ℂ) - 3 / 2)‖ := by ring_nf
    _ ≤ ‖w - R‖ + ‖(R : ℂ) - 3 / 2‖ := norm_add_le _ _
    _ ≤ η + (3 / 2 - R) := by
        gcongr
        have : (R : ℂ) - 3 / 2 = ((R - 3 / 2 : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
        linarith
    _ ≤ 3 / 2 - η := by linarith

/-- The ratio of the arc bound to the saddle lower bound at a typical height. -/
theorem ratio_sq_le (hη0 : 0 < η) (hT : 1 ≤ T) (hε : 0 ≤ ε) :
    ((T ^ ε + 2) / (Real.exp (-(12 * (ε * Real.log T + 9) / η)) / 3)) ^ 2
      ≤ 81 * Real.exp (216 / η) * T ^ (2 * ε + 24 * ε / η) := by
  have hT0 : 0 < T := by linarith
  have h1 : 1 ≤ T ^ ε := Real.one_le_rpow hT hε
  have hB : T ^ ε + 2 ≤ 3 * T ^ ε := by linarith
  have hx : Real.exp (12 * (ε * Real.log T + 9) / η) = Real.exp (108 / η) * T ^ (12 * ε / η) := by
    rw [Real.rpow_def_of_pos hT0, ← Real.exp_add]; congr 1; field_simp; ring
  have hq : (T ^ ε + 2) / (Real.exp (-(12 * (ε * Real.log T + 9) / η)) / 3)
      = 3 * (T ^ ε + 2) * Real.exp (12 * (ε * Real.log T + 9) / η) := by
    rw [Real.exp_neg]; field_simp
  have hle : (T ^ ε + 2) / (Real.exp (-(12 * (ε * Real.log T + 9) / η)) / 3)
      ≤ 9 * Real.exp (108 / η) * T ^ (ε + 12 * ε / η) := by
    rw [hq, hx, Real.rpow_add hT0]
    have : 0 ≤ Real.exp (108 / η) * T ^ (12 * ε / η) := by positivity
    nlinarith
  have h0 : 0 ≤ (T ^ ε + 2) / (Real.exp (-(12 * (ε * Real.log T + 9) / η)) / 3) := by positivity
  calc _ ≤ (9 * Real.exp (108 / η) * T ^ (ε + 12 * ε / η)) ^ 2 := pow_le_pow_left₀ h0 hle 2
    _ = 81 * Real.exp (108 / η) ^ 2 * (T ^ (ε + 12 * ε / η)) ^ 2 := by ring
    _ = 81 * Real.exp (216 / η) * T ^ (2 * ε + 24 * ε / η) := by
        have hE2 : Real.exp (108 / η) ^ 2 = Real.exp (216 / η) := by
          rw [sq, ← Real.exp_add]; congr 1; ring
        have hT2 : (T ^ (ε + 12 * ε / η)) ^ 2 = T ^ (2 * ε + 24 * ε / η) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]; congr 1; push_cast; ring
        rw [hE2, hT2]

/-- **Arc tail at a typical height.** For `2η ≤ R ≤ 5/4` and `θ₁ ≤ θ ≤ π/2`,
`|S(θ)| ≤ 81 e^{216/η} T^{2ε + 24ε/η} · e (2π)^{5/4} t^{−2ηθ₁²/5}`. -/
theorem norm_sliceArc_le (h : zetaTypicalHeight η ε T t) (hη0 : 0 < η) (hη8 : η ≤ 1 / 8)
    (hT : 56 ≤ T) (hε : 0 ≤ ε) (k : ℕ) {R θ₁ θ : ℝ} (hR : 2 * η ≤ R) (hR1 : R ≤ 5 / 4)
    (hθ₁ : 0 < θ₁) (hθ : θ₁ ≤ θ) (hθπ : θ ≤ Real.pi / 2) :
    ‖sliceArc t R k θ‖ ≤ 81 * Real.exp (216 / η) * T ^ (2 * ε + 24 * ε / η)
      * (Real.exp 1 * ((2 * Real.pi) ^ (5 / 4 : ℝ) * t ^ (-(2 * η * θ₁ ^ 2 / 5)))) := by
  have ht := h.1
  have ht56 : 56 ≤ t := by linarith [ht.1]
  have hR0 : 0 < R := by linarith
  have hθ0 : 0 ≤ θ := by linarith
  have hcos : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) hθπ
  set m₀ := Real.exp (-(12 * (ε * Real.log T + 9) / η)) / 3 with hm₀
  have hm₀0 : 0 < m₀ := by positivity
  have hz₀ : m₀ ≤ ‖riemannZeta (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
    refine h.norm_ge hη0 (by linarith) (by linarith) hε ?_
    have e : ((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I - (2 + (t : ℂ) * I) = ((R - 3 / 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have hzB : ∀ c : ℝ, |c| ≤ R → ‖riemannZeta (((1 / 2 + R * Real.cos θ : ℝ) : ℂ)
      + ((t + c : ℝ) : ℂ) * I)‖ ≤ T ^ ε + 2 := by
    intro c hc
    refine h.norm_le (by linarith) ?_ ?_
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
      nlinarith
    · simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, mul_zero, add_zero, mul_one, zero_add]
      rw [show t + c - t = c by ring]; linarith
  have hsinR : |R * Real.sin θ| ≤ R := by
    rw [abs_mul, abs_of_pos hR0]; exact mul_le_of_le_one_right hR0.le (Real.abs_sin_le_one θ)
  have hz₂ := hzB (-(R * Real.sin θ)) (by rwa [abs_neg])
  rw [← sub_eq_add_neg] at hz₂
  have hcirc := norm_xiSliceProduct_circle_le (by linarith) hR0.le (by linarith) hcos hm₀0 hz₀
    (hzB _ hsinR) hz₂
  have hθsq : 2 * η * θ₁ ^ 2 / 5 ≤ R * (1 - Real.cos θ) := by
    have hc5 := one_sub_cos_ge_sq_div_five (θ := θ)
      (by rw [abs_of_nonneg hθ0]; linarith [Real.pi_pos])
    have hθ2 : θ₁ ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ hθ₁.le hθ 2
    have h1c : 0 ≤ 1 - Real.cos θ := by linarith [Real.cos_le_one θ]
    calc 2 * η * θ₁ ^ 2 / 5 ≤ 2 * η * (θ ^ 2 / 5) := by nlinarith
      _ ≤ 2 * η * (1 - Real.cos θ) := by nlinarith
      _ ≤ R * (1 - Real.cos θ) := mul_le_mul_of_nonneg_right hR h1c
  have hdR : 2 * η * θ₁ ^ 2 / 5 ≤ 5 / 4 :=
    hθsq.trans ((mul_le_of_le_one_right hR0.le (by linarith)).trans hR1)
  have hexpX := circle_decay_exp_le (t := t) (R₁ := 5 / 4) (d := 2 * η * θ₁ ^ 2 / 5) (by linarith) hR0.le
    hR1 hcos hθsq hdR
  have hgR : 0 < ‖xiSliceProduct t (R : ℂ)‖ := by
    rw [norm_xiSliceProduct_real]
    refine pow_pos (norm_pos_iff.mpr (xi_ne_zero_of_riemannZeta_ne_zero_offReal ?_ ?_)) 2
    · simp; linarith [ht.1]
    · refine h.ne_zero ?_ ?_
      · simp; linarith
      · simp
  have hratio := ratio_sq_le (T := T) (ε := ε) hη0 (by linarith) hε
  rw [norm_sliceArc_eq, div_le_iff₀ hgR]
  calc ‖xiSliceProduct t ((R : ℂ) * Complex.exp ((θ : ℂ) * I))‖
      ≤ _ := hcirc
    _ ≤ ‖xiSliceProduct t (R : ℂ)‖ * (81 * Real.exp (216 / η) * T ^ (2 * ε + 24 * ε / η))
        * (Real.exp 1 * ((2 * Real.pi) ^ (5 / 4 : ℝ) * t ^ (-(2 * η * θ₁ ^ 2 / 5)))) := by
        gcongr
    _ = _ := by ring

end zetaTypicalHeight

/-! ## Assembly -/

/-- The linear budget of the saddle in `u = log t`: with `C ≤ 3ηu/10⁸ + C₀` and
`u ≥ 1000 (C₀ + 5)/η`, the saddle range, slope and disc conditions hold. -/
theorem slice_strip_budget {η C₀ C u : ℝ} (hη0 : 0 < η) (hη8 : η ≤ 1 / 8) (hC₀ : 0 ≤ C₀)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 * η * u / 10 ^ 8 + C₀) (hu : 1000 * (C₀ + 5) / η ≤ u) :
    2 * C ≤ u ∧ 5 * Real.log 2 + 10 * C ≤ u
      ∧ Real.log 2 + 2 * C + 5 / 4 * (Real.log 4 + Real.pi + 4 * C) / η ≤ u / 10
      ∧ η * (Real.log (3 / 2) + Real.pi / 2 + 2 * C) + 5 / 4 * (Real.log 4 + Real.pi + 4 * C)
        ≤ η * u := by
  have hηu : 1000 * (C₀ + 5) ≤ η * u := by
    rw [div_le_iff₀ hη0] at hu; linarith
  have hu0 : 0 ≤ u := by
    have : 0 ≤ 1000 * (C₀ + 5) / η := by positivity
    linarith
  have hl2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hl4 : Real.log 4 < 2 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [this]; linarith
  have hl32 : Real.log (3 / 2) < 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 2); linarith
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpi := Real.pi_lt_d2
  have hηuC : η * u ≤ u / 8 := by nlinarith
  have hCu : C ≤ u / 10 ^ 8 + C₀ := by nlinarith
  have hηC : η * C ≤ 3 * η * u / 10 ^ 8 + C₀ / 8 := by nlinarith
  have hCη : C ≤ 3 * η * u / 10 ^ 8 + C₀ := hC
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · rw [show Real.log 2 + 2 * C + 5 / 4 * (Real.log 4 + Real.pi + 4 * C) / η
        = (η * (Real.log 2 + 2 * C) + 5 / 4 * (Real.log 4 + Real.pi + 4 * C)) / η by
        field_simp]
    rw [div_le_iff₀ hη0]
    nlinarith
  · nlinarith

/-- The Stirling constant at a typical height is at most `3ηu/10⁸ + C₀` with `u = log t`. -/
theorem stirling_const_le {η T t : ℝ} (hη0 : 0 < η) (hη8 : η ≤ 1 / 8) (hT1 : 1 ≤ T)
    (hTt : T ≤ t) :
    3 + 24 * (η ^ 4 / 10 ^ 8 * Real.log T + 9) / η ^ 2
      ≤ 3 * η * Real.log t / 10 ^ 8 + (3 + 216 / η ^ 2) := by
  have hlogT : Real.log T ≤ Real.log t := Real.log_le_log (by linarith) hTt
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have e : 3 + 24 * (η ^ 4 / 10 ^ 8 * Real.log T + 9) / η ^ 2
      = (3 + 216 / η ^ 2) + 24 * η ^ 2 * Real.log T / 10 ^ 8 := by
    field_simp; ring
  rw [e]
  have h1 : 24 * η ^ 2 ≤ 3 * η := by nlinarith
  have h2 : 24 * η ^ 2 * Real.log T ≤ 3 * η * Real.log t :=
    (mul_le_mul_of_nonneg_right h1 hlogT0).trans
      (mul_le_mul_of_nonneg_left hlogT (by positivity))
  linarith

/-- **The saddle data at a typical height.** For `2η log t ≤ k ≤ ½ log t` and
`log t ≥ 1000(C₀ + 5)/η`, `C₀ = 3 + 216/η²`, the saddle radius of the order `2k` lies in
`[2η, 5/4]`, the slope lies in `[(9/10) log t, 2 log t]`, and the disc constant is at most
`2η log t`. -/
theorem typical_saddle_data {η T t : ℝ} {k : ℕ} (hη0 : 0 < η) (hη8 : η ≤ 1 / 8) (hT : 56 ≤ T)
    (htyp : zetaTypicalHeight η (η ^ 4 / 10 ^ 8) T t)
    (hklo : 2 * η * Real.log t ≤ k) (hkhi : (k : ℝ) ≤ Real.log t / 2)
    (hbud : 1000 * ((3 + 216 / η ^ 2) + 5) / η ≤ Real.log t) :
    ∃ R : ℝ, 2 * η ≤ R ∧ R ≤ 5 / 4
      ∧ (HTGeometry.scaledLogDeriv (xiSliceProduct t) R).re = 2 * (k : ℝ)
      ∧ 9 / 10 * Real.log t ≤ (deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re
      ∧ (deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re ≤ 2 * Real.log t
      ∧ xiSliceDiscConstantStrip η (3 + 24 * (η ^ 4 / 10 ^ 8 * Real.log T + 9) / η ^ 2) t R
        ≤ 2 * η * Real.log t := by
  have ht := htyp.1
  have hTt : T ≤ t := ht.1
  have ht0 : 0 < t := by linarith
  set C := 3 + 24 * (η ^ 4 / 10 ^ 8 * Real.log T + 9) / η ^ 2 with hCdef
  have hC0 : 0 ≤ C := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T); positivity
  obtain ⟨b1, b2, b3, b4⟩ := slice_strip_budget hη0 hη8 (by positivity) hC0
    (stirling_const_le hη0 hη8 (by linarith) hTt) hbud
  set u := Real.log t with hudef
  set U : Set ℂ := ball (3 / 2 : ℂ) (3 / 2 - η / 4) with hUdef
  have hU : ∀ w ∈ U, xiSliceProduct t w ≠ 0 := fun w hw =>
    htyp.xiSliceProduct_ne_zero hη0 (by linarith) hw
  have hnR : ∀ R : ℝ, R ≤ 3 / 2 → ‖(R : ℂ) - 3 / 2‖ = 3 / 2 - R := by
    intro R hR
    have e : (R : ℂ) - 3 / 2 = ((R - 3 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  have hIcc : ∀ R ∈ Icc (2 * η) (5 / 4), (R : ℂ) ∈ U := by
    intro R hR
    rw [hUdef, mem_ball, dist_eq_norm, hnR R (by linarith [hR.2])]
    linarith [hR.1]
  have hEreal : ∀ R ∈ Icc (2 * η) (5 / 4), ‖logDeriv xi (1 / 2 + (R : ℂ) + (t : ℂ) * I)
      - Complex.log ((1 / 2 + (R : ℂ) + (t : ℂ) * I) / 2) / 2‖ ≤ C := by
    intro R hR
    refine (htyp.stirling_le hη0 (by linarith) (by linarith) (by positivity) ?_).1
    rw [hnR R (by linarith [hR.2])]; linarith [hR.1]
  have hlog2 : Real.log (t / 2) = u - Real.log 2 := by
    rw [Real.log_div ht0.ne' (by norm_num)]
  have hlo : 2 * η * (Real.log t + 2 * C) ≤ 2 * (k : ℝ) := by
    rw [← hudef]
    have := mul_le_mul_of_nonneg_left b1 hη0.le
    linarith
  have hhi : 2 * (k : ℝ) ≤ 5 / 4 * (Real.log (t / 2) - 2 * C) := by
    rw [hlog2]; linarith
  obtain ⟨R, ⟨hRa, hRb⟩, hsad⟩ := exists_saddle_radius_strip (U := U) (by linarith)
    (by positivity) (by linarith) (by linarith) hU hIcc hEreal hlo hhi
  have hball : closedBall (R : ℂ) η ⊆ U := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    rw [hUdef, mem_ball, dist_eq_norm]
    have h1 : ‖w - 3 / 2‖ ≤ ‖w - R‖ + ‖(R : ℂ) - 3 / 2‖ := by
      have := norm_add_le (w - R) ((R : ℂ) - 3 / 2)
      rwa [show w - R + ((R : ℂ) - 3 / 2) = w - 3 / 2 by ring] at this
    rw [hnR R (by linarith)] at h1
    linarith
  have hS := htyp.xiSliceStirling hη0 hη8 (by linarith) (by positivity) hRa hRb
  rw [← hCdef] at hS
  obtain ⟨hF₁lo, hF₁hi⟩ := xiSlice_saddleSlope_bounds_strip isOpen_ball hU hball hη0
    (by linarith) (by linarith) (by linarith) (by linarith) hS
  have hq0 : 0 ≤ Real.log 4 + Real.pi + 4 * C := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); positivity
  have hRq : R * (Real.log 4 + Real.pi + 4 * C) / η
      ≤ 5 / 4 * (Real.log 4 + Real.pi + 4 * C) / η :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hRb hq0) hη0.le
  rw [hlog2] at hF₁lo
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨R, hRa, hRb, hsad, by linarith, by linarith, ?_⟩
  unfold xiSliceDiscConstantStrip
  have e : Real.log (3 * t / 2) = Real.log (3 / 2) + u := by
    rw [show 3 * t / 2 = 3 / 2 * t by ring, Real.log_mul (by norm_num) ht0.ne']
  rw [e]
  have h3 : R * (Real.log 4 + Real.pi + 4 * C) ≤ 5 / 4 * (Real.log 4 + Real.pi + 4 * C) :=
    mul_le_mul_of_nonneg_right hRb hq0
  linarith

/-- **The tail at a typical height**, absorbed into a negative power of `t`: with
`c = ηθ₁²/5` and `2ε + 24ε/η ≤ c`, `|S(θ)| ≤ 2A t^{−c}` for `θ₁ ≤ θ ≤ π/2`. -/
theorem typical_tail_le {η T t R θ₁ c A : ℝ} (k : ℕ) (hη0 : 0 < η) (hη8 : η ≤ 1 / 8)
    (hT : 56 ≤ T) (htyp : zetaTypicalHeight η (η ^ 4 / 10 ^ 8) T t) (hRa : 2 * η ≤ R)
    (hRb : R ≤ 5 / 4) (hθ₁0 : 0 < θ₁) (hcdef : c = η * θ₁ ^ 2 / 5)
    (hAdef : A = 81 * Real.exp (216 / η) * (Real.exp 1 * (2 * Real.pi) ^ (5 / 4 : ℝ)))
    (hεc : 2 * (η ^ 4 / 10 ^ 8) + 24 * (η ^ 4 / 10 ^ 8) / η ≤ c) :
    ∀ θ : ℝ, θ₁ ≤ θ → θ ≤ Real.pi / 2 → ‖sliceArc t R k θ‖ ≤ 2 * A * t ^ (-c) := by
  intro θ hθ hθπ
  have ht := htyp.1
  have hTt : T ≤ t := ht.1
  have ht0 : 0 < t := by linarith
  have hA0 : 0 < A := by rw [hAdef]; positivity
  have h := htyp.norm_sliceArc_le hη0 hη8 hT (by positivity) k hRa hRb hθ₁0 hθ hθπ
  set x := 2 * (η ^ 4 / 10 ^ 8) + 24 * (η ^ 4 / 10 ^ 8) / η with hx
  have hx0 : 0 ≤ x := by positivity
  have hTx : T ^ x ≤ t ^ x := Real.rpow_le_rpow (by linarith) hTt hx0
  have e2c : 2 * η * θ₁ ^ 2 / 5 = 2 * c := by rw [hcdef]; ring
  rw [e2c] at h
  have hpow : t ^ x * t ^ (-(2 * c)) ≤ t ^ (-c) := by
    rw [← Real.rpow_add ht0]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hAt : 0 ≤ t ^ (-c) := by positivity
  calc ‖sliceArc t R k θ‖
      ≤ 81 * Real.exp (216 / η) * T ^ x
        * (Real.exp 1 * ((2 * Real.pi) ^ (5 / 4 : ℝ) * t ^ (-(2 * c)))) := h
    _ ≤ 81 * Real.exp (216 / η) * t ^ x
        * (Real.exp 1 * ((2 * Real.pi) ^ (5 / 4 : ℝ) * t ^ (-(2 * c)))) := by gcongr
    _ = A * (t ^ x * t ^ (-(2 * c))) := by rw [hAdef]; ring
    _ ≤ A * t ^ (-c) := mul_le_mul_of_nonneg_left hpow hA0.le
    _ ≤ 2 * A * t ^ (-c) := by linarith [mul_nonneg hA0.le hAt]

/-- The exponent budget `2ε + 24ε/η ≤ ηθ₁²/5` for `ε = η⁴/10⁸`, `θ₁ = η/625`. -/
theorem slice_exponent_budget {η : ℝ} (hη0 : 0 < η) (hη8 : η ≤ 1 / 8) :
    2 * (η ^ 4 / 10 ^ 8) + 24 * (η ^ 4 / 10 ^ 8) / η ≤ η * (η / 625) ^ 2 / 5 := by
  have h1 : 2 * (η ^ 4 / 10 ^ 8) + 24 * (η ^ 4 / 10 ^ 8) / η = η ^ 3 * (2 * η + 24) / 10 ^ 8 := by
    field_simp
  rw [h1]
  have h2 : η * (η / 625) ^ 2 / 5 = η ^ 3 / 1953125 := by ring
  rw [h2]
  have : 2 * η + 24 ≤ 25 := by linarith
  have hη3 : 0 < η ^ 3 := by positivity
  rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
  nlinarith

/-- **Positivity at typical heights.** For `0 < η ≤ 1/8` there is `T₀` such that at every height
`t` that is typical for `(η, η⁴/10⁸)` at a scale `T ≥ T₀`, `c_{2k}(t) > 0` for all orders
`2η log t ≤ k ≤ ½ log t`. -/
theorem exists_xiSliceCoeff_pos_of_typical {η : ℝ} (hη0 : 0 < η) (hη8 : η ≤ 1 / 8) :
    ∃ T₀ : ℝ, 56 ≤ T₀ ∧ ∀ T t : ℝ, T₀ ≤ T → zetaTypicalHeight η (η ^ 4 / 10 ^ 8) T t →
      ∀ k : ℕ, 2 * η * Real.log t ≤ k → (k : ℝ) ≤ Real.log t / 2 →
        0 < xiSliceCoeff t (2 * k) := by
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 5 / 4 / (2 * η) := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by rw [hKdef, le_div_iff₀ (by positivity)]; linarith
  have hθ₁η : 1 / (1000 * K) = η / 625 := by rw [hKdef]; field_simp; ring
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = η * (1 / (1000 * K)) ^ 2 / 5 := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hcdef]; positivity
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ,
      A = 81 * Real.exp (216 / η) * (Real.exp 1 * (2 * Real.pi) ^ (5 / 4 : ℝ)) := ⟨_, rfl⟩
  have hA0 : 0 < A := by rw [hAdef]; positivity
  have hεc : 2 * (η ^ 4 / 10 ^ 8) + 24 * (η ^ 4 / 10 ^ 8) / η ≤ c := by
    rw [hcdef, hθ₁η]; exact slice_exponent_budget hη0 hη8
  have e1 := (tendsto_order.1 tendsto_rpow_half_mul_exp_neg_fifth_root).2 50 (by norm_num)
  have e3 := (tendsto_order.1 (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 5))).2
    (1 / (1000 * K)) (by positivity)
  have e4 := (tendsto_order.1 (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 5))).2
    (3 / (2 * (1 + 128 * K))) (by positivity)
  obtain ⟨Λ₀, hΛ₀⟩ := Filter.eventually_atTop.mp (e1.and (e3.and e4))
  have e5 := (tendsto_order.1 (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2) c hc0)).2
    (1 / (10 * Real.pi * A * (5 / 4 : ℝ) ^ (1 / 2 : ℝ))) (by positivity)
  obtain ⟨U₅, hU₅⟩ := Filter.eventually_atTop.mp e5
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ,
      L = 1000 * ((3 + 216 / η ^ 2) + 5) / η + (|Λ₀| + 1) / (2 * η) + |U₅| + 1 := ⟨_, rfl⟩
  have hB0 : 0 ≤ 1000 * ((3 + 216 / η ^ 2) + 5) / η := by positivity
  have hB1 : 0 ≤ (|Λ₀| + 1) / (2 * η) := by positivity
  have hU₅a := abs_nonneg U₅
  refine ⟨max 56 (Real.exp L), le_max_left _ _, ?_⟩
  intro T t hT htyp k hklo hkhi
  have hT56 : 56 ≤ T := le_trans (le_max_left _ _) hT
  have hTt : T ≤ t := htyp.1.1
  have ht0 : 0 < t := by linarith
  have hLu : L ≤ Real.log t := by
    have h1 : Real.exp L ≤ t := le_trans (le_trans (le_max_right _ _) hT) hTt
    have h2 := Real.log_le_log (Real.exp_pos L) h1
    rwa [Real.log_exp] at h2
  have hu0 : 0 < Real.log t := by linarith
  obtain ⟨R, hRa, hRb, hsad, hF₁lo, hF₁hi, hKd⟩ :=
    typical_saddle_data hη0 hη8 hT56 htyp hklo hkhi (by linarith)
  have hball : closedBall (R : ℂ) η ⊆ ball (3 / 2 : ℂ) (3 / 2 - η / 4) := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    rw [mem_ball, dist_eq_norm]
    have h1 : ‖w - 3 / 2‖ ≤ ‖w - R‖ + ‖(R : ℂ) - 3 / 2‖ := by
      have := norm_add_le (w - R) ((R : ℂ) - 3 / 2)
      rwa [show w - R + ((R : ℂ) - 3 / 2) = w - 3 / 2 by ring] at this
    have e : (R : ℂ) - 3 / 2 = ((R - 3 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)] at h1
    linarith
  have htail := typical_tail_le k hη0 hη8 hT56 htyp hRa hRb (by positivity) hcdef hAdef hεc
  have hΛlo : 2 * η * Real.log t ≤ R * Real.log t := mul_le_mul_of_nonneg_right hRa hu0.le
  have hΛhi : R * Real.log t ≤ 5 / 4 * Real.log t := mul_le_mul_of_nonneg_right hRb hu0.le
  have hΛbig : max Λ₀ 1 ≤ R * Real.log t := by
    have h1 : (|Λ₀| + 1) / (2 * η) ≤ Real.log t := by linarith
    rw [div_le_iff₀ (by positivity)] at h1
    have := le_abs_self Λ₀
    exact max_le (by linarith) (by linarith [abs_nonneg Λ₀])
  obtain ⟨hE1, hE3, hE4⟩ := hΛ₀ (R * Real.log t) (le_trans (le_max_left _ _) hΛbig)
  have hEt := tail_budget_le hA0 (by norm_num : (0 : ℝ) < 5 / 4) ht0 rfl hu0
    (by linarith [le_max_right Λ₀ 1]) hΛhi (hU₅ (Real.log t) (by linarith [le_abs_self U₅])).le
  exact xiSliceCoeff_pos_of_saddle_strip isOpen_ball
    (fun w hw => htyp.xiSliceProduct_ne_zero hη0 (by linarith) hw) hball
    (htyp.xiSliceStirling hη0 hη8 (by linarith) (by positivity) hRa hRb)
    (by have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T); positivity) hη0 hη8
    (by linarith : 2 * η ≤ 5 / 4) hKdef (by linarith) hu0 hRa hRb (by linarith) hsad hF₁lo
    hF₁hi hKd htail (le_trans (le_max_right _ _) hΛbig) hE1 hE3 hE4 hEt

/-- **Slice positivity at orders `≥ η log t` for almost every height.** For every `η > 0` and
`δ > 0`, for all large `T`, the heights `t ∈ [T, 2T]` at which `c_{2k}(t)` fails to be positive for
some order `k ≥ η log t` have measure at most `δT`. -/
theorem eventually_volume_xiSliceCoeff_nonpos_le {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    ∀ᶠ T in Filter.atTop,
      volume {t | t ∈ Icc T (2 * T) ∧
        ∃ k : ℕ, η * Real.log t ≤ k ∧ ¬ 0 < xiSliceCoeff t (2 * k)} ≤ ENNReal.ofReal (δ * T) := by
  set η' := min (η / 2) (1 / 8) with hη'def
  have hη'0 : 0 < η' := lt_min (by linarith) (by norm_num)
  have hη'8 : η' ≤ 1 / 8 := min_le_right _ _
  have hη'η : 2 * η' ≤ η := by have := min_le_left (η / 2) (1 / 8); linarith
  have hε0 : 0 < η' ^ 4 / 10 ^ 8 := by positivity
  have hε1 : η' ^ 4 / 10 ^ 8 ≤ 1 := by
    have : η' ^ 4 ≤ 1 := pow_le_one₀ hη'0.le (by linarith)
    rw [div_le_one (by norm_num)]; linarith
  obtain ⟨T₀, -, hpos⟩ := exists_xiSliceCoeff_pos_of_typical hη'0 hη'8
  obtain ⟨K₁, hK₁⟩ := exists_xiSliceCoeff_pos_above_quarter_log (ε := 1 / 4) (by norm_num)
  filter_upwards [eventually_volume_not_zetaTypicalHeight_le hη'0 hε0 hε1 hδ,
    Filter.eventually_ge_atTop T₀, Filter.eventually_ge_atTop (Real.exp (2 * |K₁|)),
    Filter.eventually_ge_atTop 1] with T hvol hT₀ hTK hT1
  refine le_trans (measure_mono ?_) hvol
  rintro t ⟨ht, k, hk, hneg⟩
  refine ⟨ht, fun htyp => hneg ?_⟩
  have hTt : T ≤ t := ht.1
  have hlogt : 2 * |K₁| ≤ Real.log t := by
    have h := Real.log_le_log (Real.exp_pos _) (le_trans hTK hTt)
    rwa [Real.log_exp] at h
  have hlog0 : 0 ≤ Real.log t := by linarith [abs_nonneg K₁]
  rcases le_or_gt (k : ℝ) (Real.log t / 2) with hkhi | hkhi
  · refine hpos T t hT₀ htyp k ?_ hkhi
    have := mul_le_mul_of_nonneg_right hη'η hlog0
    linarith
  · refine hK₁ t (by linarith) k (max_le ?_ ?_)
    · linarith [le_abs_self K₁]
    · linarith

end

end RHTower
