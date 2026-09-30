import GaloisForLFunctions.RHTower.XiSliceTypicalOrderPositivity
import GaloisForLFunctions.RHTower.ZetaTypicalScaleLogDeriv

/-!
# Slice positivity at orders `≥ C log log t` for almost every height

At a scale `0 < R ≤ 1/16` and a height `t`, *scale data* (`ZetaScaleData t R M W`) are: no zero
with `Re ≥ ½ + R/10` within height `3R`, `|ζ| ≤ M` on `½ ≤ Re ≤ ½ + 6R`, `|Im − t| ≤ 6R`, and
`log|ζ| ≥ −W` at `½ + 3R + it`. With `B = log M + W + 1`, Borel–Carathéodory at scale `R` gives the
Stirling comparison with `C = 3 + 58B/R` on `|w − 3R| ≤ 2.3R`, and the strip saddle
(`xiSliceCoeff_pos_of_saddle_strip`, disc radius `R/4`, saddle radius in `[R, 5R]`) proves
`c_{2k}(t) > 0` for every order `k` with `R log t ≤ k ≤ 2R log t` and `k ≥ 10¹¹ B`
(`exists_xiSliceCoeff_pos_of_scaleData`).

Scale data hold at almost every height simultaneously on the dyadic scales `R_j = 2^j k₀/log T`
with `M_j = V 2^j (4T)^{cR_j}(1 + log 4T)²`, `W_j = W₀ 2^{j/2}`, `W₀ ≍ log log T`
(`ZetaTypicalScaleBounds`), which gives the density statement for orders `≥ C_δ log log t`
(`eventually_volume_xiSliceCoeff_nonpos_loglog_le`).
-/

open Complex Real Metric MeasureTheory Set
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- **Scale data at height `t`.** -/
structure ZetaScaleData (t R M W : ℝ) : Prop where
  zeroFree : ∀ w : ℂ, riemannZeta w = 0 → 1 / 2 + R / 10 ≤ w.re → 3 * R < |w.im - t|
  upper : ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 1 / 2 + 6 * R → |z.im - t| ≤ 6 * R →
    ‖riemannZeta z‖ ≤ M
  lower : -W ≤ Real.log ‖riemannZeta (scaleCentre R t)‖

namespace ZetaScaleData

variable {t R M W : ℝ}

theorem slicePoint_sub_centre (R t : ℝ) (w : ℂ) :
    1 / 2 + w + (t : ℂ) * I - scaleCentre R t = w - ((3 * R : ℝ) : ℂ) := by
  simp only [scaleCentre]; push_cast; ring

theorem norm_conj_sub_real (w : ℂ) (a : ℝ) :
    ‖(starRingEnd ℂ) w - (a : ℂ)‖ = ‖w - (a : ℂ)‖ := by
  rw [← Complex.norm_conj, map_sub, Complex.conj_conj, Complex.conj_ofReal]

theorem conj_slicePoint' (w : ℂ) (t : ℝ) :
    1 / 2 + w - (t : ℂ) * I = (starRingEnd ℂ) (1 / 2 + (starRingEnd ℂ) w + (t : ℂ) * I) := by
  apply Complex.ext <;> simp; ring

theorem one_add_log_ge_one (h : ZetaScaleData t R M W) (hR : 0 < R) (hR16 : R ≤ 1 / 16)
    (ht : 8 ≤ t) : 1 ≤ Real.log M + W + 1 ∧ 0 < M := by
  obtain ⟨-, -, hMb, hm⟩ := scale_disc_hypotheses hR hR16 ht h.zeroFree h.upper h.lower
  have hmc : Real.exp (-W) ≤ M := hm.trans (hMb _ (mem_ball_self (by positivity)))
  have hM0 : 0 < M := lt_of_lt_of_le (Real.exp_pos _) hmc
  have := Real.log_le_log (Real.exp_pos _) hmc
  rw [Real.log_exp] at this
  exact ⟨by linarith, hM0⟩

/-- **Zero-free slice product at scale `R`.** -/
theorem xiSliceProduct_ne_zero (h : ZetaScaleData t R M W) (hR : 0 < R) (hR16 : R ≤ 1 / 16)
    (ht : 8 ≤ t) {w : ℂ} (hw : w ∈ ball ((3 * R : ℝ) : ℂ) (29 / 10 * R)) :
    xiSliceProduct t w ≠ 0 := by
  obtain ⟨-, hne, -, -⟩ := scale_disc_hypotheses hR hR16 ht h.zeroFree h.upper h.lower
  have key : ∀ v : ℂ, ‖v - ((3 * R : ℝ) : ℂ)‖ < 29 / 10 * R →
      xi (1 / 2 + v + (t : ℂ) * I) ≠ 0 := by
    intro v hv
    have hmem : 1 / 2 + v + (t : ℂ) * I ∈ ball (scaleCentre R t) (29 / 10 * R) := by
      rw [mem_ball, dist_eq_norm, slicePoint_sub_centre]; exact hv
    have him : (1 / 2 + v + (t : ℂ) * I).im ≠ 0 := by
      have h1 := (abs_le.mp ((Complex.abs_im_le_norm (v - ((3 * R : ℝ) : ℂ))).trans hv.le))
      simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at h1
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      norm_num
      intro h0
      linarith
    exact xi_ne_zero_of_riemannZeta_ne_zero_offReal him (hne _ hmem)
  rw [mem_ball, dist_eq_norm] at hw
  unfold xiSliceProduct
  have e : (1 / 2 : ℂ) - w + (t : ℂ) * I = 1 - (1 / 2 + w - (t : ℂ) * I) := by ring
  refine mul_ne_zero (key w hw) ?_
  rw [e, xi_one_sub, conj_slicePoint', xi_conj]
  exact (map_ne_zero _).mpr (key _ (by rw [norm_conj_sub_real]; exact hw))

/-- **Stirling comparison at scale `R`.** On `|w − 3R| ≤ 2.3R`, both points `½ + w ± it`
satisfy `|ξ'/ξ(s) − ½ log(s/2)| ≤ 3 + 58B/R`. -/
theorem stirling_le (h : ZetaScaleData t R M W) (hR : 0 < R) (hR16 : R ≤ 1 / 16) (ht : 8 ≤ t)
    {w : ℂ} (hw : ‖w - ((3 * R : ℝ) : ℂ)‖ ≤ 23 / 10 * R) :
    ‖logDeriv xi (1 / 2 + w + (t : ℂ) * I) - Complex.log ((1 / 2 + w + (t : ℂ) * I) / 2) / 2‖
        ≤ 3 + 58 * (Real.log M + W + 1) / R
      ∧ ‖logDeriv xi (1 / 2 + w - (t : ℂ) * I) - Complex.log ((1 / 2 + w - (t : ℂ) * I) / 2) / 2‖
        ≤ 3 + 58 * (Real.log M + W + 1) / R := by
  obtain ⟨-, hne, -, -⟩ := scale_disc_hypotheses hR hR16 ht h.zeroFree h.upper h.lower
  have plus : ∀ v : ℂ, ‖v - ((3 * R : ℝ) : ℂ)‖ ≤ 23 / 10 * R →
      0 < (1 / 2 + v + (t : ℂ) * I).re ∧
      ‖logDeriv xi (1 / 2 + v + (t : ℂ) * I) - Complex.log ((1 / 2 + v + (t : ℂ) * I) / 2) / 2‖
        ≤ 3 + 58 * (Real.log M + W + 1) / R := by
    intro v hv
    have h1 := abs_le.mp ((Complex.abs_re_le_norm (v - ((3 * R : ℝ) : ℂ))).trans hv)
    have h2 := abs_le.mp ((Complex.abs_im_le_norm (v - ((3 * R : ℝ) : ℂ))).trans hv)
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      sub_zero] at h1 h2
    have hre : (1 / 2 + v + (t : ℂ) * I).re = 1 / 2 + v.re := by simp
    have him : (1 / 2 + v + (t : ℂ) * I).im = v.im + t := by simp
    have hre0 : 0 < (1 / 2 + v + (t : ℂ) * I).re := by rw [hre]; linarith
    refine ⟨hre0, ?_⟩
    have hs : ‖1 / 2 + v + (t : ℂ) * I - scaleCentre R t‖ ≤ 23 / 10 * R := by
      rw [slicePoint_sub_centre]; exact hv
    have hB := norm_logDeriv_le_scale hR hR16 ht h.zeroFree h.upper h.lower hs
    have him0 : (1 / 2 + v + (t : ℂ) * I).im ≠ 0 := by rw [him]; linarith
    have hs4 : 4 ≤ ‖1 / 2 + v + (t : ℂ) * I‖ := by
      refine le_trans ?_ (Complex.abs_im_le_norm _)
      rw [him, abs_of_pos (by linarith)]; linarith
    have hmem : 1 / 2 + v + (t : ℂ) * I ∈ ball (scaleCentre R t) (29 / 10 * R) := by
      rw [mem_ball, dist_eq_norm]; linarith
    exact norm_logDeriv_xi_sub_half_log_le_of_zeta hre0 him0 hs4 (hne _ hmem) hB
  refine ⟨(plus w hw).2, ?_⟩
  have hc := plus ((starRingEnd ℂ) w) (by rw [norm_conj_sub_real]; exact hw)
  rw [conj_slicePoint', norm_logDeriv_xi_sub_half_log_conj hc.1]
  exact hc.2

/-- The Stirling hypothesis on the saddle disc `|w − Rs| ≤ R/4`, `R ≤ Rs ≤ 5R`. -/
theorem xiSliceStirling (h : ZetaScaleData t R M W) (hR : 0 < R) (hR16 : R ≤ 1 / 16)
    (ht : 8 ≤ t) {Rs : ℝ} (hRs1 : R ≤ Rs) (hRs5 : Rs ≤ 5 * R) :
    XiSliceStirling t (3 + 58 * (Real.log M + W + 1) / R) (closedBall (Rs : ℂ) (R / 4)) := by
  intro w hw
  refine h.stirling_le hR hR16 ht ?_
  rw [mem_closedBall, dist_eq_norm] at hw
  have e : w - ((3 * R : ℝ) : ℂ) = (w - Rs) + ((Rs - 3 * R : ℝ) : ℂ) := by push_cast; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  have : |Rs - 3 * R| ≤ 2 * R := abs_le.mpr ⟨by linarith, by linarith⟩
  linarith

/-- **Arc tail at scale `R`.** For `R ≤ Rs ≤ 5R` and `θ₁ ≤ θ ≤ π/2`,
`|S(θ)| ≤ e^{18B} · e · 2π · t^{−Rs θ₁²/5}`. -/
theorem norm_sliceArc_le (h : ZetaScaleData t R M W) (hR : 0 < R) (hR16 : R ≤ 1 / 16)
    (ht : 48 ≤ t) (k : ℕ) {Rs θ₁ θ : ℝ} (hRs1 : R ≤ Rs) (hRs5 : Rs ≤ 5 * R) (hθ₁ : 0 < θ₁)
    (hθ : θ₁ ≤ θ) (hθπ : θ ≤ Real.pi / 2) :
    ‖sliceArc t Rs k θ‖ ≤ Real.exp (18 * (Real.log M + W + 1))
      * (Real.exp 1 * ((2 * Real.pi) ^ (1 : ℝ) * t ^ (-(Rs * θ₁ ^ 2 / 5)))) := by
  obtain ⟨hB1, hM0⟩ := h.one_add_log_ge_one hR hR16 (by linarith)
  have hRs0 : 0 < Rs := by linarith
  have hθ0 : 0 ≤ θ := by linarith
  have hcos : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) hθπ
  set m₀ := Real.exp (-W - 8 * (Real.log M + W + 1)) with hm₀
  have hz₀ : m₀ ≤ ‖riemannZeta (((1 / 2 + Rs : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
    refine norm_ge_scale hR hR16 (by linarith) h.zeroFree h.upper h.lower ?_
    have e : ((1 / 2 + Rs : ℝ) : ℂ) + (t : ℂ) * I - scaleCentre R t = ((Rs - 3 * R : ℝ) : ℂ) := by
      simp only [scaleCentre]; push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hzB : ∀ c : ℝ, |c| ≤ Rs → ‖riemannZeta (((1 / 2 + Rs * Real.cos θ : ℝ) : ℂ)
      + ((t + c : ℝ) : ℂ) * I)‖ ≤ M := by
    intro c hc
    refine h.upper _ ?_ ?_ ?_
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
      nlinarith
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
      nlinarith [Real.cos_le_one θ]
    · simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, mul_zero, add_zero, mul_one, zero_add]
      rw [show t + c - t = c by ring]; linarith
  have hsinR : |Rs * Real.sin θ| ≤ Rs := by
    rw [abs_mul, abs_of_pos hRs0]; exact mul_le_of_le_one_right hRs0.le (Real.abs_sin_le_one θ)
  have hz₂ := hzB (-(Rs * Real.sin θ)) (by rwa [abs_neg])
  rw [← sub_eq_add_neg] at hz₂
  have hm₀0 : 0 < m₀ := Real.exp_pos _
  have hcirc := norm_xiSliceProduct_circle_le (by linarith) hRs0.le (by linarith) hcos hm₀0 hz₀
    (hzB _ hsinR) hz₂
  have hθsq : Rs * θ₁ ^ 2 / 5 ≤ Rs * (1 - Real.cos θ) := by
    have hc5 := one_sub_cos_ge_sq_div_five (θ := θ)
      (by rw [abs_of_nonneg hθ0]; linarith [Real.pi_pos])
    have hθ2 : θ₁ ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ hθ₁.le hθ 2
    have : Rs * θ₁ ^ 2 / 5 ≤ Rs * (θ ^ 2 / 5) := by nlinarith
    nlinarith
  have hdR : Rs * θ₁ ^ 2 / 5 ≤ 1 :=
    hθsq.trans ((mul_le_of_le_one_right hRs0.le (by linarith)).trans (by linarith))
  have hexpX := circle_decay_exp_le (t := t) (R₁ := 1) (d := Rs * θ₁ ^ 2 / 5) (by linarith)
    hRs0.le (by linarith) hcos hθsq hdR
  have hgR : 0 < ‖xiSliceProduct t (Rs : ℂ)‖ := by
    rw [norm_xiSliceProduct_real]
    refine pow_pos (norm_pos_iff.mpr (xi_ne_zero_of_riemannZeta_ne_zero_offReal ?_ ?_)) 2
    · simp; linarith
    · intro h0
      have := h.zeroFree _ h0 (by simp; linarith)
      simp at this; linarith
  have hratio : (M / m₀) ^ 2 ≤ Real.exp (18 * (Real.log M + W + 1)) := by
    rw [hm₀, div_eq_mul_inv, ← Real.exp_neg, mul_pow, ← Real.exp_nat_mul]
    have hMe : M = Real.exp (Real.log M) := (Real.exp_log hM0).symm
    rw [hMe, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    push_cast
    rw [Real.log_exp]
    nlinarith
  rw [norm_sliceArc_eq, div_le_iff₀ hgR]
  calc ‖xiSliceProduct t ((Rs : ℂ) * Complex.exp ((θ : ℂ) * I))‖
      ≤ _ := hcirc
    _ ≤ ‖xiSliceProduct t (Rs : ℂ)‖ * Real.exp (18 * (Real.log M + W + 1))
        * (Real.exp 1 * ((2 * Real.pi) ^ (1 : ℝ) * t ^ (-(Rs * θ₁ ^ 2 / 5)))) := by
        gcongr
    _ = _ := by ring

end ZetaScaleData

/-- The linear budget of the saddle at scale: with `C ≤ 3 + u/10⁸` and `u ≥ 10⁴`. -/
theorem scale_budget {C u : ℝ} (hC : C ≤ 3 + u / 10 ^ 8) (hu : 10000 ≤ u) :
    2 * C ≤ u ∧ 5 * Real.log 2 + 10 * C ≤ u
      ∧ Real.log 2 + 2 * C + 20 * (Real.log 4 + Real.pi + 4 * C) ≤ u / 10
      ∧ (Real.log (3 / 2) + Real.pi / 2 + 2 * C) / 4 + 5 * (Real.log 4 + Real.pi + 4 * C)
        ≤ u / 4 := by
  have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hl4 : Real.log 4 < 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
  have hl32 : Real.log (3 / 2) < 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 2); linarith
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpi := Real.pi_lt_d2
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

namespace ZetaScaleData

variable {t R M W : ℝ}

/-- The Stirling constant at scale `R` is at most `3 + u/10⁸` when `k ≤ 2Ru` and `10¹¹ B ≤ k`. -/
theorem stirlingConst_le {R B u : ℝ} {k : ℕ} (hR : 0 < R) (hB : 1 ≤ B)
    (hk2 : (k : ℝ) ≤ 2 * R * u) (hkB : 10 ^ 11 * B ≤ k) :
    3 + 58 * B / R ≤ 3 + u / 10 ^ 8 := by
  have hk0 : 0 < (k : ℝ) := by nlinarith
  have hRu : 0 < u := by nlinarith
  have h1 : 58 * B / R ≤ 116 * B * u / k := by
    rw [div_le_div_iff₀ hR hk0]; nlinarith
  have h2 : 116 * B * u / k ≤ u / 10 ^ 8 := by
    rw [div_le_div_iff₀ hk0 (by norm_num)]; nlinarith
  linarith

theorem norm_ofReal_sub_three (R R' : ℝ) :
    ‖(R' : ℂ) - ((3 * R : ℝ) : ℂ)‖ = |R' - 3 * R| := by
  rw [show (R' : ℂ) - ((3 * R : ℝ) : ℂ) = ((R' - 3 * R : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs]

theorem closedBall_subset_scaleBall {R Rs : ℝ} (hR : 0 < R) (hRa : R ≤ Rs) (hRb : Rs ≤ 5 * R) :
    closedBall (Rs : ℂ) (R / 4) ⊆ ball ((3 * R : ℝ) : ℂ) (29 / 10 * R) := by
  intro w hw
  rw [mem_closedBall, dist_eq_norm] at hw
  rw [mem_ball, dist_eq_norm]
  have e : w - ((3 * R : ℝ) : ℂ) = (w - Rs) + ((Rs - 3 * R : ℝ) : ℂ) := by push_cast; ring
  rw [e]
  refine (norm_add_le _ _).trans_lt ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  have : |Rs - 3 * R| ≤ 2 * R := abs_le.mpr ⟨by linarith, by linarith⟩
  linarith

/-- **The saddle radius at scale `R`** lies in `[R, 5R]`. -/
theorem saddle_radius (h : ZetaScaleData t R M W) (hR : 0 < R) (hR16 : R ≤ 1 / 16) (ht : 48 ≤ t)
    (hu : 10000 ≤ Real.log t) {k : ℕ} (hk1 : R * Real.log t ≤ k)
    (hk2 : (k : ℝ) ≤ 2 * R * Real.log t) (hkB : 10 ^ 11 * (Real.log M + W + 1) ≤ k) :
    ∃ Rs : ℝ, R ≤ Rs ∧ Rs ≤ 5 * R
      ∧ (HTGeometry.scaledLogDeriv (xiSliceProduct t) Rs).re = 2 * (k : ℝ) := by
  have ht0 : 0 < t := by linarith
  obtain ⟨hB1, -⟩ := h.one_add_log_ge_one hR hR16 (by linarith)
  have hCu := stirlingConst_le hR hB1 hk2 hkB
  obtain ⟨-, b2, -, -⟩ := scale_budget hCu hu
  have hU : ∀ w ∈ ball ((3 * R : ℝ) : ℂ) (29 / 10 * R), xiSliceProduct t w ≠ 0 := fun w hw =>
    h.xiSliceProduct_ne_zero hR hR16 (by linarith) hw
  have hIcc : ∀ R' ∈ Icc R (5 * R), (R' : ℂ) ∈ ball ((3 * R : ℝ) : ℂ) (29 / 10 * R) := by
    intro R' hR'
    rw [mem_ball, dist_eq_norm, norm_ofReal_sub_three]
    exact abs_lt.mpr ⟨by linarith [hR'.1], by linarith [hR'.2]⟩
  have hEreal : ∀ R' ∈ Icc R (5 * R), ‖logDeriv xi (1 / 2 + (R' : ℂ) + (t : ℂ) * I)
      - Complex.log ((1 / 2 + (R' : ℂ) + (t : ℂ) * I) / 2) / 2‖
        ≤ 3 + 58 * (Real.log M + W + 1) / R := by
    intro R' hR'
    refine (h.stirling_le hR hR16 (by linarith) ?_).1
    rw [norm_ofReal_sub_three]; exact abs_le.mpr ⟨by linarith [hR'.1], by linarith [hR'.2]⟩
  have hlog2 : Real.log (t / 2) = Real.log t - Real.log 2 := by
    rw [Real.log_div ht0.ne' (by norm_num)]
  have hlo : R * (Real.log t + 2 * (3 + 58 * (Real.log M + W + 1) / R)) ≤ 2 * (k : ℝ) := by
    have h1 : R * (2 * (3 + 58 * (Real.log M + W + 1) / R))
        = 6 * R + 116 * (Real.log M + W + 1) := by field_simp; ring
    have h2 : 116 * (Real.log M + W + 1) + 1 ≤ (k : ℝ) := by nlinarith
    nlinarith
  have hhi : 2 * (k : ℝ) ≤ 5 * R * (Real.log (t / 2) - 2 * (3 + 58 * (Real.log M + W + 1) / R)) := by
    rw [hlog2]
    have := mul_le_mul_of_nonneg_left b2 hR.le
    nlinarith
  obtain ⟨Rs, ⟨hRa, hRb⟩, hsad⟩ := exists_saddle_radius_strip (by linarith) hR.le (by linarith)
    (by linarith) hU hIcc hEreal hlo hhi
  exact ⟨Rs, hRa, hRb, hsad⟩

/-- **Slope and disc constant at scale `R`.** -/
theorem saddle_slope_disc (h : ZetaScaleData t R M W) (hR : 0 < R) (hR16 : R ≤ 1 / 16)
    (ht : 48 ≤ t) (hu : 10000 ≤ Real.log t) {k : ℕ} (hk2 : (k : ℝ) ≤ 2 * R * Real.log t)
    (hkB : 10 ^ 11 * (Real.log M + W + 1) ≤ k) {Rs : ℝ} (hRa : R ≤ Rs) (hRb : Rs ≤ 5 * R) :
    9 / 10 * Real.log t ≤ (deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) Rs).re
      ∧ (deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) Rs).re ≤ 2 * Real.log t
      ∧ xiSliceDiscConstantStrip (R / 4) (3 + 58 * (Real.log M + W + 1) / R) t Rs
        ≤ 2 * (R / 4) * Real.log t := by
  have ht0 : 0 < t := by linarith
  obtain ⟨hB1, -⟩ := h.one_add_log_ge_one hR hR16 (by linarith)
  set C := 3 + 58 * (Real.log M + W + 1) / R with hCdef
  have hC0 : 0 ≤ C := by
    rw [hCdef]
    have : 0 < Real.log M + W + 1 := by linarith
    positivity
  have hCu := stirlingConst_le hR hB1 hk2 hkB
  rw [← hCdef] at hCu
  obtain ⟨-, -, b3, b4⟩ := scale_budget hCu hu
  have hU : ∀ w ∈ ball ((3 * R : ℝ) : ℂ) (29 / 10 * R), xiSliceProduct t w ≠ 0 := fun w hw =>
    h.xiSliceProduct_ne_zero hR hR16 (by linarith) hw
  have hball := closedBall_subset_scaleBall hR hRa hRb
  have hS := h.xiSliceStirling hR hR16 (by linarith) hRa hRb
  rw [← hCdef] at hS
  obtain ⟨hF₁lo, hF₁hi⟩ := xiSlice_saddleSlope_bounds_strip isOpen_ball hU hball
    (by positivity : 0 < R / 4) (by linarith) (by linarith) (by linarith) (by linarith) hS
  have hq0 : 0 ≤ Real.log 4 + Real.pi + 4 * C := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); positivity
  have hRq : Rs * (Real.log 4 + Real.pi + 4 * C) / (R / 4) ≤ 20 * (Real.log 4 + Real.pi + 4 * C) := by
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

/-- **The size of `Rs log t`**: `k ≤ Rs log t ≤ 4k` at the saddle radius. -/
theorem saddle_scale (h : ZetaScaleData t R M W) (hR : 0 < R) (hR16 : R ≤ 1 / 16) (ht : 48 ≤ t)
    (hu : 10000 ≤ Real.log t) {k : ℕ} (hk2 : (k : ℝ) ≤ 2 * R * Real.log t)
    (hkB : 10 ^ 11 * (Real.log M + W + 1) ≤ k) {Rs : ℝ} (hRa : R ≤ Rs) (hRb : Rs ≤ 5 * R)
    (hsad : (HTGeometry.scaledLogDeriv (xiSliceProduct t) Rs).re = 2 * (k : ℝ)) :
    (k : ℝ) ≤ Rs * Real.log t ∧ Rs * Real.log t ≤ 4 * k := by
  have ht0 : 0 < t := by linarith
  obtain ⟨hB1, -⟩ := h.one_add_log_ge_one hR hR16 (by linarith)
  have hCu := stirlingConst_le hR hB1 hk2 hkB
  obtain ⟨b1, -, -, -⟩ := scale_budget hCu hu
  have hU : ∀ w ∈ ball ((3 * R : ℝ) : ℂ) (29 / 10 * R), xiSliceProduct t w ≠ 0 := fun w hw =>
    h.xiSliceProduct_ne_zero hR hR16 (by linarith) hw
  have hS := h.xiSliceStirling hR hR16 (by linarith) hRa hRb
  have hSR := (hS Rs (mem_closedBall_self (by positivity))).1
  obtain ⟨-, hLlo, hLhi⟩ := xiSliceLogDeriv_real_bounds_strip (by linarith) (by linarith)
    (by linarith) hSR
  have hRU : (Rs : ℂ) ∈ ball ((3 * R : ℝ) : ℂ) (29 / 10 * R) :=
    closedBall_subset_scaleBall hR hRa hRb (mem_closedBall_self (by positivity))
  have hsad' : Rs * (xiSliceLogDeriv t Rs).re = 2 * (k : ℝ) := by
    rw [← hsad, scaledLogDeriv_xiSliceProduct_of_ne (hU _ hRU)]
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

/-- The tail at scale `R` in terms of the order: `|S(θ)| ≤ 2πe · e^{−k/10⁹}` for
`1/10000 ≤ θ ≤ π/2`. -/
theorem tail_le_order (h : ZetaScaleData t R M W) (hR : 0 < R) (hR16 : R ≤ 1 / 16) (ht : 48 ≤ t)
    {k : ℕ} (hkB : 10 ^ 11 * (Real.log M + W + 1) ≤ k) {Rs : ℝ} (hRa : R ≤ Rs) (hRb : Rs ≤ 5 * R)
    (hRsk : (k : ℝ) ≤ Rs * Real.log t) :
    ∀ θ : ℝ, 1 / (1000 * 10) ≤ θ → θ ≤ Real.pi / 2 →
      ‖sliceArc t Rs k θ‖ ≤ Real.exp 1 * (2 * Real.pi) * Real.exp (-((k : ℝ) / 10 ^ 9)) := by
  intro θ hθ hθπ
  have ht0 : 0 < t := by linarith
  have hb := h.norm_sliceArc_le hR hR16 ht k hRa hRb (by norm_num : (0 : ℝ) < 1 / (1000 * 10))
    hθ hθπ
  rw [Real.rpow_one, Real.rpow_def_of_pos ht0] at hb
  refine hb.trans ?_
  have hexp : Real.exp (18 * (Real.log M + W + 1)) * (Real.exp 1 * (2 * Real.pi
      * Real.exp (Real.log t * -(Rs * (1 / (1000 * 10)) ^ 2 / 5))))
      = Real.exp 1 * (2 * Real.pi) * Real.exp (18 * (Real.log M + W + 1)
        - Rs * Real.log t / (5 * 10 ^ 8)) := by
    have e : 18 * (Real.log M + W + 1) - Rs * Real.log t / (5 * 10 ^ 8)
        = 18 * (Real.log M + W + 1) + Real.log t * -(Rs * (1 / (1000 * 10)) ^ 2 / 5) := by ring
    rw [e, Real.exp_add]; ring
  rw [hexp]
  gcongr
  have h1 : 18 * (Real.log M + W + 1) ≤ 18 * (k : ℝ) / 10 ^ 11 := by
    rw [le_div_iff₀ (by norm_num)]; nlinarith
  have h2 : (k : ℝ) / (5 * 10 ^ 8) ≤ Rs * Real.log t / (5 * 10 ^ 8) :=
    div_le_div_of_nonneg_right hRsk (by norm_num)
  have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
  linarith

end ZetaScaleData

/-- **Positivity from scale data.** There is `k₁` such that `c_{2k}(t) > 0` whenever scale data
`(t, R, M, W)` hold with `0 < R ≤ 1/16`, `t ≥ 48`, `log t ≥ 10⁴`, `R log t ≤ k ≤ 2R log t`,
`k ≥ 10¹¹ (log M + W + 1)` and `k ≥ k₁`. -/
theorem exists_xiSliceCoeff_pos_of_scaleData :
    ∃ k₁ : ℝ, 1 ≤ k₁ ∧ ∀ t R M W : ℝ, ∀ k : ℕ, ZetaScaleData t R M W → 0 < R → R ≤ 1 / 16 →
      48 ≤ t → 10000 ≤ Real.log t → R * Real.log t ≤ k → (k : ℝ) ≤ 2 * R * Real.log t →
      10 ^ 11 * (Real.log M + W + 1) ≤ k → k₁ ≤ k → 0 < xiSliceCoeff t (2 * k) := by
  have e1 := (tendsto_order.1 tendsto_rpow_half_mul_exp_neg_fifth_root).2 50 (by norm_num)
  have e3 := (tendsto_order.1 (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 5))).2
    (1 / (1000 * 10)) (by norm_num)
  have e4 := (tendsto_order.1 (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 5))).2
    (3 / (2 * (1 + 128 * 10))) (by norm_num)
  obtain ⟨Λ₀, hΛ₀⟩ := Filter.eventually_atTop.mp (e1.and (e3.and e4))
  have e5 := (tendsto_order.1 (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2) (1 / 10 ^ 9)
    (by norm_num))).2 (1 / (20 * Real.pi ^ 2 * Real.exp 1)) (by positivity)
  obtain ⟨K₅, hK₅⟩ := Filter.eventually_atTop.mp e5
  refine ⟨max (max Λ₀ K₅) 1, le_max_right _ _, ?_⟩
  intro t R M W k h hR hR16 ht hu hk1 hk2 hkB hk₁
  have hkΛ : Λ₀ ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk₁
  have hkK : K₅ ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk₁
  have hk1' : (1 : ℝ) ≤ k := le_trans (le_max_right _ _) hk₁
  have ht0 : 0 < t := by linarith
  have hu0 : 0 < Real.log t := by linarith
  obtain ⟨Rs, hRa, hRb, hsad⟩ := h.saddle_radius hR hR16 ht hu hk1 hk2 hkB
  obtain ⟨hF₁lo, hF₁hi, hKd⟩ := h.saddle_slope_disc hR hR16 ht hu hk2 hkB hRa hRb
  obtain ⟨hRsk, hRsk4⟩ := h.saddle_scale hR hR16 ht hu hk2 hkB hRa hRb hsad
  have htail := h.tail_le_order hR hR16 ht hkB hRa hRb hRsk
  obtain ⟨hE1, hE3, hE4⟩ := hΛ₀ (Rs * Real.log t) (by linarith)
  have hΛpos : 0 < Rs * Real.log t := by linarith
  have hEt : Real.pi / 2 * (Real.exp 1 * (2 * Real.pi) * Real.exp (-((k : ℝ) / 10 ^ 9)))
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
    have hexpk : Real.exp (-((k : ℝ) / 10 ^ 9)) = Real.exp (-(1 / 10 ^ 9) * k) := by
      congr 1; ring
    rw [hexpk]
    rw [h4k] at hmono
    have key : Real.pi / 2 * (Real.exp 1 * (2 * Real.pi) * Real.exp (-(1 / 10 ^ 9) * k))
        ≤ 1 / (2 * (k : ℝ) ^ (1 / 2 : ℝ)) / 10 := by
      rw [div_div, le_div_iff₀ (by positivity)]
      have e : Real.pi / 2 * (Real.exp 1 * (2 * Real.pi) * Real.exp (-(1 / 10 ^ 9) * k))
          * (2 * (k : ℝ) ^ (1 / 2 : ℝ) * 10)
          = 20 * Real.pi ^ 2 * Real.exp 1 * ((k : ℝ) ^ (1 / 2 : ℝ)
            * Real.exp (-(1 / 10 ^ 9) * k)) := by ring
      rw [e]
      have hpos : 0 < 20 * Real.pi ^ 2 * Real.exp 1 := by positivity
      calc 20 * Real.pi ^ 2 * Real.exp 1 * ((k : ℝ) ^ (1 / 2 : ℝ) * Real.exp (-(1 / 10 ^ 9) * k))
          ≤ 20 * Real.pi ^ 2 * Real.exp 1 * (1 / (20 * Real.pi ^ 2 * Real.exp 1)) :=
            mul_le_mul_of_nonneg_left h5 hpos.le
        _ = 1 := by field_simp
    linarith
  have hU : ∀ w ∈ ball ((3 * R : ℝ) : ℂ) (29 / 10 * R), xiSliceProduct t w ≠ 0 := fun w hw =>
    h.xiSliceProduct_ne_zero hR hR16 (by linarith) hw
  have hC0 : 0 ≤ 3 + 58 * (Real.log M + W + 1) / R := by
    obtain ⟨hB1, -⟩ := h.one_add_log_ge_one hR hR16 (by linarith)
    have : 0 < Real.log M + W + 1 := by linarith
    positivity
  exact xiSliceCoeff_pos_of_saddle_strip isOpen_ball hU
    (ZetaScaleData.closedBall_subset_scaleBall hR hRa hRb)
    (h.xiSliceStirling hR hR16 (by linarith) hRa hRb) hC0 (by positivity) (by linarith)
    (by linarith : 2 * (R / 4) ≤ 5 * R) (by field_simp; ring) (by linarith) hu0
    (by linarith) hRb (by linarith) hsad hF₁lo hF₁hi hKd htail (by linarith) hE1 hE3 hE4 hEt

end

end RHTower
