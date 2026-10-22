import GaloisForLFunctions.RHTower.ThetaPowerHardyZeros
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspChargePowIntegral

/-!
# The saddle window of `F_a` at its pole cusp, for every real `a > 1/2`

For `a > 1/2` the form `F_a = θ₃h^{a/4}` has a pole of order `m = 2a - 1 > 0` at the cusp `1`.  On
the line `Im z = -β(t)` the integrand `e^{-ius} T_a(s - iβ)` at the saddle frequency
`u = mπ/(8t⁴)` factors exactly as

`g₀ · e^{Re ψ - R₀} · A(s) · e^{i(Im ψ + mπ/8)} · (1 + ε_a(v))`,

with `g₀ = 2^{-2a} P₀ e^{R₀}`: the window law of `F_a` contributes the phase `e^{iπa/4}`, which the
line height `β` and the pole order combine into `e^{iθ/2}` exactly as for integer powers.  The phase
function is linear in `m`, so the Gaussian law, the inner bound and the cubic phase bound hold for
every real `m > 0` with constants proportional to `m`.
-/

open Complex
open scoped Real

namespace RHTower

noncomputable section

section GeometryReal

variable {m t : ℝ}

theorem chR0m_sub_psim_re_le_inner_real (ht : 0 < t) (ht1 : t ≤ 1) {K : ℝ} (hK : 1 ≤ K)
    (hm0 : 0 ≤ m) (hm : m ≤ 8 * K) {s : ℝ} (hs : |s| ≤ t ^ 3 / (4 * K)) :
    chR0m m t - (chPsim m t s).re ≤ 1 / 2 := by
  have ht4 : t ^ 4 ≤ 1 := pow_le_one₀ ht.le ht1
  have hs1 : |s| ≤ 1 := by
    have : t ^ 3 ≤ 1 := pow_le_one₀ ht.le ht1
    have : t ^ 3 / (4 * K) ≤ t ^ 3 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [pow_pos ht 3]
    linarith
  rw [chR0m_sub_psim_re ht ht4]
  have hb1 := chB_le_one (t := t)
  have hσ := abs_chSigma_le hs1
  have hσ2 : chSigma s ^ 2 ≤ 9 * s ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) hσ 2
    rw [sq_abs, mul_pow, sq_abs] at this; linarith
  have hs2 : s ^ 2 ≤ t ^ 6 / (16 * K ^ 2) := by
    have := pow_le_pow_left₀ (abs_nonneg _) hs 2
    rw [sq_abs] at this
    calc s ^ 2 ≤ (t ^ 3 / (4 * K)) ^ 2 := this
      _ = t ^ 6 / (16 * K ^ 2) := by field_simp; ring
  have hq : 4 * t ^ 4 ≤ chSigma s ^ 2 + 4 * t ^ 4 := by nlinarith [sq_nonneg (chSigma s)]
  rw [div_le_iff₀ (by positivity)]
  have hπ := Real.pi_lt_d2
  have hkey : m * π * 9 * (t ^ 6 / (16 * K ^ 2)) ≤ 1 / 2 * (8 * t ^ 2 * (4 * t ^ 4)) := by
    have h1 : m * π * 9 ≤ 8 * K * 3.15 * 9 := by
      have := mul_le_mul hm hπ.le Real.pi_pos.le (by positivity); nlinarith
    have h2 : 0 ≤ t ^ 6 / (16 * K ^ 2) := by positivity
    calc m * π * 9 * (t ^ 6 / (16 * K ^ 2))
        ≤ 8 * K * 3.15 * 9 * (t ^ 6 / (16 * K ^ 2)) := mul_le_mul_of_nonneg_right h1 h2
      _ = 3.15 * 9 / (2 * K) * t ^ 6 := by field_simp; ring
      _ ≤ 3.15 * 9 / 2 * t ^ 6 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
      _ ≤ 1 / 2 * (8 * t ^ 2 * (4 * t ^ 4)) := by nlinarith [pow_pos ht 6]
  calc m * π * chB t * chSigma s ^ 2 ≤ m * π * 1 * (9 * (t ^ 6 / (16 * K ^ 2))) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hb1 (by positivity))
          (le_trans hσ2 (by nlinarith)) (sq_nonneg _) (by positivity)
    _ = m * π * 9 * (t ^ 6 / (16 * K ^ 2)) := by ring
    _ ≤ 1 / 2 * (8 * t ^ 2 * (4 * t ^ 4)) := hkey
    _ ≤ 1 / 2 * (8 * t ^ 2 * (chSigma s ^ 2 + 4 * t ^ 4)) := by gcongr

/-- **The Gaussian law for every real pole order.** -/
theorem chR0m_sub_psim_re_ge_mid_real (hm : 0 < m) (ht : 0 < t) (ht2 : t ^ 2 ≤ 1 / 4) {s : ℝ}
    (hs : |s| ≤ 2 * t ^ 2) : m * s ^ 2 / (28 * t ^ 6) ≤ chR0m m t - (chPsim m t s).re := by
  have ht4 : t ^ 4 ≤ 1 := by nlinarith
  have hb := half_le_chB (t := t) (by nlinarith)
  rw [chR0m_sub_psim_re ht ht4]
  have hσ := two_abs_le_abs_chSigma s
  have hσ2 : 4 * s ^ 2 ≤ chSigma s ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hσ 2
    rw [mul_pow, sq_abs, sq_abs] at this; linarith
  have hs2 : s ^ 2 ≤ 4 * t ^ 4 := by
    have := pow_le_pow_left₀ (abs_nonneg _) hs 2
    rw [sq_abs] at this; nlinarith
  have ht2p : 0 < t ^ 2 := by positivity
  have hX : s ^ 2 / (s ^ 2 + t ^ 4) ≤ chSigma s ^ 2 / (chSigma s ^ 2 + 4 * t ^ 4) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg s, pow_pos ht 4]
  have hY : s ^ 2 / (5 * t ^ 4) ≤ s ^ 2 / (s ^ 2 + t ^ 4) := by
    rcases eq_or_lt_of_le (sq_nonneg s) with h0 | h0
    · rw [← h0]; simp
    · exact div_le_div_of_nonneg_left h0.le (by positivity) (by linarith)
  have hπ := Real.pi_gt_three
  have hmain : m * π * chB t * chSigma s ^ 2 / (8 * t ^ 2 * (chSigma s ^ 2 + 4 * t ^ 4)) =
      m * π * chB t / (8 * t ^ 2) * (chSigma s ^ 2 / (chSigma s ^ 2 + 4 * t ^ 4)) := by
    field_simp
  rw [hmain]
  calc m * s ^ 2 / (28 * t ^ 6) ≤ m * π * (1 / 2) / (8 * t ^ 2) * (s ^ 2 / (5 * t ^ 4)) := by
        rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
        have hst : 0 ≤ m * (s ^ 2 * t ^ 6) := by positivity
        have e1 : m * s ^ 2 * (8 * t ^ 2 * (5 * t ^ 4)) = 40 * (m * (s ^ 2 * t ^ 6)) := by ring
        have e2 : m * π * (1 / 2) * s ^ 2 * (28 * t ^ 6) = 14 * π * (m * (s ^ 2 * t ^ 6)) := by ring
        rw [e1, e2]; nlinarith
    _ ≤ m * π * chB t / (8 * t ^ 2) * (chSigma s ^ 2 / (chSigma s ^ 2 + 4 * t ^ 4)) := by
        apply mul_le_mul _ (le_trans hY hX) (by positivity) (by
          have : 0 ≤ chB t := chB_nonneg; positivity)
        apply div_le_div_of_nonneg_right _ (by positivity)
        have : 0 ≤ m * π := by positivity
        nlinarith

theorem abs_chPhim_le_real (ht : 0 < t) (ht1 : t ≤ 1) {K : ℝ} (hm0 : 0 ≤ m)
    (hm : m ≤ 8 * K) {s : ℝ} (hs : |s| ≤ 1 / 2) :
    |(chPsim m t s).im + m * π / 8| ≤ 11 * K * |s| ^ 3 / t ^ 8 := by
  have ht4 : t ^ 4 ≤ 1 := pow_le_one₀ ht.le ht1
  have hK : 0 ≤ K := by linarith
  rw [chPsim_im_add ht ht4]
  have hsk := abs_chSigma_mul_chKappa_sub_le hs
  have hσ := abs_chSigma_le (s := s) (by linarith)
  have hσ2 : chSigma s ^ 2 ≤ 9 * s ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) hσ 2
    rw [sq_abs, mul_pow, sq_abs] at this; linarith
  have ht8 : 0 < t ^ 8 := by positivity
  have hnum : |t ^ 4 * (chSigma s * chKappa s - 4 * s) - s * chSigma s ^ 2| ≤ 13 * |s| ^ 3 := by
    calc _ ≤ |t ^ 4 * (chSigma s * chKappa s - 4 * s)| + |s * chSigma s ^ 2| := abs_sub _ _
      _ = t ^ 4 * |chSigma s * chKappa s - 4 * s| + |s| * chSigma s ^ 2 := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ t ^ 4),
            abs_of_nonneg (sq_nonneg (chSigma s))]
      _ ≤ 1 * (4 * |s| ^ 3) + |s| * (9 * s ^ 2) := by gcongr
      _ = 13 * |s| ^ 3 := by rw [← sq_abs s]; ring
  have hq : 0 < t ^ 4 * (chSigma s ^ 2 + 4 * t ^ 4) := by positivity
  rw [abs_div, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ m * π / 8), abs_of_pos hq]
  rw [div_le_div_iff₀ hq ht8]
  have hπ := Real.pi_lt_d2
  have hmπ : m * π / 8 ≤ K * 3.15 := by
    have := mul_le_mul hm hπ.le Real.pi_pos.le (by positivity); nlinarith
  have hs3 := pow_nonneg (abs_nonneg s) 3
  calc m * π / 8 * |t ^ 4 * (chSigma s * chKappa s - 4 * s) - s * chSigma s ^ 2| * t ^ 8
      ≤ K * 3.15 * (13 * |s| ^ 3) * t ^ 8 := by gcongr
    _ ≤ 11 * K * |s| ^ 3 * (4 * t ^ 8) := by
        have : (0:ℝ) ≤ K * |s| ^ 3 * t ^ 8 := by positivity
        nlinarith
    _ ≤ 11 * K * |s| ^ 3 * (t ^ 4 * (chSigma s ^ 2 + 4 * t ^ 4)) := by
        have hden : 4 * t ^ 8 ≤ t ^ 4 * (chSigma s ^ 2 + 4 * t ^ 4) := by
          nlinarith [sq_nonneg (chSigma s), pow_pos ht 4]
        gcongr

end GeometryReal

/-! ## Factorization of the line integrand of `F_a` -/

/-- The pole order `m = 2a - 1` of `F_a` at the cusp `1`. -/
def chMa (a : ℝ) : ℝ := 2 * a - 1

/-- The saddle size `g₀ = 2^{-2a} P₀ e^{R₀}` of `F_a`. -/
def chG0a (a t : ℝ) : ℝ := (2 : ℝ) ^ (-(2 * a)) * chP0 t * Real.exp (chR0m (chMa a) t)

/-- The shifted-line integrand of `F_a` at its saddle frequency. -/
def chLineA (a t s : ℝ) : ℂ :=
  Complex.exp (-Complex.I * chUm (chMa a) t * s) *
    chargeTailC (thetaPowerForm a) ((s : ℂ) - (chBeta t : ℂ) * Complex.I)

theorem chG0a_pos (a t : ℝ) : 0 < chG0a a t := by
  unfold chG0a; have := chP0_pos (t := t); positivity

section Factorization

variable {a t : ℝ}

theorem chLineA_eq (ht : 0 < t) (ht2 : t ^ 2 ≤ 1 / 2) {s : ℝ} (hv4 : 4 < (chV t s).im) :
    chLineA a t s = (chG0a a t : ℂ) *
      (Real.exp ((chPsim (chMa a) t s).re - chR0m (chMa a) t) : ℂ) *
      (chA t s * Complex.exp (Complex.I * ((chPsim (chMa a) t s).im + chMa a * π / 8 : ℝ)) *
        (1 + powerChargeErr a (chV t s))) := by
  have ht4 : t ^ 4 ≤ 1 := by nlinarith
  have ht21 : t ^ 2 ≤ 1 := by linarith
  have hF : thetaPowerForm a
      (Complex.I * Complex.exp (2 * ((s : ℂ) - (chBeta t : ℂ) * Complex.I))) =
      Complex.exp (π * Complex.I * a / 4) * chP t s * (((2 : ℝ) ^ (1 - 2 * a) : ℝ) : ℂ) *
        Complex.exp ((1 - 2 * a) * π * Complex.I * chV t s / 4) *
        (1 + powerChargeErr a (chV t s)) := by
    rw [I_mul_cexp_line ht21, ← one_add_neg_one_div_chV ht ht4, thetaPowerForm_window a hv4]
    rfl
  have hz : Complex.exp (((s : ℂ) - (chBeta t : ℂ) * Complex.I) / 2) =
      (Real.exp (s / 2) : ℂ) * Complex.exp (-Complex.I * ((chBeta t / 2 : ℝ) : ℂ)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]; congr 1; push_cast; ring
  have hΨ : Complex.exp (-Complex.I * (chUm (chMa a) t : ℂ) * (s : ℂ)) *
      Complex.exp ((1 - 2 * a) * π * Complex.I * chV t s / 4) =
      (Real.exp (chPsim (chMa a) t s).re : ℂ) *
        Complex.exp (Complex.I * ((chPsim (chMa a) t s).im + chMa a * π / 8 : ℝ)) *
        Complex.exp (-Complex.I * ((chMa a * π / 8 : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    rw [show -Complex.I * (chUm (chMa a) t : ℂ) * (s : ℂ) +
        (1 - 2 * a) * π * Complex.I * chV t s / 4 = chPsim (chMa a) t s by
      unfold chPsim chMa; push_cast; ring]
    conv_lhs => rw [← Complex.re_add_im (chPsim (chMa a) t s)]
    rw [Complex.exp_add, ← Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]
    congr 2; push_cast; ring
  have key : Complex.exp (-Complex.I * ((chBeta t / 2 : ℝ) : ℂ)) *
      Complex.exp (-Complex.I * ((chMa a * π / 8 : ℝ) : ℂ)) * Complex.exp (π * Complex.I * a / 4) =
      Complex.exp (Complex.I * ((chTheta t / 2 : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    unfold chBeta chMa; push_cast; ring
  have hp : ((chP0 t : ℝ) : ℂ) * ((chP0 t : ℝ) : ℂ)⁻¹ = 1 :=
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr chP0_pos.ne')
  have hE : (Real.exp ((chPsim (chMa a) t s).re - chR0m (chMa a) t) : ℂ) *
      (Real.exp (chR0m (chMa a) t) : ℂ) = (Real.exp (chPsim (chMa a) t s).re : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]; congr 2; ring
  have h2 : (((2 : ℝ) ^ (1 - 2 * a) : ℝ) : ℂ) = 2 * (((2 : ℝ) ^ (-(2 * a)) : ℝ) : ℂ) := by
    rw [show 1 - 2 * a = 1 + -(2 * a) by ring, Real.rpow_add (by norm_num), Real.rpow_one]
    push_cast; ring
  unfold chLineA chargeTailC
  rw [hF, hz, h2]
  unfold chG0a chA
  simp only [Complex.ofReal_mul]
  set Es : ℂ := (Real.exp (s / 2) : ℂ)
  set Cb : ℂ := Complex.exp (-Complex.I * ((chBeta t / 2 : ℝ) : ℂ))
  set C7 : ℂ := Complex.exp (-Complex.I * ((chMa a * π / 8 : ℝ) : ℂ))
  set Ca : ℂ := Complex.exp (π * Complex.I * a / 4)
  set Ct : ℂ := Complex.exp (Complex.I * ((chTheta t / 2 : ℝ) : ℂ))
  set Cp : ℂ := Complex.exp (Complex.I * ((chPsim (chMa a) t s).im + chMa a * π / 8 : ℝ))
  set EP : ℂ := (Real.exp (chPsim (chMa a) t s).re : ℂ)
  set ER : ℂ := (Real.exp (chR0m (chMa a) t) : ℂ)
  set Ed : ℂ := (Real.exp ((chPsim (chMa a) t s).re - chR0m (chMa a) t) : ℂ)
  set pp : ℂ := ((chP0 t : ℝ) : ℂ)
  set X : ℂ := Complex.exp (-Complex.I * (chUm (chMa a) t : ℂ) * (s : ℂ))
  set Y : ℂ := Complex.exp ((1 - 2 * a) * π * Complex.I * chV t s / 4)
  set P : ℂ := chP t s
  set ε : ℂ := powerChargeErr a (chV t s)
  set c : ℂ := (((2 : ℝ) ^ (-(2 * a)) : ℝ) : ℂ)
  linear_combination (c * Es * Cb * Ca * P * (1 + ε)) * hΨ +
    (c * Es * P * (1 + ε) * EP * Cp) * key +
    (-(c * Es * P * (1 + ε) * Cp * Ct * ER * Ed)) * hp +
    (-(c * Es * P * (1 + ε) * Cp * Ct)) * hE

end Factorization

/-! ## Window estimates -/

section Window

variable {a t : ℝ}

/-- Smallness of the saddle parameter for `F_a`. -/
def chSmallA (a t : ℝ) : Prop := 0 < t ∧ t ^ 2 * (20000 * (1 + a)) ≤ 1

theorem chSmallA.t2 (ha : 0 ≤ a) (h : chSmallA a t) : t ^ 2 ≤ 1 / 20000 := by
  obtain ⟨_, h⟩ := h
  rw [le_div_iff₀ (by norm_num)]; nlinarith [sq_nonneg t]

theorem chSmallA.le (ha : 0 ≤ a) (h : chSmallA a t) : t ≤ 1 / 100 := by
  have h2 := h.t2 ha
  have ht := h.1
  nlinarith

theorem chV_im_ge_five (ha : 0 ≤ a) (h : chSmallA a t) {s : ℝ} (hs : |s| ≤ 2 * t ^ 2) :
    5 < (chV t s).im := by
  have ht0 := h.1
  have ht2 := h.t2 ha
  have hv := chV_im_ge_window ht0 (by linarith) hs
  have : 5 < 1 / (40 * t ^ 2) := by
    rw [lt_div_iff₀ (by positivity)]; nlinarith
  linarith

theorem norm_powerChargeErr_window (ha : 0 ≤ a) (h : chSmallA a t) {s : ℝ}
    (hs : |s| ≤ 2 * t ^ 2) : ‖powerChargeErr a (chV t s)‖ ≤ 1 / 8 := by
  have ht0 := h.1
  have ht2 := h.t2 ha
  have hv := chV_im_ge_window ht0 (by linarith) hs
  have hv5 := chV_im_ge_five ha h hs
  set Y : ℝ := (chV t s).im with hY
  have hYpos : 0 < Y := by linarith
  have he : Real.exp (-(π / 2 * Y)) ≤ 1 / Y := by
    refine (exp_neg_le_inv (by positivity)).trans ?_
    apply one_div_le_one_div_of_le hYpos
    nlinarith [Real.pi_gt_three]
  have h40 : 1 / Y ≤ 40 * t ^ 2 := by
    rw [div_le_iff₀ hYpos]
    rw [div_le_iff₀ (by positivity)] at hv
    linarith
  have hsm : 60 * (1 + a) * Real.exp (-(π / 2 * Y)) ≤ 1 / 8 := by
    have h1 : 60 * (1 + a) * Real.exp (-(π / 2 * Y)) ≤ 60 * (1 + a) * (40 * t ^ 2) :=
      mul_le_mul_of_nonneg_left (he.trans h40) (by positivity)
    have h2 := h.2
    nlinarith
  exact (norm_powerChargeErr_le ha (by linarith) (by linarith)).trans hsm

theorem norm_chLineA_le_window (ha : 0 ≤ a) (h : chSmallA a t) {s : ℝ} (hs : |s| ≤ 2 * t ^ 2) :
    ‖chLineA a t s‖ ≤
      9 / 8 * (chG0a a t * Real.exp ((chPsim (chMa a) t s).re - chR0m (chMa a) t)) := by
  have ht0 := h.1
  have ht2 := h.t2 ha
  have ht4 : t ^ 4 ≤ 1 := by nlinarith
  rw [chLineA_eq ht0 (by linarith) (by linarith [chV_im_ge_five ha h hs])]
  have hε := norm_powerChargeErr_window ha h hs
  have hA := norm_chA_le_one ht0 ht4 s
  have hG := (chG0a_pos a t).le
  rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hG, abs_of_pos (Real.exp_pos _)]
  have hc : ‖Complex.exp (Complex.I *
      (((chPsim (chMa a) t s).im + chMa a * π / 8 : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  rw [hc, mul_one]
  have h1 : ‖1 + powerChargeErr a (chV t s)‖ ≤ 9 / 8 := by
    refine le_trans (norm_add_le _ _) ?_; rw [norm_one]; linarith
  have hE := Real.exp_pos ((chPsim (chMa a) t s).re - chR0m (chMa a) t)
  calc chG0a a t * Real.exp ((chPsim (chMa a) t s).re - chR0m (chMa a) t) *
        (‖chA t s‖ * ‖1 + powerChargeErr a (chV t s)‖)
      ≤ chG0a a t * Real.exp ((chPsim (chMa a) t s).re - chR0m (chMa a) t) * (1 * (9 / 8)) := by
        gcongr
    _ = _ := by ring

/-- **Positivity on the core of radius `Λt³`.** -/
theorem half_le_re_chLineA_core (ha : 1 / 2 < a) (h : chSmallA a t) {K Λ : ℝ} (hK : 1 ≤ K)
    (hmK : chMa a ≤ 8 * K) (hΛ : 1 ≤ Λ) (hcore : t * (176 * K * Λ ^ 3) ≤ 1) {s : ℝ}
    (hs : |s| ≤ Λ * t ^ 3) :
    chG0a a t * Real.exp ((chPsim (chMa a) t s).re - chR0m (chMa a) t) / 2 ≤
      (chLineA a t s).re := by
  have ha0 : 0 ≤ a := by linarith
  have ht0 := h.1
  have htle := h.le ha0
  have ht1 : t ≤ 1 := by linarith
  have ht2 := h.t2 ha0
  have hm0 : 0 ≤ chMa a := by unfold chMa; linarith
  have hΛt : Λ * t ≤ 1 / 176 := by
    have hΛ3 : Λ ≤ Λ ^ 3 := by
      nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ Λ) (by linarith : (0:ℝ) ≤ Λ - 1))
        (by linarith : (0:ℝ) ≤ Λ + 1)]
    have h1 : Λ ≤ K * Λ ^ 3 := by
      have : 0 ≤ Λ ^ 3 := by positivity
      nlinarith
    have : t * (176 * Λ) ≤ 1 := le_trans (by nlinarith) hcore
    linarith
  have hs2 : |s| ≤ 2 * t ^ 2 := by
    have : Λ * t ^ 3 ≤ 2 * t ^ 2 := by
      have e : Λ * t ^ 3 = (Λ * t) * t ^ 2 := by ring
      rw [e]; nlinarith [pow_pos ht0 2]
    linarith
  have hs12 : |s| ≤ 1 / 2 := by nlinarith [pow_pos ht0 2]
  rw [chLineA_eq ht0 (by linarith) (by linarith [chV_im_ge_five ha0 h hs2])]
  set U : ℂ := chA t s * Complex.exp (Complex.I *
      (((chPsim (chMa a) t s).im + chMa a * π / 8 : ℝ) : ℂ)) *
    (1 + powerChargeErr a (chV t s)) with hU
  have hε := norm_powerChargeErr_window ha0 h hs2
  have hAd := norm_chA_sub_one_le ht0 ht1 hs12
  have hφ := abs_chPhim_le_real ht0 ht1 hm0 hmK hs12
  have hA8 : ‖chA t s - 1‖ ≤ 1 / 8 := by
    refine le_trans hAd ?_
    rw [div_le_iff₀ (by positivity)]
    have e : 10 * (Λ * t ^ 3) = 10 * (Λ * t) * t ^ 2 := by ring
    nlinarith [pow_pos ht0 2]
  have hφ16 : |(chPsim (chMa a) t s).im + chMa a * π / 8| ≤ 1 / 16 := by
    refine le_trans hφ ?_
    rw [div_le_iff₀ (by positivity)]
    have h3 : |s| ^ 3 ≤ (Λ * t ^ 3) ^ 3 := pow_le_pow_left₀ (abs_nonneg s) hs 3
    have e : 11 * K * (Λ * t ^ 3) ^ 3 = 11 * (t * (K * Λ ^ 3)) * t ^ 8 := by ring
    have h4 : t * (K * Λ ^ 3) ≤ 1 / 176 := by
      rw [le_div_iff₀ (by norm_num)]; linarith
    calc 11 * K * |s| ^ 3 ≤ 11 * K * (Λ * t ^ 3) ^ 3 := by gcongr
      _ = 11 * (t * (K * Λ ^ 3)) * t ^ 8 := e
      _ ≤ 11 * (1 / 176) * t ^ 8 := by gcongr
      _ = 1 / 16 * t ^ 8 := by ring
  have hexp1 : ‖Complex.exp (Complex.I *
      (((chPsim (chMa a) t s).im + chMa a * π / 8 : ℝ) : ℂ)) - 1‖ ≤ 1 / 8 := by
    have h := Complex.norm_exp_sub_one_le
      (x := Complex.I * (((chPsim (chMa a) t s).im + chMa a * π / 8 : ℝ) : ℂ))
      (by rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]; linarith)
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs] at h
    linarith
  have hc : ‖Complex.exp (Complex.I *
      (((chPsim (chMa a) t s).im + chMa a * π / 8 : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  have hU1 : ‖U - 1‖ ≤ 1 / 2 := by
    have e : U - 1 = (chA t s - 1) *
        Complex.exp (Complex.I * (((chPsim (chMa a) t s).im + chMa a * π / 8 : ℝ) : ℂ)) *
        (1 + powerChargeErr a (chV t s)) +
        (Complex.exp (Complex.I * (((chPsim (chMa a) t s).im + chMa a * π / 8 : ℝ) : ℂ)) - 1) *
          (1 + powerChargeErr a (chV t s)) + powerChargeErr a (chV t s) := by rw [hU]; ring
    have h1e : ‖1 + powerChargeErr a (chV t s)‖ ≤ 9 / 8 := by
      refine le_trans (norm_add_le _ _) ?_; rw [norm_one]; linarith
    rw [e]
    calc _ ≤ ‖(chA t s - 1) *
            Complex.exp (Complex.I * (((chPsim (chMa a) t s).im + chMa a * π / 8 : ℝ) : ℂ)) *
            (1 + powerChargeErr a (chV t s))‖ +
          ‖(Complex.exp (Complex.I * (((chPsim (chMa a) t s).im + chMa a * π / 8 : ℝ) : ℂ)) - 1) *
            (1 + powerChargeErr a (chV t s))‖ + ‖powerChargeErr a (chV t s)‖ := norm_add₃_le
      _ = ‖chA t s - 1‖ * 1 * ‖1 + powerChargeErr a (chV t s)‖ +
          ‖Complex.exp (Complex.I * (((chPsim (chMa a) t s).im + chMa a * π / 8 : ℝ) : ℂ)) - 1‖ *
            ‖1 + powerChargeErr a (chV t s)‖ + ‖powerChargeErr a (chV t s)‖ := by
          rw [norm_mul, norm_mul, norm_mul, hc]
      _ ≤ 1 / 8 * 1 * (9 / 8) + 1 / 8 * (9 / 8) + 1 / 8 := by gcongr
      _ ≤ 1 / 2 := by norm_num
  have hReU : 1 / 2 ≤ U.re := by
    have h := Complex.abs_re_le_norm (U - 1)
    rw [Complex.sub_re, Complex.one_re] at h
    have := abs_le.mp (le_trans h hU1)
    linarith [this.1]
  have hG := (chG0a_pos a t).le
  rw [← Complex.ofReal_mul, Complex.re_ofReal_mul]
  have hpos : 0 ≤ chG0a a t * Real.exp ((chPsim (chMa a) t s).re - chR0m (chMa a) t) :=
    mul_nonneg hG (Real.exp_pos _).le
  nlinarith

end Window

end

end RHTower
