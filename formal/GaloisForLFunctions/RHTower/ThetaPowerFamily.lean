import GaloisForLFunctions.RHTower.ThetaHauptmodulLogarithm
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspChargeWindowLaw
import GaloisForLFunctions.RHTower.ThetaGroupFormCuspBounds

/-!
# The theta-power family `F_a = θ₃ h^{a/4} = θ₃^{1-2a} (θ₂θ₄)^a`

For real `a` put `F_a(τ) = θ₃(τ) exp((a/4) log h(τ))` with the Hauptmodul logarithm normalized
real on the imaginary axis.  Then `F_a` is holomorphic on the upper half-plane, has exactly the theta
inversion law `F_a(-1/τ) = (-iτ)^{1/2} F_a(τ)`, has modulus `|θ₃| |h|^{a/4}`, and decays at the
cusp `∞` at the rate `πa/4`.

At the cusp `1` the logarithm of `h` is exactly `iπ - 8 log 2 - 2πiv + Log Q(v)` on `Im v > 4`,
`τ = 1 - 1/v`, where `Q = 256 e^{2πiv} θ₄⁴θ₃⁴/θ₂⁸ → 1`: both sides are logarithms of the same
function on a connected set, and they agree at a point of the unit circle, where `log h` is real.
Hence the **window law**

`F_a(1 - 1/v) = e^{iπa/4} (-iv)^{1/2} 2^{1-2a} e^{(1-2a)πiv/4} (1 + ε_a(v))`,

with `ε_a(v) → 0`.  The cusp order at `1` is `m = 2a - 1`: a zero for `a < 1/2`, a pole for
`a > 1/2`, and a finite nonzero value at `a = 1/2`.
-/

open Complex
open scoped Real

namespace RHTower

noncomputable section

open Bottcher

/-- The theta-power form `F_a = θ₃ · exp((a/4) log h)`. -/
def thetaPowerForm (a : ℝ) (τ : ℂ) : ℂ :=
  thetaThree τ * Complex.exp (((a / 4 : ℝ) : ℂ) * hauptmodulLog τ)

theorem differentiableOn_thetaPowerForm (a : ℝ) :
    DifferentiableOn ℂ (thetaPowerForm a) modUpperSet := by
  intro τ hτ
  have hτ' : 0 < τ.im := hτ
  have h3 : DifferentiableAt ℂ thetaThree τ := differentiableAt_thetaThree hτ'
  have hL : DifferentiableAt ℂ hauptmodulLog τ :=
    (differentiableOn_hauptmodulLog τ hτ).differentiableAt (isOpen_modUpperSet.mem_nhds hτ)
  exact (h3.mul ((hL.const_mul _).cexp)).differentiableWithinAt

theorem thetaPowerForm_zero (τ : ℂ) : thetaPowerForm 0 τ = thetaThree τ := by
  simp [thetaPowerForm]

/-- **Theta inversion law.** -/
theorem thetaPowerForm_S (a : ℝ) {τ : ℂ} (hτ : 0 < τ.im) :
    thetaPowerForm a (-1 / τ) = (-I * τ) ^ (1 / 2 : ℂ) * thetaPowerForm a τ := by
  have hτ0 : τ ≠ 0 := fun h => by rw [h] at hτ; simp at hτ
  unfold thetaPowerForm
  rw [thetaThree_S τ hτ0, hauptmodulLog_S hτ]
  ring

theorem norm_thetaPowerForm {a : ℝ} {τ : ℂ} (hτ : 0 < τ.im) :
    ‖thetaPowerForm a τ‖ = ‖thetaThree τ‖ * ‖thetaGroupHauptmodul τ‖ ^ (a / 4) := by
  unfold thetaPowerForm
  rw [norm_mul, norm_exp_mul_hauptmodulLog hτ]

theorem thetaPowerForm_ne_zero (a : ℝ) {τ : ℂ} (hτ : 0 < τ.im) : thetaPowerForm a τ ≠ 0 := by
  unfold thetaPowerForm
  exact mul_ne_zero (thetaThree_ne_zero_of_im_pos hτ) (Complex.exp_ne_zero _)

theorem thetaThree_add_two (τ : ℂ) : thetaThree (τ + 2) = thetaThree τ := by
  rw [show τ + 2 = (τ + 1) + 1 by ring, thetaThree_add_one, thetaFour_add_one]

/-- The modulus of `F_a` is two-periodic. -/
theorem norm_thetaPowerForm_add_two (a : ℝ) {τ : ℂ} (hτ : 0 < τ.im) :
    ‖thetaPowerForm a (τ + 2)‖ = ‖thetaPowerForm a τ‖ := by
  have hτ2 : 0 < (τ + 2).im := by simpa using hτ
  rw [norm_thetaPowerForm hτ2, norm_thetaPowerForm hτ, thetaThree_add_two,
    thetaGroupHauptmodul_add_two]

/-- `F_a` is real on the positive imaginary axis. -/
theorem thetaPowerForm_I_mul_real (a : ℝ) {y : ℝ} (hy : 0 < y) :
    thetaPowerForm a (I * (y : ℂ)) = ((thetaPowerForm a (I * (y : ℂ))).re : ℂ) := by
  have h3 : thetaThree (I * (y : ℂ)) = ((thetaThree (I * (y : ℂ))).re : ℂ) :=
    theta_I_mul_real_eq_re thetaThree_conj y
  have hL : hauptmodulLog (I * (y : ℂ)) = ((hauptmodulLog (I * (y : ℂ))).re : ℂ) := by
    apply Complex.ext <;> simp [hauptmodulLog_I_mul_im hy]
  have e : thetaPowerForm a (I * (y : ℂ)) =
      (((thetaThree (I * (y : ℂ))).re * Real.exp (a / 4 * (hauptmodulLog (I * (y : ℂ))).re) : ℝ) : ℂ) := by
    unfold thetaPowerForm
    rw [h3, hL]
    push_cast
    simp
  rw [e, Complex.ofReal_re]

/-- The axis form of the inversion law. -/
theorem thetaPowerForm_axis (a : ℝ) (x : ℝ) :
    thetaPowerForm a (modAxisPoint (-x)) = (Real.exp x : ℂ) * thetaPowerForm a (modAxisPoint x) := by
  have hp : 0 < (modAxisPoint x).im := modAxisPoint_mem x
  have hinv : modAxisPoint (-x) = -1 / modAxisPoint x := by
    unfold modAxisPoint
    have hne : (Real.exp (2 * x) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
    rw [eq_div_iff (mul_ne_zero I_ne_zero hne)]
    have : (Real.exp (2 * -x) : ℂ) * (Real.exp (2 * x) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]; simp
    calc I * (Real.exp (2 * -x) : ℂ) * (I * (Real.exp (2 * x) : ℂ)) =
        (I * I) * ((Real.exp (2 * -x) : ℂ) * (Real.exp (2 * x) : ℂ)) := by ring
      _ = -1 := by rw [I_mul_I, this]; ring
  rw [hinv, thetaPowerForm_S a hp]
  congr 1
  have e : -I * modAxisPoint x = ((Real.exp (2 * x) : ℝ) : ℂ) := by
    unfold modAxisPoint; rw [← mul_assoc, neg_mul, I_mul_I]; ring
  rw [e, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (Real.exp_pos _).le, ← Real.exp_mul]
  congr 2; ring

/-! ## Decay at the cusp `∞` -/

/-- The cusp constant of `F_a` at `∞`. -/
def thetaPowerCuspConstant (a : ℝ) : ℝ := 2 * (4096 * thetaTwoCuspConstant ^ 4) ^ (a / 4)

/-- **Decay at `∞` at the rate `πa/4`.** -/
theorem norm_thetaPowerForm_le_cusp {a : ℝ} (ha : 0 ≤ a) {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖thetaPowerForm a τ‖ ≤ thetaPowerCuspConstant a * Real.exp (-(π * a / 4) * τ.im) := by
  have hτ0 : 0 < τ.im := by linarith
  rw [norm_thetaPowerForm hτ0]
  have h3 := norm_thetaThree_le_two hτ
  have hh := norm_thetaGroupHauptmodul_le hτ
  set Ch : ℝ := 4096 * thetaTwoCuspConstant ^ 4 with hCh
  have hCh0 : 0 ≤ Ch := by have := thetaTwoCuspConstant_nonneg; positivity
  have hpow : ‖thetaGroupHauptmodul τ‖ ^ (a / 4) ≤ (Ch * Real.exp (-π * τ.im)) ^ (a / 4) :=
    Real.rpow_le_rpow (norm_nonneg _) hh (by linarith)
  have hsplit : (Ch * Real.exp (-π * τ.im)) ^ (a / 4) =
      Ch ^ (a / 4) * Real.exp (-(π * a / 4) * τ.im) := by
    rw [Real.mul_rpow hCh0 (Real.exp_pos _).le, ← Real.exp_mul]
    congr 2; ring
  unfold thetaPowerCuspConstant
  rw [← hCh]
  calc ‖thetaThree τ‖ * ‖thetaGroupHauptmodul τ‖ ^ (a / 4)
      ≤ 2 * (Ch ^ (a / 4) * Real.exp (-(π * a / 4) * τ.im)) := by
        rw [← hsplit]
        exact mul_le_mul h3 hpow (Real.rpow_nonneg (norm_nonneg _) _) (by norm_num)
    _ = 2 * Ch ^ (a / 4) * Real.exp (-(π * a / 4) * τ.im) := by ring

/-! ## The branch of `log h` at the cusp `1` -/

/-- `Q(v) = 256 e^{2πiv} θ₄⁴θ₃⁴/θ₂⁸`, the normalized value of `-h(1-1/v)`. -/
def cuspOneQuot (v : ℂ) : ℂ :=
  256 * Complex.exp (2 * π * I * v) * thetaFour v ^ 4 * thetaThree v ^ 4 / thetaTwo v ^ 8

theorem neg_one_div_im_pos {v : ℂ} (hv : 0 < v.im) : 0 < (-1 / v).im := by
  have hne : v ≠ 0 := fun h => by rw [h] at hv; simp at hv
  rw [neg_div, Complex.neg_im, one_div, Complex.inv_im, neg_div, neg_neg]
  exact div_pos hv (Complex.normSq_pos.mpr hne)

theorem one_add_neg_one_div_im_pos {v : ℂ} (hv : 0 < v.im) : 0 < (1 + -1 / v).im := by
  simpa using neg_one_div_im_pos hv

/-- `h(1 - 1/v) = exp(iπ - 8 log 2 - 2πiv) Q(v)`. -/
theorem thetaGroupHauptmodul_cusp_one {v : ℂ} (hv : 0 < v.im) :
    thetaGroupHauptmodul (1 + -1 / v) =
      Complex.exp (π * I - 8 * Real.log 2 - 2 * π * I * v) * cuspOneQuot v := by
  have hv0 : v ≠ 0 := fun h => by rw [h] at hv; simp at hv
  set τ₀ : ℂ := -1 / v with hτ₀
  set P : ℂ := (-Complex.I * v) ^ (1 / 2 : ℂ) with hP
  have hIv : Complex.I / v = (-Complex.I * v)⁻¹ := by
    field_simp; exact Complex.I_sq
  have hQ : (Complex.I / v) ^ (1 / 2 : ℂ) = P⁻¹ := by
    rw [hIv, Complex.inv_cpow _ _ (arg_neg_I_mul_ne_pi hv)]
  have hP0 : P ≠ 0 := by
    rw [hP]; intro h
    rw [Complex.cpow_eq_zero_iff] at h
    exact (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hv0) h.1
  have h2 := thetaTwo_S v hv0
  have h3 := thetaThree_S v hv0
  have h4 := thetaFour_S v hv0
  rw [hQ, one_div, inv_inv] at h2 h4
  rw [← hP] at h3
  have ht2 : thetaTwo v ≠ 0 := thetaTwo_ne_zero_of_im_pos hv
  have hh : thetaGroupHauptmodul (1 + τ₀) =
      -(thetaTwo τ₀ ^ 4) * thetaThree τ₀ ^ 4 / thetaFour τ₀ ^ 8 := by
    unfold thetaGroupHauptmodul
    rw [add_comm, thetaThree_add_one, thetaTwo_pow4_add_one, thetaFour_add_one]
  rw [hh, h2, h3, h4]
  unfold cuspOneQuot
  have hlog2 : Complex.exp (8 * (Real.log 2 : ℂ)) = 256 := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, ← Complex.ofReal_exp,
      show (8 : ℝ) * Real.log 2 = Real.log (2 ^ 8) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_log (by norm_num)]
    norm_num
  have hsplit : Complex.exp (π * I - 8 * Real.log 2 - 2 * π * I * v) =
      -(Complex.exp (2 * π * I * v))⁻¹ * (Complex.exp (8 * (Real.log 2 : ℂ)))⁻¹ := by
    rw [show (π : ℂ) * I - 8 * Real.log 2 - 2 * π * I * v =
        π * I + (-(8 * (Real.log 2 : ℂ)) + -(2 * π * I * v)) by ring,
      Complex.exp_add, Complex.exp_add, Complex.exp_neg, Complex.exp_neg, Complex.exp_pi_mul_I]
    ring
  rw [hsplit, hlog2]
  have hE : Complex.exp (2 * π * I * v) ≠ 0 := Complex.exp_ne_zero _
  field_simp

/-! ### The normalized quotient is close to `1` -/

theorem jacobiThetaTailConstant_le_three : jacobiThetaTailConstant ≤ 3 := by
  unfold jacobiThetaTailConstant
  have h := exp_neg_pi_lt_twentieth
  rw [div_le_iff₀ (by linarith)]
  linarith

theorem exp_neg_two_pi_lt : Real.exp (-(2 * π)) < 1 / 400 := by
  have h := exp_neg_pi_lt_twentieth
  have hpos := Real.exp_pos (-π)
  have e : Real.exp (-(2 * π)) = Real.exp (-π) * Real.exp (-π) := by
    rw [← Real.exp_add]; ring_nf
  rw [e]; nlinarith

theorem norm_one_add_pow_sub_one_le_twice {w : ℂ} {N : ℕ} (hw : N * ‖w‖ ≤ 1) :
    ‖(1 + w) ^ N - 1‖ ≤ 2 * (N * ‖w‖) := by
  have h1 := norm_one_add_pow_sub_one_le_charge w N
  have h2 : (1 + ‖w‖) ^ N ≤ Real.exp (N * ‖w‖) := by
    calc (1 + ‖w‖) ^ N ≤ Real.exp ‖w‖ ^ N :=
          pow_le_pow_left₀ (by linarith [norm_nonneg w]) (by linarith [Real.add_one_le_exp ‖w‖]) N
      _ = Real.exp (N * ‖w‖) := by rw [← Real.exp_nat_mul]
  have hNw : 0 ≤ (N : ℝ) * ‖w‖ := mul_nonneg (Nat.cast_nonneg N) (norm_nonneg w)
  have h3 := Real.abs_exp_sub_one_le (x := N * ‖w‖) (by rw [abs_of_nonneg hNw]; exact hw)
  rw [abs_of_nonneg hNw] at h3
  have h4 : Real.exp (N * ‖w‖) - 1 ≤ 2 * (N * ‖w‖) := by
    have := le_abs_self (Real.exp (N * ‖w‖) - 1); linarith
  linarith

/-- Quantitative approach of `Q` to `1` on `Im v ≥ 4`. -/
theorem norm_cuspOneQuot_sub_one_le {v : ℂ} (hv : 4 ≤ v.im) :
    ‖cuspOneQuot v - 1‖ ≤ 50 * Real.exp (-(π / 2 * v.im)) := by
  have hv0 : 0 < v.im := by linarith
  set e : ℝ := Real.exp (-(π / 2 * v.im)) with he
  have hepos : 0 < e := Real.exp_pos _
  have he400 : e < 1 / 400 := by
    have : e ≤ Real.exp (-(2 * π)) := Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    linarith [exp_neg_two_pi_lt]
  have hsq : Real.exp (-π * v.im) = e * e := by rw [he, ← Real.exp_add]; congr 1; ring
  have hK := jacobiThetaTailConstant_le_three
  have hKpos := jacobiThetaTailConstant_pos
  set x : ℂ := thetaThree v - 1 with hx_def
  set y : ℂ := thetaFour v - 1 with hy_def
  set z : ℂ := jacobiTheta₂ (v / 2) v / 2 - 1 with hz_def
  have hx : ‖x‖ ≤ 3 * (e * e) := by
    have := norm_thetaThree_sub_one_le (τ := v) (by linarith)
    rw [hsq] at this
    exact this.trans (mul_le_mul_of_nonneg_right hK (by positivity))
  have hy : ‖y‖ ≤ 3 * (e * e) := by
    have := norm_thetaFour_sub_one_le (τ := v) (by linarith)
    rw [hsq] at this
    exact this.trans (mul_le_mul_of_nonneg_right hK (by positivity))
  have hz : ‖z‖ ≤ 3 / 2 * e := by
    have h1 := norm_jacobiTheta₂_half_sub_two_le_exp (τ := v) (by linarith)
    have hzeq : z = (jacobiTheta₂ (v / 2) v - 2) / 2 := by rw [hz_def]; ring
    rw [hzeq, norm_div, Complex.norm_ofNat]
    rw [← he] at h1; linarith
  set w : ℂ := x + y + x * y with hw
  have hwb : ‖w‖ ≤ 9 * (e * e) := by
    have hy1 : ‖y‖ ≤ 1 := by nlinarith
    have hxy : ‖x * y‖ ≤ ‖x‖ := by
      rw [norm_mul]; nlinarith [norm_nonneg x]
    calc ‖w‖ ≤ ‖x‖ + ‖y‖ + ‖x * y‖ := by
          refine le_trans (norm_add_le _ _) ?_; linarith [norm_add_le x y]
      _ ≤ 9 * (e * e) := by linarith
  have h3 : thetaThree v = 1 + x := by rw [hx_def]; ring
  have h4 : thetaFour v = 1 + y := by rw [hy_def]; ring
  have hJ : jacobiTheta₂ (v / 2) v = 2 * (1 + z) := by rw [hz_def]; ring
  have hθ2 : thetaTwo v = Complex.exp (π * I * v / 4) * jacobiTheta₂ (v / 2) v := rfl
  have hz1 : 1 - ‖z‖ ≤ ‖(1 : ℂ) + z‖ := by
    have h5 : ‖(1:ℂ)‖ ≤ ‖1 + z‖ + ‖z‖ := by
      calc ‖(1:ℂ)‖ = ‖(1 + z) + -z‖ := by ring_nf
        _ ≤ ‖1 + z‖ + ‖-z‖ := norm_add_le _ _
        _ = ‖1 + z‖ + ‖z‖ := by rw [norm_neg]
    rw [norm_one] at h5; linarith
  have hz0 : (1 : ℂ) + z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz1; linarith
  have hQeq : cuspOneQuot v = (1 + w) ^ 4 / (1 + z) ^ 8 := by
    unfold cuspOneQuot
    rw [hθ2, hJ, h3, h4, hw]
    have hE8 : Complex.exp (π * I * v / 4) ^ 8 = Complex.exp (2 * π * I * v) := by
      rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
    rw [mul_pow, mul_pow, hE8]
    have hE : Complex.exp (2 * π * I * v) ≠ 0 := Complex.exp_ne_zero _
    have hz8 : (1 + z) ^ 8 ≠ 0 := pow_ne_zero _ hz0
    field_simp
    ring
  have hA : ‖(1 + w) ^ 4 - 1‖ ≤ 2 * (4 * ‖w‖) := by
    apply norm_one_add_pow_sub_one_le_twice
    push_cast; nlinarith
  have hB : ‖(1 + z) ^ 8 - 1‖ ≤ 2 * (8 * ‖z‖) := by
    apply norm_one_add_pow_sub_one_le_twice
    push_cast; nlinarith
  have hden : 1 / 2 ≤ ‖(1 + z) ^ 8‖ := by
    have : ‖(1:ℂ)‖ ≤ ‖(1 + z) ^ 8‖ + ‖(1 + z) ^ 8 - 1‖ := by
      calc ‖(1:ℂ)‖ = ‖(1 + z) ^ 8 - ((1 + z) ^ 8 - 1)‖ := by ring_nf
        _ ≤ ‖(1 + z) ^ 8‖ + ‖(1 + z) ^ 8 - 1‖ := norm_sub_le _ _
    rw [norm_one] at this
    nlinarith
  have hQ1 : cuspOneQuot v - 1 = (((1 + w) ^ 4 - 1) - ((1 + z) ^ 8 - 1)) / (1 + z) ^ 8 := by
    rw [hQeq]; field_simp; ring
  rw [hQ1, norm_div, div_le_iff₀ (by linarith)]
  calc ‖((1 + w) ^ 4 - 1) - ((1 + z) ^ 8 - 1)‖
      ≤ ‖(1 + w) ^ 4 - 1‖ + ‖(1 + z) ^ 8 - 1‖ := norm_sub_le _ _
    _ ≤ 2 * (4 * (9 * (e * e))) + 2 * (8 * (3 / 2 * e)) := by nlinarith
    _ ≤ 50 * e * (1 / 2) := by nlinarith
    _ ≤ 50 * e * ‖(1 + z) ^ 8‖ := by gcongr

theorem cuspOneQuot_re_pos {v : ℂ} (hv : 4 ≤ v.im) : 0 < (cuspOneQuot v).re := by
  have h := norm_cuspOneQuot_sub_one_le hv
  have he : Real.exp (-(π / 2 * v.im)) < 1 / 400 := by
    have : Real.exp (-(π / 2 * v.im)) ≤ Real.exp (-(2 * π)) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    linarith [exp_neg_two_pi_lt]
  have hre := Complex.abs_re_le_norm (cuspOneQuot v - 1)
  rw [Complex.sub_re, Complex.one_re] at hre
  have := abs_le.mp (hre.trans h)
  linarith [this.1]

theorem differentiableAt_cuspOneQuot {v : ℂ} (hv : 0 < v.im) :
    DifferentiableAt ℂ cuspOneQuot v := by
  unfold cuspOneQuot
  have h2 := differentiableAt_thetaTwo hv
  have h3 := differentiableAt_thetaThree hv
  have h4 := differentiableAt_thetaFour hv
  have hE : DifferentiableAt ℂ (fun v : ℂ => Complex.exp (2 * π * I * v)) v := by fun_prop
  exact ((((differentiableAt_const _).mul hE).mul (h4.pow 4)).mul (h3.pow 4)).div (h2.pow 8)
    (pow_ne_zero _ (thetaTwo_ne_zero_of_im_pos hv))

/-- The half-plane `Im v > 4`. -/
def cuspOneWindowSet : Set ℂ := {v : ℂ | 4 < v.im}

theorem isOpen_cuspOneWindowSet : IsOpen cuspOneWindowSet :=
  isOpen_lt continuous_const Complex.continuous_im

theorem isPreconnected_cuspOneWindowSet : IsPreconnected cuspOneWindowSet := by
  apply Convex.isPreconnected
  intro x hx y hy a b ha hb hab
  show 4 < (a • x + b • y).im
  have hx' : 4 < x.im := hx
  have hy' : 4 < y.im := hy
  simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero]
  rcases eq_or_lt_of_le ha with h | h
  · subst h; simp at hab; subst hab; simpa using hy'
  · nlinarith [mul_lt_mul_of_pos_left hx' h, mul_le_mul_of_nonneg_left hy'.le hb]

/-- **The branch of `log h` at the cusp `1`.** -/
theorem hauptmodulLog_cusp_one {v : ℂ} (hv : 4 < v.im) :
    hauptmodulLog (1 + -1 / v) =
      π * I - 8 * Real.log 2 - 2 * π * I * v + Complex.log (cuspOneQuot v) := by
  set A : ℂ → ℂ := fun v => hauptmodulLog (1 + -1 / v) with hA
  set B : ℂ → ℂ := fun v =>
    π * I - 8 * Real.log 2 - 2 * π * I * v + Complex.log (cuspOneQuot v) with hB
  have hmem : ∀ v ∈ cuspOneWindowSet, 0 < v.im := fun v hv => by
    have : 4 < v.im := hv; linarith
  have hslit : ∀ v ∈ cuspOneWindowSet, cuspOneQuot v ∈ Complex.slitPlane := fun v hv =>
    Or.inl (cuspOneQuot_re_pos (le_of_lt hv))
  have hdA : DifferentiableOn ℂ A cuspOneWindowSet := by
    intro v hv
    have hv' := hmem v hv
    have hne : v ≠ 0 := fun h => by rw [h] at hv'; simp at hv'
    have hin : DifferentiableAt ℂ (fun v : ℂ => 1 + -1 / v) v :=
      (differentiableAt_const _).add ((differentiableAt_const _).div differentiableAt_id hne)
    have hpt : (1 + -1 / v) ∈ modUpperSet := one_add_neg_one_div_im_pos hv'
    have hout : DifferentiableAt ℂ hauptmodulLog (1 + -1 / v) :=
      (differentiableOn_hauptmodulLog _ hpt).differentiableAt (isOpen_modUpperSet.mem_nhds hpt)
    exact (hout.comp v hin).differentiableWithinAt
  have hdB : DifferentiableOn ℂ B cuspOneWindowSet := by
    intro v hv
    have hv' := hmem v hv
    have hlog : DifferentiableAt ℂ (fun v => Complex.log (cuspOneQuot v)) v :=
      (differentiableAt_cuspOneQuot hv').clog (hslit v hv)
    exact ((by fun_prop : DifferentiableAt ℂ
      (fun v : ℂ => π * I - 8 * Real.log 2 - 2 * π * I * v) v).add hlog).differentiableWithinAt
  have hexp : ∀ v ∈ cuspOneWindowSet, Complex.exp (A v) = Complex.exp (B v) := by
    intro v hv
    have hv' := hmem v hv
    have hQne : cuspOneQuot v ≠ 0 := Complex.slitPlane_ne_zero (hslit v hv)
    simp only [hA, hB]
    rw [exp_hauptmodulLog (one_add_neg_one_div_im_pos hv'), thetaGroupHauptmodul_cusp_one hv',
      Complex.exp_add, Complex.exp_log hQne]
  -- the base point on the unit circle
  set v₀ : ℂ := 1 / 2 + 5 * I with hv₀
  have hv₀mem : v₀ ∈ cuspOneWindowSet := by show (4 : ℝ) < v₀.im; simp [hv₀]; norm_num
  have hconst := log_sub_eq_const isOpen_cuspOneWindowSet isPreconnected_cuspOneWindowSet
    hdA hdB hexp hv₀mem
  -- at `v₀`, `1 - 1/v₀` lies on the unit circle, where `log h` is real
  have hv₀ne : v₀ ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp [hv₀] at this
  have hcirc : ‖1 + -1 / v₀‖ = 1 := by
    have e : 1 + -1 / v₀ = (v₀ - 1) / v₀ := by field_simp; ring
    rw [e, norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.mpr hv₀ne)]
    rw [hv₀]
    have h1 : (1 / 2 + 5 * I : ℂ) - 1 = -(1 / 2) + 5 * I := by ring
    rw [h1]
    have n1 : ‖(-(1 / 2) + 5 * I : ℂ)‖ ^ 2 = ‖(1 / 2 + 5 * I : ℂ)‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
      simp [Complex.normSq_apply]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by norm_num : (2:ℕ) ≠ 0)).mp n1
  have hAim : (A v₀).im = 0 := hauptmodulLog_im_of_norm_eq_one
    (one_add_neg_one_div_im_pos (hmem v₀ hv₀mem)) hcirc
  have hBim : |(B v₀).im| < π / 2 := by
    simp only [hB]
    have hre := cuspOneQuot_re_pos (v := v₀) (le_of_lt hv₀mem)
    have harg := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
    have e : (π * I - 8 * Real.log 2 - 2 * π * I * v₀ + Complex.log (cuspOneQuot v₀)).im =
        (cuspOneQuot v₀).arg := by
      simp [hv₀, Complex.log_im, Complex.mul_im, Complex.mul_re]
      ring
    rw [e]; exact harg
  -- the constant `A v₀ - B v₀` lies in `2πiℤ` and has imaginary part in `(-π/2, π/2)`
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp (by
    rw [Complex.exp_sub, hexp v₀ hv₀mem, div_self (Complex.exp_ne_zero _)] :
      Complex.exp (A v₀ - B v₀) = 1)
  have himn : (A v₀ - B v₀).im = n * (2 * π) := by
    rw [hn]; simp
  have hn0 : n = 0 := by
    rw [Complex.sub_im, hAim, zero_sub] at himn
    have habs : |(n : ℝ) * (2 * π)| < π / 2 := by
      rw [← himn, abs_neg]; exact hBim
    by_contra hne
    have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      have : (1 : ℤ) ≤ |n| := Int.one_le_abs hne
      exact_mod_cast this
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at habs
    nlinarith [Real.pi_pos]
  have hzero : A v₀ - B v₀ = 0 := by rw [hn, hn0]; simp
  have := hconst v hv
  rw [hzero] at this
  exact sub_eq_zero.mp this

/-! ## The window law at the cusp `1` -/

/-- The normalized error of the window law. -/
def powerChargeErr (a : ℝ) (v : ℂ) : ℂ :=
  jacobiTheta₂ (v / 2) v / 2 * Complex.exp (((a / 4 : ℝ) : ℂ) * Complex.log (cuspOneQuot v)) - 1

/-- **Exact window law of `F_a` at the cusp `1`.** -/
theorem thetaPowerForm_window (a : ℝ) {v : ℂ} (hv : 4 < v.im) :
    thetaPowerForm a (1 + -1 / v) = Complex.exp (π * I * a / 4) * (-I * v) ^ (1 / 2 : ℂ) *
      ((2 : ℝ) ^ (1 - 2 * a) : ℝ) * Complex.exp ((1 - 2 * a) * π * I * v / 4) *
        (1 + powerChargeErr a v) := by
  have hv' : 0 < v.im := by linarith
  have hv0 : v ≠ 0 := fun h => by rw [h] at hv'; simp at hv'
  set P : ℂ := (-Complex.I * v) ^ (1 / 2 : ℂ) with hP
  have hIv : Complex.I / v = (-Complex.I * v)⁻¹ := by
    field_simp; exact Complex.I_sq
  have hQ : (Complex.I / v) ^ (1 / 2 : ℂ) = P⁻¹ := by
    rw [hIv, Complex.inv_cpow _ _ (arg_neg_I_mul_ne_pi hv')]
  have h4 := thetaFour_S v hv0
  rw [hQ, one_div, inv_inv] at h4
  have hθ3 : thetaThree (1 + -1 / v) = P * thetaTwo v := by
    rw [add_comm, thetaThree_add_one, h4]
  have hθ2 : thetaTwo v = Complex.exp (π * I * v / 4) * jacobiTheta₂ (v / 2) v := rfl
  unfold thetaPowerForm powerChargeErr
  rw [hθ3, hauptmodulLog_cusp_one hv, hθ2, add_sub_cancel]
  have h2 : (((2 : ℝ) ^ (1 - 2 * a) : ℝ) : ℂ) =
      Complex.exp ((1 - 2 * a) * (Real.log 2 : ℂ)) := by
    rw [Real.rpow_def_of_pos (by norm_num), Complex.ofReal_exp]
    push_cast; ring_nf
  rw [h2]
  have e1 : ((a / 4 : ℝ) : ℂ) * (π * I - 8 * Real.log 2 - 2 * π * I * v +
      Complex.log (cuspOneQuot v)) =
      (π * I * a / 4) + (-(2 * a) * (Real.log 2 : ℂ)) + (-(a / 2) * π * I * v) +
        ((a / 4 : ℝ) : ℂ) * Complex.log (cuspOneQuot v) := by
    push_cast; ring
  rw [e1, Complex.exp_add, Complex.exp_add, Complex.exp_add]
  have e2 : Complex.exp (π * I * v / 4) * Complex.exp (-(a / 2) * π * I * v) =
      Complex.exp ((1 - 2 * a) * π * I * v / 4) := by
    rw [← Complex.exp_add]; congr 1; ring
  have e3 : Complex.exp ((1 - 2 * a) * (Real.log 2 : ℂ)) =
      2 * Complex.exp (-(2 * a) * (Real.log 2 : ℂ)) := by
    rw [show (1 - 2 * a) * (Real.log 2 : ℂ) = (Real.log 2 : ℂ) + -(2 * a) * (Real.log 2 : ℂ) by
      ring, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log (by norm_num)]
    push_cast; ring
  rw [e3, ← e2]
  ring

/-- **Size of the window error.** -/
theorem norm_powerChargeErr_le {a : ℝ} (ha : 0 ≤ a) {v : ℂ} (hv : 4 ≤ v.im)
    (hsmall : 60 * (1 + a) * Real.exp (-(π / 2 * v.im)) ≤ 1) :
    ‖powerChargeErr a v‖ ≤ 60 * (1 + a) * Real.exp (-(π / 2 * v.im)) := by
  set e : ℝ := Real.exp (-(π / 2 * v.im)) with he
  have hepos : 0 < e := Real.exp_pos _
  have he400 : e < 1 / 400 := by
    have : e ≤ Real.exp (-(2 * π)) := Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    linarith [exp_neg_two_pi_lt]
  have hQ := norm_cuspOneQuot_sub_one_le hv
  rw [← he] at hQ
  set q : ℂ := cuspOneQuot v - 1 with hq
  have hq12 : ‖q‖ ≤ 1 / 2 := by nlinarith
  have hlog : ‖Complex.log (cuspOneQuot v)‖ ≤ 3 / 2 * ‖q‖ := by
    have h := Complex.norm_log_one_add_half_le_self hq12
    rwa [hq, add_sub_cancel] at h
  set u : ℂ := ((a / 4 : ℝ) : ℂ) * Complex.log (cuspOneQuot v) with hu
  have hu1 : ‖u‖ ≤ a / 4 * (3 / 2 * (50 * e)) := by
    rw [hu, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (hlog.trans (by nlinarith)) (by positivity)
  have hu1' : ‖u‖ ≤ 1 := by nlinarith
  have hexp : ‖Complex.exp u - 1‖ ≤ 2 * ‖u‖ := by
    have := Complex.norm_exp_sub_one_le hu1'
    linarith
  set z : ℂ := jacobiTheta₂ (v / 2) v / 2 - 1 with hz_def
  have hz : ‖z‖ ≤ 3 / 2 * e := by
    have h1 := norm_jacobiTheta₂_half_sub_two_le_exp (τ := v) (by linarith)
    have hzeq : z = (jacobiTheta₂ (v / 2) v - 2) / 2 := by rw [hz_def]; ring
    rw [hzeq, norm_div, Complex.norm_ofNat]
    rw [← he] at h1; linarith
  have herr : powerChargeErr a v = z + (Complex.exp u - 1) + z * (Complex.exp u - 1) := by
    unfold powerChargeErr; rw [← hu, hz_def]; ring
  rw [herr]
  have hE1 : ‖Complex.exp u - 1‖ ≤ 1 := by nlinarith
  calc ‖z + (Complex.exp u - 1) + z * (Complex.exp u - 1)‖
      ≤ ‖z‖ + ‖Complex.exp u - 1‖ + ‖z‖ * ‖Complex.exp u - 1‖ := by
        refine le_trans (norm_add_le _ _) ?_
        rw [norm_mul]; linarith [norm_add_le z (Complex.exp u - 1)]
    _ ≤ ‖z‖ + ‖Complex.exp u - 1‖ + ‖z‖ := by nlinarith [norm_nonneg z, norm_nonneg (Complex.exp u - 1)]
    _ ≤ 3 / 2 * e + 2 * (a / 4 * (3 / 2 * (50 * e))) + 3 / 2 * e := by linarith
    _ ≤ 60 * (1 + a) * e := by nlinarith

end

end RHTower
