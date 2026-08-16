import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The universal degree--time wedge and the prime information cone

Inside the parabolic wedge `t(d+1) ≤ (log 2 / 16)²` the phase-space bound

`|F̂(ξ)|/M ≤ exp(-ξ²/(4t) + 2√d |ξ|/√t)`

is already at most `exp(-ξ²/(8t))` at every arithmetic frequency `ξ = log n ≥ log 2`: the
translated oscillator disk of radius `2√(dt)` never reaches the first prime.  Splitting that
Gaussian in half leaves the uniform factor `exp(-(log 2)²/(16t))` times an absolutely convergent
prime series, so the whole prime modulation is superexponentially small in `1/t`.

The threshold is coefficient-free: it depends on the degree and the time only through the product
`t(d+1)`, which is the exact parabolic scale at which a degree-`d` oscillator can first reach the
first prime frequency.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-! ## The wedge threshold -/

/-- The universal parabolic wedge threshold `(log 2 / 16)²`. -/
def parabolicWedgeThreshold : ℝ := (Real.log 2 / 16) ^ 2

theorem parabolicWedgeThreshold_pos : 0 < parabolicWedgeThreshold := by
  have h : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold parabolicWedgeThreshold
  positivity

/-- **(24.137) inside the wedge.**  At every arithmetic frequency the translated oscillator
exponent is at most half the free Gaussian exponent. -/
theorem parabolicWedge_exponent_le {t d : ℝ} (ht : 0 < t) (hd : 0 ≤ d)
    (hwedge : t * (d + 1) ≤ parabolicWedgeThreshold) {xi : ℝ} (hxi : Real.log 2 ≤ xi) :
    -(xi ^ 2 / (4 * t)) + 2 * Real.sqrt d * (xi / Real.sqrt t) ≤ -(xi ^ 2 / (8 * t)) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hxipos : 0 < xi := lt_of_lt_of_le hlog2 hxi
  have hsqrt_t : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hprod : Real.sqrt d * Real.sqrt t ≤ Real.log 2 / 16 := by
    have hdt : d * t ≤ parabolicWedgeThreshold := by nlinarith
    have hmul : Real.sqrt d * Real.sqrt t = Real.sqrt (d * t) :=
      (Real.sqrt_mul hd t).symm
    rw [hmul]
    have hle : Real.sqrt (d * t) ≤ Real.sqrt parabolicWedgeThreshold :=
      Real.sqrt_le_sqrt hdt
    have hthr : Real.sqrt parabolicWedgeThreshold = Real.log 2 / 16 := by
      unfold parabolicWedgeThreshold
      exact Real.sqrt_sq (by positivity)
    rwa [hthr] at hle
  have hkey : 16 * (Real.sqrt d * Real.sqrt t) ≤ xi := by
    calc 16 * (Real.sqrt d * Real.sqrt t) ≤ 16 * (Real.log 2 / 16) := by linarith
      _ = Real.log 2 := by ring
      _ ≤ xi := hxi
  have hcancel : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  have hmain : 16 * (Real.sqrt d * Real.sqrt t) * xi ≤ xi * xi := by
    nlinarith [hkey, hxipos]
  have hstep : 2 * Real.sqrt d * (xi / Real.sqrt t) ≤ xi ^ 2 / (8 * t) := by
    have hL : 2 * Real.sqrt d * (xi / Real.sqrt t)
        = (2 * Real.sqrt d * xi) / Real.sqrt t := by
      ring
    rw [hL, div_le_div_iff₀ hsqrt_t (by positivity)]
    nlinarith [hmain, hcancel, hsqrt_t, Real.sqrt_nonneg d, hxipos]
  have hsplit : xi ^ 2 / (4 * t) = xi ^ 2 / (8 * t) + xi ^ 2 / (8 * t) := by
    field_simp
    ring
  linarith

/-- **(24.138) the Gaussian split.**  Half of the Gaussian is uniform in the frequency. -/
theorem gaussianSplit_le {t : ℝ} (ht : 0 < t) {xi : ℝ} (hxi : Real.log 2 ≤ xi) :
    Real.exp (-(xi ^ 2 / (8 * t)))
      ≤ Real.exp (-((Real.log 2) ^ 2 / (16 * t))) * Real.exp (-(xi ^ 2 / (16 * t))) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsq : (Real.log 2) ^ 2 ≤ xi ^ 2 := by nlinarith
  have hsplit : xi ^ 2 / (8 * t) = xi ^ 2 / (16 * t) + xi ^ 2 / (16 * t) := by
    field_simp
    ring
  have hmono : (Real.log 2) ^ 2 / (16 * t) ≤ xi ^ 2 / (16 * t) := by
    apply div_le_div_of_nonneg_right hsq
    positivity
  linarith

/-! ## The prime series inside the wedge is absolutely convergent -/

/-- The logarithm is dominated by a quarter power. -/
theorem log_le_four_rpow {x : ℝ} (hx : 0 < x) : Real.log x ≤ 4 * x ^ ((1 : ℝ) / 4) := by
  have h1 : Real.log (x ^ ((1 : ℝ) / 4)) ≤ x ^ ((1 : ℝ) / 4) - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx _)
  rw [Real.log_rpow hx] at h1
  nlinarith [Real.rpow_pos_of_pos hx ((1 : ℝ) / 4)]

/-- Beyond the parabolic radius the Gaussian tail beats an inverse square. -/
theorem exp_gaussian_le_inv_sq {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 32 * t ≤ Real.log n)
    (hn1 : 1 ≤ n) :
    Real.exp (-((Real.log n) ^ 2 / (16 * t))) ≤ ((n : ℝ) ^ (2 : ℝ))⁻¹ := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hlognn : 0 ≤ Real.log n := le_trans (by positivity) hn
  have hstep : 2 * Real.log n ≤ (Real.log n) ^ 2 / (16 * t) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hexp : Real.exp (-((Real.log n) ^ 2 / (16 * t))) ≤ Real.exp (-(2 * Real.log n)) :=
    Real.exp_le_exp.2 (by linarith)
  have hval : Real.exp (-(2 * Real.log n)) = ((n : ℝ) ^ (2 : ℝ))⁻¹ := by
    rw [Real.rpow_def_of_pos hnpos, ← Real.exp_neg]
    congr 1
    ring
  rwa [hval] at hexp

/-- **(24.138)** The prime modulation series inside the wedge converges absolutely. -/
theorem summable_vonMangoldt_gaussianTail {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n) * ((n : ℝ) ^ ((1 : ℝ) / 2))⁻¹
      * Real.exp (-((Real.log n) ^ 2 / (16 * t)))) := by
  have hmaj : Summable (fun n : ℕ => 4 * ((n : ℝ) ^ ((9 : ℝ) / 4))⁻¹) :=
    (Real.summable_nat_rpow_inv.2 (by norm_num)).mul_left 4
  refine Summable.of_norm_bounded_eventually_nat hmaj ?_
  filter_upwards [Filter.eventually_ge_atTop (max 1 (Nat.ceil (Real.exp (32 * t))))]
    with n hn
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hceil : Nat.ceil (Real.exp (32 * t)) ≤ n := le_trans (le_max_right _ _) hn
  have hexpn : Real.exp (32 * t) ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hceil)
  have hlog : 32 * t ≤ Real.log n := by
    have := Real.log_le_log (Real.exp_pos _) hexpn
    rwa [Real.log_exp] at this
  have hlognn : 0 ≤ Real.log n := le_trans (by positivity) hlog
  have hgauss := exp_gaussian_le_inv_sq ht hlog hn1
  have hvm : ArithmeticFunction.vonMangoldt n ≤ Real.log n :=
    ArithmeticFunction.vonMangoldt_le_log
  have hvm0 : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  have hlogle : Real.log n ≤ 4 * (n : ℝ) ^ ((1 : ℝ) / 4) := log_le_four_rpow hnpos
  have hinvpos : (0 : ℝ) < ((n : ℝ) ^ ((1 : ℝ) / 2))⁻¹ := by positivity
  have hgauss0 : (0 : ℝ) ≤ Real.exp (-((Real.log n) ^ 2 / (16 * t))) := (Real.exp_pos _).le
  have hchain : ArithmeticFunction.vonMangoldt n * ((n : ℝ) ^ ((1 : ℝ) / 2))⁻¹
        * Real.exp (-((Real.log n) ^ 2 / (16 * t)))
      ≤ (4 * (n : ℝ) ^ ((1 : ℝ) / 4)) * ((n : ℝ) ^ ((1 : ℝ) / 2))⁻¹ * ((n : ℝ) ^ (2 : ℝ))⁻¹ := by
    have h1 : ArithmeticFunction.vonMangoldt n ≤ 4 * (n : ℝ) ^ ((1 : ℝ) / 4) :=
      le_trans hvm hlogle
    have h2 : ArithmeticFunction.vonMangoldt n * ((n : ℝ) ^ ((1 : ℝ) / 2))⁻¹
        ≤ (4 * (n : ℝ) ^ ((1 : ℝ) / 4)) * ((n : ℝ) ^ ((1 : ℝ) / 2))⁻¹ :=
      mul_le_mul_of_nonneg_right h1 hinvpos.le
    have h3 : (0 : ℝ) ≤ (4 * (n : ℝ) ^ ((1 : ℝ) / 4)) * ((n : ℝ) ^ ((1 : ℝ) / 2))⁻¹ := by
      positivity
    calc ArithmeticFunction.vonMangoldt n * ((n : ℝ) ^ ((1 : ℝ) / 2))⁻¹
          * Real.exp (-((Real.log n) ^ 2 / (16 * t)))
        ≤ (4 * (n : ℝ) ^ ((1 : ℝ) / 4)) * ((n : ℝ) ^ ((1 : ℝ) / 2))⁻¹
          * Real.exp (-((Real.log n) ^ 2 / (16 * t))) :=
          mul_le_mul_of_nonneg_right h2 hgauss0
      _ ≤ (4 * (n : ℝ) ^ ((1 : ℝ) / 4)) * ((n : ℝ) ^ ((1 : ℝ) / 2))⁻¹ * ((n : ℝ) ^ (2 : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_left hgauss h3
  have hpow : (4 * (n : ℝ) ^ ((1 : ℝ) / 4)) * ((n : ℝ) ^ ((1 : ℝ) / 2))⁻¹ * ((n : ℝ) ^ (2 : ℝ))⁻¹
      = 4 * ((n : ℝ) ^ ((9 : ℝ) / 4))⁻¹ := by
    rw [← Real.rpow_neg hnpos.le, ← Real.rpow_neg hnpos.le, ← Real.rpow_neg hnpos.le]
    rw [mul_assoc, mul_assoc, ← Real.rpow_add hnpos, ← Real.rpow_add hnpos]
    norm_num
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [← hpow]
  exact hchain

end

end RHTower
