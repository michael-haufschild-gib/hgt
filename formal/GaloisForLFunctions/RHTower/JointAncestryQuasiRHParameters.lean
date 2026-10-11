import GaloisForLFunctions.RHTower.JointAncestryQuasiRHCore

/-!
# Parameters of the quasi-RH amplification

The amplification at a target of height `γ` uses the prime window `(n, n²]` with
`n = ⌊γ^{75/θ}⌋`, the scale range `[τ_min, τ_max]`, `τ_max = (n+1)^θ`, the suppression threshold
`L₀` and the height cut `T₀ = e^Q`.  This file defines these as functions of `x = n` and proves that
all numerical conditions of `re_tsum_jasLogWeightValue_neg` hold for every large `x`
(`eventually_jqr_conditions`).  Every condition compares a polylogarithm with a positive power of
`x`: the window mass is `≍ log x`, `τ_min ≍ x^{41θ/75}` up to constants, the Perron error carries
`x^{σ₁ − 1 + ε}` against `Q² ≲ x^{2θ+4ε} log² x`, and `θ, ε ≤ (1−σ₁)/20` makes the exponents
negative.
-/

open Filter Real
open scoped Topology

namespace RHTower

noncomputable section

/-! ## Polylogarithms against powers -/

/-- `K (1 + log x)^k ≤ x^s` eventually, for `s > 0`. -/
theorem eventually_mul_one_add_log_pow_le (k : ℕ) {s : ℝ} (hs : 0 < s) (K : ℝ) :
    ∀ᶠ x : ℝ in atTop, K * (1 + Real.log x) ^ k ≤ x ^ s := by
  have hK : 0 < |K| * 2 ^ k + 1 := by positivity
  have ho := (isLittleO_log_rpow_rpow_atTop (k : ℝ) hs).bound (c := 1 / (|K| * 2 ^ k + 1))
    (by positivity)
  filter_upwards [ho, tendsto_log_atTop.eventually_ge_atTop 1, eventually_gt_atTop 0]
    with x hx hlog hx0
  have hlog0 : 0 ≤ Real.log x := by linarith
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog0 _), Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _),
    Real.rpow_natCast] at hx
  have h1 : (1 + Real.log x) ^ k ≤ 2 ^ k * Real.log x ^ k := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (by linarith) k
  have hxs : 0 ≤ x ^ s := Real.rpow_nonneg hx0.le s
  calc K * (1 + Real.log x) ^ k ≤ |K| * (1 + Real.log x) ^ k :=
        mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
    _ ≤ |K| * (2 ^ k * Real.log x ^ k) := mul_le_mul_of_nonneg_left h1 (abs_nonneg K)
    _ = (|K| * 2 ^ k) * Real.log x ^ k := by ring
    _ ≤ (|K| * 2 ^ k + 1) * Real.log x ^ k := by
        have := pow_nonneg hlog0 k; nlinarith
    _ ≤ (|K| * 2 ^ k + 1) * (1 / (|K| * 2 ^ k + 1) * x ^ s) :=
        mul_le_mul_of_nonneg_left hx hK.le
    _ = x ^ s := by field_simp

/-- `exp(a log y) = y^a` for `y > 0`. -/
theorem exp_mul_log_eq_rpow {y : ℝ} (hy : 0 < y) (a : ℝ) : Real.exp (a * Real.log y) = y ^ a := by
  rw [Real.rpow_def_of_pos hy, mul_comm]

/-- `(x + 1)^a ≤ 2^a x^a` for `x ≥ 1`, `a ≥ 0`. -/
theorem add_one_rpow_le {x a : ℝ} (hx : 1 ≤ x) (ha : 0 ≤ a) : (x + 1) ^ a ≤ 2 ^ a * x ^ a := by
  rw [← Real.mul_rpow (by norm_num) (by linarith)]
  exact Real.rpow_le_rpow (by linarith) (by linarith) ha

/-- `(x + 1)^a ≤ x^a` for `x > 0`, `a ≤ 0`. -/
theorem add_one_rpow_le_of_nonpos {x a : ℝ} (hx : 0 < x) (ha : a ≤ 0) : (x + 1) ^ a ≤ x ^ a :=
  Real.rpow_le_rpow_of_nonpos hx (by linarith) ha

/-! ## The parameter functions -/

/-- The height bound `Γ(x) = (x+1)^{θ/75}`. -/
def jqrHeight (θ x : ℝ) : ℝ := (x + 1) ^ (θ / 75)

/-- The largest scale `τ_max = (x+1)^θ`. -/
def jqrScaleMax (θ x : ℝ) : ℝ := (x + 1) ^ θ

/-- The scale unit lower bound `τ_min = τ_max e^{−34(C + log(Γ + 4))}`. -/
def jqrScaleMin (θ C x : ℝ) : ℝ :=
  jqrScaleMax θ x * Real.exp (-(34 * (C + Real.log (jqrHeight θ x + 4))))

/-- Lower and upper Mertens bounds for the window mass. -/
def jqrMassLo (CM x : ℝ) : ℝ := Real.log x - 2 * CM

def jqrMassHi (CM x : ℝ) : ℝ := 2 * Real.log x + CM

/-- The suppression threshold. -/
def jqrThreshold (θ W x : ℝ) : ℝ := 2 * (28 + Real.log (8 * W * (jqrHeight θ x + 2) ^ 2 + 1))

/-- The far-zero amplification exponent. -/
def jqrFarExponent (θ ε CM x : ℝ) : ℝ :=
  jqrScaleMax θ x * (Real.exp (2 * ε * Real.log x) * jqrMassHi CM x + jqrMassHi CM x) + 1

/-- The logarithm of the height cut. -/
def jqrCut (θ ε CM C x : ℝ) : ℝ :=
  2 * (jqrFarExponent θ ε CM x +
    Real.log (640 * Real.exp 1 * (C + 3) * (jqrHeight θ x + 2) ^ 2))

/-! ## Basic growth -/

theorem one_le_jqrHeight {θ x : ℝ} (hθ : 0 ≤ θ) (hx : 0 ≤ x) : 1 ≤ jqrHeight θ x :=
  Real.one_le_rpow (by linarith) (by positivity)

theorem jqrScaleMin_ge {θ C x : ℝ} (hθ : 0 ≤ θ) (hx : 0 ≤ x) :
    Real.exp (-(34 * C)) * 5 ^ (-(34 : ℝ)) * (x + 1) ^ (θ - 34 * θ / 75) ≤ jqrScaleMin θ C x := by
  have hΓ := one_le_jqrHeight hθ hx
  have hx1 : 0 < x + 1 := by linarith
  have hmin : jqrScaleMin θ C x =
      (x + 1) ^ θ * Real.exp (-(34 * C)) * (jqrHeight θ x + 4) ^ (-(34 : ℝ)) := by
    unfold jqrScaleMin jqrScaleMax
    rw [show -(34 * (C + Real.log (jqrHeight θ x + 4))) =
        -(34 * C) + (-(34 : ℝ)) * Real.log (jqrHeight θ x + 4) by ring, Real.exp_add,
      exp_mul_log_eq_rpow (by linarith)]
    ring
  have h1 : (5 * jqrHeight θ x) ^ (-(34 : ℝ)) ≤ (jqrHeight θ x + 4) ^ (-(34 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num)
  have h2 : (5 * jqrHeight θ x) ^ (-(34 : ℝ)) = 5 ^ (-(34 : ℝ)) * (x + 1) ^ (-(34 * θ / 75)) := by
    rw [Real.mul_rpow (by norm_num) (by linarith), jqrHeight, ← Real.rpow_mul hx1.le]
    congr 2; ring
  have h3 : (x + 1) ^ (θ - 34 * θ / 75) = (x + 1) ^ θ * (x + 1) ^ (-(34 * θ / 75)) := by
    rw [← Real.rpow_add hx1]; congr 1
  rw [hmin, h3]
  rw [h2] at h1
  have hp : 0 ≤ (x + 1) ^ θ := Real.rpow_nonneg hx1.le _
  have hE := Real.exp_pos (-(34 * C))
  calc Real.exp (-(34 * C)) * 5 ^ (-(34 : ℝ)) * ((x + 1) ^ θ * (x + 1) ^ (-(34 * θ / 75)))
      = (x + 1) ^ θ * Real.exp (-(34 * C)) * (5 ^ (-(34 : ℝ)) * (x + 1) ^ (-(34 * θ / 75))) := by
        ring
    _ ≤ (x + 1) ^ θ * Real.exp (-(34 * C)) * (jqrHeight θ x + 4) ^ (-(34 : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)

/-! ## The eventual conditions -/

theorem eventually_jqrMassLo_ge (CM b : ℝ) : ∀ᶠ x : ℝ in atTop, b ≤ jqrMassLo CM x := by
  filter_upwards [tendsto_log_atTop.eventually_ge_atTop (b + 2 * CM)] with x hx
  unfold jqrMassLo; linarith

/-- `jqrMassHi ≤ (2 + CM)(1 + log x)` for `log x ≥ 0`. -/
theorem jqrMassHi_le {CM x : ℝ} (hCM : 0 ≤ CM) (hx : 0 ≤ Real.log x) :
    jqrMassHi CM x ≤ (2 + CM) * (1 + Real.log x) := by
  unfold jqrMassHi; nlinarith

theorem eventually_trivial_mass {CM : ℝ} (hCM : 0 ≤ CM) :
    ∀ᶠ x : ℝ in atTop, Real.exp (-(1 / 8) * Real.log (x + 1)) * jqrMassHi CM x ≤ 99 := by
  filter_upwards [eventually_mul_one_add_log_pow_le 1 (s := 1 / 8) (by norm_num) (2 + CM),
    eventually_ge_atTop 1] with x hx hx1
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  rw [exp_mul_log_eq_rpow (by linarith)]
  have h1 := add_one_rpow_le_of_nonpos (x := x) (a := -(1 / 8)) (by linarith) (by norm_num)
  have h2 := jqrMassHi_le hCM hlog
  rw [pow_one] at hx
  have h3 : x ^ (-(1 / 8) : ℝ) * x ^ (1 / 8 : ℝ) = 1 := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  have hp : 0 ≤ (x + 1) ^ (-(1 / 8) : ℝ) := Real.rpow_nonneg (by linarith) _
  have hq : 0 ≤ x ^ (-(1 / 8) : ℝ) := Real.rpow_nonneg (by linarith) _
  calc (x + 1) ^ (-(1 / 8) : ℝ) * jqrMassHi CM x ≤ x ^ (-(1 / 8) : ℝ) * ((2 + CM) * (1 + Real.log x)) :=
        mul_le_mul h1 h2 (by unfold jqrMassHi; positivity) hq
    _ ≤ x ^ (-(1 / 8) : ℝ) * x ^ (1 / 8 : ℝ) := mul_le_mul_of_nonneg_left hx hq
    _ ≤ 99 := by rw [h3]; norm_num

/-- A power with negative exponent beats a polylogarithm: `K (1+log x)^k x^{−s} ≤ c`. -/
theorem eventually_mul_log_pow_mul_rpow_neg_le (k : ℕ) {s c : ℝ} (hs : 0 < s) (hc : 0 < c) (K : ℝ) :
    ∀ᶠ x : ℝ in atTop, K * (1 + Real.log x) ^ k * x ^ (-s) ≤ c := by
  filter_upwards [eventually_mul_one_add_log_pow_le k hs (K / c), eventually_gt_atTop 0] with x hx hx0
  have hxs : 0 < x ^ s := Real.rpow_pos_of_pos hx0 s
  rw [Real.rpow_neg hx0.le, ← div_eq_mul_inv, div_le_iff₀ hxs]
  rw [div_mul_eq_mul_div, div_le_iff₀ hc] at hx
  linarith

theorem eventually_dev {θ ε : ℝ} (hθε : θ + ε ≤ 1 / 2) :
    ∀ᶠ x : ℝ in atTop,
      2 * (x + 1) ^ θ * (2 * Real.log x) * Real.exp ((ε - 1) * Real.log (x + 1)) ≤ 1 / 2 := by
  filter_upwards [eventually_mul_log_pow_mul_rpow_neg_le 1 (s := 1 / 2) (c := 1 / 2) (by norm_num)
    (by norm_num) 4, eventually_ge_atTop 1] with x hx hx1
  have hx0 : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  rw [exp_mul_log_eq_rpow (by linarith)]
  have hc : (x + 1) ^ θ * (x + 1) ^ (ε - 1) = (x + 1) ^ (θ + ε - 1) := by
    rw [← Real.rpow_add (by linarith)]; ring_nf
  have h1 : (x + 1) ^ (θ + ε - 1) ≤ x ^ (-(1 / 2) : ℝ) :=
    (add_one_rpow_le_of_nonpos hx0 (by linarith)).trans
      (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))
  rw [pow_one] at hx
  calc 2 * (x + 1) ^ θ * (2 * Real.log x) * (x + 1) ^ (ε - 1)
      = 4 * Real.log x * ((x + 1) ^ θ * (x + 1) ^ (ε - 1)) := by ring
    _ = 4 * Real.log x * (x + 1) ^ (θ + ε - 1) := by rw [hc]
    _ ≤ 4 * (1 + Real.log x) * x ^ (-(1 / 2) : ℝ) := by
        refine mul_le_mul (by linarith) h1 (Real.rpow_nonneg (by linarith) _) (by linarith)
    _ ≤ 1 / 2 := hx

theorem eventually_remainder {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1 / 20) :
    ∀ᶠ x : ℝ in atTop, 16 * ((x + 1) ^ θ) ^ 2 * (2 * Real.log x) ^ 2 / Real.sqrt x ≤ 1 / 100 := by
  filter_upwards [eventually_mul_log_pow_mul_rpow_neg_le 2 (s := 2 / 5) (c := 1 / 100) (by norm_num)
    (by norm_num) 128, eventually_ge_atTop 1] with x hx hx1
  have hx0 : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hsq : Real.sqrt x = x ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow x
  have h1 : ((x + 1) ^ θ) ^ 2 ≤ 2 * x ^ (1 / 10 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    calc (x + 1) ^ (θ * ((2 : ℕ) : ℝ)) ≤ 2 ^ (θ * ((2 : ℕ) : ℝ)) * x ^ (θ * ((2 : ℕ) : ℝ)) :=
          add_one_rpow_le hx1 (by positivity)
      _ ≤ 2 * x ^ (1 / 10 : ℝ) := by
          push_cast
          refine mul_le_mul ?_ (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))
            (Real.rpow_nonneg hx0.le _) (by norm_num)
          calc (2 : ℝ) ^ (θ * 2) ≤ 2 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            _ = 2 := Real.rpow_one 2
  have hpow : x ^ (1 / 10 : ℝ) / x ^ (1 / 2 : ℝ) = x ^ (-(2 / 5) : ℝ) := by
    rw [← Real.rpow_sub hx0]; norm_num
  have hL : (2 * Real.log x) ^ 2 ≤ 4 * (1 + Real.log x) ^ 2 := by nlinarith
  rw [hsq]
  have hxh : 0 < x ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx0 _
  calc 16 * ((x + 1) ^ θ) ^ 2 * (2 * Real.log x) ^ 2 / x ^ (1 / 2 : ℝ)
      ≤ 16 * (2 * x ^ (1 / 10 : ℝ)) * (4 * (1 + Real.log x) ^ 2) / x ^ (1 / 2 : ℝ) := by
        gcongr
    _ = 128 * (1 + Real.log x) ^ 2 * (x ^ (1 / 10 : ℝ) / x ^ (1 / 2 : ℝ)) := by ring
    _ = 128 * (1 + Real.log x) ^ 2 * x ^ (-(2 / 5) : ℝ) := by rw [hpow]
    _ ≤ 1 / 100 := hx

theorem eventually_mirror_small {θ δ CM : ℝ} (hδ : 0 < δ) (hθδ : θ ≤ δ / 16)
    (hCM : 0 ≤ CM) :
    ∀ᶠ x : ℝ in atTop,
      (x + 1) ^ θ * (Real.exp (-(δ / 2) * Real.log (x + 1)) * jqrMassHi CM x) ≤ 1 / 100 := by
  filter_upwards [eventually_mul_log_pow_mul_rpow_neg_le 1 (s := δ / 4) (c := 1 / 100) (by positivity)
    (by norm_num) (2 + CM), eventually_ge_atTop 1] with x hx hx1
  have hx0 : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  rw [exp_mul_log_eq_rpow (by linarith)]
  have hc : (x + 1) ^ θ * (x + 1) ^ (-(δ / 2)) = (x + 1) ^ (θ - δ / 2) := by
    rw [← Real.rpow_add (by linarith)]; ring_nf
  have h1 : (x + 1) ^ (θ - δ / 2) ≤ x ^ (-(δ / 4)) :=
    (add_one_rpow_le_of_nonpos hx0 (by linarith)).trans
      (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))
  rw [pow_one] at hx
  have h2 := jqrMassHi_le hCM hlog
  calc (x + 1) ^ θ * ((x + 1) ^ (-(δ / 2)) * jqrMassHi CM x)
      = (x + 1) ^ (θ - δ / 2) * jqrMassHi CM x := by rw [← hc]; ring
    _ ≤ x ^ (-(δ / 4)) * ((2 + CM) * (1 + Real.log x)) :=
        mul_le_mul h1 h2 (by unfold jqrMassHi; positivity) (Real.rpow_nonneg hx0.le _)
    _ = (2 + CM) * (1 + Real.log x) * x ^ (-(δ / 4)) := by ring
    _ ≤ 1 / 100 := hx

theorem eventually_admissible {θ : ℝ} (hθ : 0 < θ) :
    ∀ᶠ x : ℝ in atTop,
      (x + 1) ^ θ * (2 * Real.log x) * Real.exp (-(2 * θ) * Real.log (x + 1)) ≤ 1 / 2 := by
  filter_upwards [eventually_mul_log_pow_mul_rpow_neg_le 1 (s := θ) (c := 1 / 2) hθ
    (by norm_num) 2, eventually_ge_atTop 1] with x hx hx1
  have hx0 : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  rw [exp_mul_log_eq_rpow (by linarith)]
  have hc : (x + 1) ^ θ * (x + 1) ^ (-(2 * θ)) = (x + 1) ^ (-θ) := by
    rw [← Real.rpow_add (by linarith)]; ring_nf
  have h1 : (x + 1) ^ (-θ) ≤ x ^ (-θ) := add_one_rpow_le_of_nonpos hx0 (by linarith)
  rw [pow_one] at hx
  calc (x + 1) ^ θ * (2 * Real.log x) * (x + 1) ^ (-(2 * θ))
      = 2 * Real.log x * ((x + 1) ^ θ * (x + 1) ^ (-(2 * θ))) := by ring
    _ = 2 * Real.log x * (x + 1) ^ (-θ) := by rw [hc]
    _ ≤ 2 * (1 + Real.log x) * x ^ (-θ) :=
        mul_le_mul (by linarith) h1 (Real.rpow_nonneg (by linarith) _) (by linarith)
    _ ≤ 1 / 2 := hx

theorem eventually_exp_neg_le_half {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, Real.exp (-δ * Real.log (x + 1)) ≤ 1 / 2 := by
  filter_upwards [(tendsto_rpow_atTop hδ).eventually_ge_atTop 2, eventually_ge_atTop 1] with x hx hx1
  rw [exp_mul_log_eq_rpow (by linarith), Real.rpow_neg (by linarith)]
  have h := Real.rpow_le_rpow (by linarith) (show x ≤ x + 1 by linarith) hδ.le
  rw [inv_le_comm₀ (Real.rpow_pos_of_pos (by linarith) δ) (by norm_num)]
  linarith

theorem eventually_le_rpow (b : ℝ) {s : ℝ} (hs : 0 < s) : ∀ᶠ x : ℝ in atTop, b ≤ x ^ s :=
  (tendsto_rpow_atTop hs).eventually_ge_atTop b

/-- The suppression threshold is logarithmic. -/
theorem jqrThreshold_le {θ W x : ℝ} (hθ : 0 ≤ θ) (hθ75 : θ ≤ 75 / 2) (hW : 0 ≤ W) (hx : 1 ≤ x) :
    jqrThreshold θ W x ≤ (58 + 2 * Real.log (144 * W + 1)) * (1 + Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hΓ := one_le_jqrHeight hθ hx0.le
  have hΓsq : (jqrHeight θ x + 2) ^ 2 ≤ 18 * x := by
    have h1 : (jqrHeight θ x + 2) ^ 2 ≤ 9 * jqrHeight θ x ^ 2 := by nlinarith
    have h2 : jqrHeight θ x ^ 2 ≤ x + 1 := by
      rw [jqrHeight, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      calc (x + 1) ^ (θ / 75 * ((2 : ℕ) : ℝ)) ≤ (x + 1) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; linarith)
        _ = x + 1 := Real.rpow_one _
    nlinarith
  have hlog : Real.log (8 * W * (jqrHeight θ x + 2) ^ 2 + 1) ≤
      Real.log (144 * W + 1) + Real.log x := by
    rw [← Real.log_mul (by positivity) hx0.ne']
    refine Real.log_le_log (by positivity) ?_
    nlinarith [mul_le_mul_of_nonneg_left hΓsq (show (0 : ℝ) ≤ 8 * W by positivity)]
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hl1 : 0 ≤ Real.log (144 * W + 1) := Real.log_nonneg (by linarith)
  unfold jqrThreshold
  nlinarith

theorem eventually_scale_conditions {θ C CM W : ℝ} (hθ : 0 < θ) (hθ75 : θ ≤ 75 / 2) (hW : 0 ≤ W) :
    ∀ᶠ x : ℝ in atTop, 32 * Real.pi ≤ jqrScaleMin θ C x * jqrMassLo CM x ∧
      4 * jqrThreshold θ W x ≤ jqrScaleMin θ C x * jqrMassLo CM x ∧
      (230 + 4 * Real.pi * jqrThreshold θ W x) / (jqrScaleMin θ C x * jqrMassLo CM x) ≤
        Real.pi / 8 := by
  set c₁ : ℝ := Real.exp (-(34 * C)) * 5 ^ (-(34 : ℝ)) with hc₁
  have hc₁0 : 0 < c₁ := mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (by norm_num) _)
  set s : ℝ := θ - 34 * θ / 75 with hs
  have hs0 : 0 < s := by rw [hs]; linarith
  set K₂ : ℝ := 58 + 2 * Real.log (144 * W + 1) with hK₂
  have hK₂0 : 0 ≤ K₂ := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 144 * W + 1 by linarith); rw [hK₂]; linarith
  filter_upwards [eventually_jqrMassLo_ge CM 1, eventually_le_rpow (32 * Real.pi / c₁) hs0,
    eventually_mul_one_add_log_pow_le 1 hs0 (4 * K₂ / c₁),
    eventually_mul_one_add_log_pow_le 1 hs0 ((230 + 4 * Real.pi * K₂) / (Real.pi / 8 * c₁)),
    eventually_ge_atTop 1] with x hM h1 h2 h3 hx1
  have hx0 : 0 < x := by linarith
  rw [pow_one] at h2 h3
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hmin : c₁ * x ^ s ≤ jqrScaleMin θ C x := by
    refine le_trans ?_ (jqrScaleMin_ge hθ.le hx0.le)
    rw [← hc₁, ← hs]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx0.le (by linarith) hs0.le) hc₁0.le
  have hxs : 0 < x ^ s := Real.rpow_pos_of_pos hx0 s
  have hprod : c₁ * x ^ s ≤ jqrScaleMin θ C x * jqrMassLo CM x := by
    have hmin0 : 0 ≤ jqrScaleMin θ C x := le_trans (by positivity) hmin
    nlinarith
  have hthr := jqrThreshold_le hθ.le hθ75 hW hx1
  rw [← hK₂] at hthr
  have hcx : 0 < c₁ * x ^ s := mul_pos hc₁0 hxs
  refine ⟨?_, ?_, ?_⟩
  · have : 32 * Real.pi ≤ c₁ * x ^ s := by
      rw [div_le_iff₀ hc₁0] at h1; linarith
    linarith
  · have : 4 * K₂ * (1 + Real.log x) ≤ c₁ * x ^ s := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hc₁0] at h2; linarith
    nlinarith
  · rw [div_le_iff₀ (lt_of_lt_of_le hcx hprod)]
    have : (230 + 4 * Real.pi * K₂) * (1 + Real.log x) ≤ Real.pi / 8 * (c₁ * x ^ s) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at h3; linarith
    have hthr' : 4 * Real.pi * jqrThreshold θ W x ≤ 4 * Real.pi * (K₂ * (1 + Real.log x)) :=
      mul_le_mul_of_nonneg_left hthr (by positivity)
    have : 230 ≤ 230 * (1 + Real.log x) := by nlinarith
    nlinarith [Real.pi_pos]

/-- The height cut exceeds the window and the height. -/
theorem eventually_cut_large {θ ε CM C : ℝ} (hθ : 0 ≤ θ) (hθ75 : θ ≤ 75) (hCM : 0 ≤ CM)
    (hC : 0 ≤ C) :
    ∀ᶠ x : ℝ in atTop, 2 * (x ^ 2 + jqrHeight θ x + 10) ≤ Real.exp (jqrCut θ ε CM C x) := by
  filter_upwards [eventually_ge_atTop 3] with x hx3
  have hx0 : 0 < x := by linarith
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hΓ := one_le_jqrHeight hθ hx0.le
  have hΓx : jqrHeight θ x ≤ x + 1 := by
    rw [jqrHeight]
    calc (x + 1) ^ (θ / 75) ≤ (x + 1) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = x + 1 := Real.rpow_one _
  have hlogt : 0 ≤ Real.log (640 * Real.exp 1 * (C + 3) * (jqrHeight θ x + 2) ^ 2) := by
    refine Real.log_nonneg ?_
    have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have h3 : (1 : ℝ) ≤ 640 * Real.exp 1 * (C + 3) := by nlinarith
    have h4 : (1 : ℝ) ≤ (jqrHeight θ x + 2) ^ 2 := by nlinarith
    exact one_le_mul_of_one_le_of_one_le h3 h4
  have hfar : 2 * Real.log x ≤ jqrFarExponent θ ε CM x := by
    unfold jqrFarExponent jqrMassHi jqrScaleMax
    have h1 : (1 : ℝ) ≤ (x + 1) ^ θ := Real.one_le_rpow (by linarith) hθ
    have h2 : 0 ≤ Real.exp (2 * ε * Real.log x) * (2 * Real.log x + CM) :=
      mul_nonneg (Real.exp_pos _).le (by positivity)
    nlinarith
  have hcut : 4 * Real.log x ≤ jqrCut θ ε CM C x := by unfold jqrCut; linarith
  have hx4 : Real.exp (4 * Real.log x) = x ^ 4 := by
    rw [show 4 * Real.log x = Real.log (x ^ 4) by rw [Real.log_pow]; norm_num,
      Real.exp_log (by positivity)]
  have hx9 : 9 ≤ x ^ 2 := by nlinarith
  have hx44 : 9 * x ^ 2 ≤ x ^ 4 := by nlinarith
  calc 2 * (x ^ 2 + jqrHeight θ x + 10) ≤ x ^ 4 := by nlinarith
    _ = Real.exp (4 * Real.log x) := hx4.symm
    _ ≤ Real.exp (jqrCut θ ε CM C x) := Real.exp_le_exp.mpr hcut

theorem two_pow_le_two {θ : ℝ} (hθ1 : θ ≤ 1) : (2 : ℝ) ^ θ ≤ 2 :=
  (Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ1).trans_eq (Real.rpow_one 2)

/-- The far exponent is `O(x^{θ+2ε} log x)`. -/
theorem jqrFarExponent_le {θ ε CM x : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hε : 0 ≤ ε) (hCM : 0 ≤ CM)
    (hx1 : 1 ≤ x) :
    jqrFarExponent θ ε CM x ≤ (4 * (2 + CM) + 1) * x ^ (θ + 2 * ε) * (1 + Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hpθ : (x + 1) ^ θ ≤ 2 * x ^ θ :=
    (add_one_rpow_le hx1 hθ).trans (mul_le_mul_of_nonneg_right (two_pow_le_two hθ1)
      (Real.rpow_nonneg hx0.le _))
  have hx2 : Real.exp (2 * ε * Real.log x) = x ^ (2 * ε) := exp_mul_log_eq_rpow hx0 _
  have hx21 : 1 ≤ x ^ (2 * ε) := Real.one_le_rpow hx1 (by linarith)
  have hxθ1 : 1 ≤ x ^ θ := Real.one_le_rpow hx1 hθ
  have hsplit : x ^ (θ + 2 * ε) = x ^ θ * x ^ (2 * ε) := Real.rpow_add hx0 _ _
  have hM := jqrMassHi_le hCM hl0
  have hM0 : 0 ≤ jqrMassHi CM x := by unfold jqrMassHi; positivity
  have h2 : x ^ (2 * ε) * jqrMassHi CM x + jqrMassHi CM x ≤
      2 * x ^ (2 * ε) * ((2 + CM) * (1 + Real.log x)) := by nlinarith
  have h1 : (x + 1) ^ θ * (x ^ (2 * ε) * jqrMassHi CM x + jqrMassHi CM x) ≤
      2 * x ^ θ * (2 * x ^ (2 * ε) * ((2 + CM) * (1 + Real.log x))) :=
    mul_le_mul hpθ h2 (by positivity) (by positivity)
  have h4 : 1 ≤ x ^ (θ + 2 * ε) * (1 + Real.log x) := by
    rw [hsplit]
    have h5 : 1 ≤ x ^ θ * x ^ (2 * ε) := one_le_mul_of_one_le_of_one_le hxθ1 hx21
    exact one_le_mul_of_one_le_of_one_le h5 (by linarith)
  unfold jqrFarExponent jqrScaleMax
  rw [hx2]
  calc (x + 1) ^ θ * (x ^ (2 * ε) * jqrMassHi CM x + jqrMassHi CM x) + 1
      ≤ 2 * x ^ θ * (2 * x ^ (2 * ε) * ((2 + CM) * (1 + Real.log x))) +
          x ^ (θ + 2 * ε) * (1 + Real.log x) := add_le_add h1 h4
    _ = (4 * (2 + CM) + 1) * x ^ (θ + 2 * ε) * (1 + Real.log x) := by rw [hsplit]; ring

/-- The logarithmic part of the cut. -/
theorem log_jqrCut_term_le {θ C x : ℝ} (hθ : 0 ≤ θ) (hθ75 : θ ≤ 75 / 2) (hC : 0 ≤ C) (hx1 : 1 ≤ x) :
    Real.log (640 * Real.exp 1 * (C + 3) * (jqrHeight θ x + 2) ^ 2) ≤
      (Real.log (11520 * Real.exp 1 * (C + 3)) + 1) * (1 + Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hΓ := one_le_jqrHeight hθ hx0.le
  have hΓsq : (jqrHeight θ x + 2) ^ 2 ≤ 18 * x := by
    have h1 : (jqrHeight θ x + 2) ^ 2 ≤ 9 * jqrHeight θ x ^ 2 := by nlinarith
    have h2 : jqrHeight θ x ^ 2 ≤ x + 1 := by
      rw [jqrHeight, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      calc (x + 1) ^ (θ / 75 * ((2 : ℕ) : ℝ)) ≤ (x + 1) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; linarith)
        _ = x + 1 := Real.rpow_one _
    nlinarith
  have hE : 0 < Real.exp 1 := Real.exp_pos 1
  have hc1 : 1 ≤ 11520 * Real.exp 1 * (C + 3) := by
    have := Real.one_le_exp (show (0 : ℝ) ≤ 1 by norm_num); nlinarith
  have h1 : Real.log (640 * Real.exp 1 * (C + 3) * (jqrHeight θ x + 2) ^ 2) ≤
      Real.log (11520 * Real.exp 1 * (C + 3) * x) := by
    refine Real.log_le_log (by positivity) ?_
    have := mul_le_mul_of_nonneg_left hΓsq (show (0 : ℝ) ≤ 640 * Real.exp 1 * (C + 3) by positivity)
    nlinarith
  rw [Real.log_mul (by positivity) hx0.ne'] at h1
  have hlc := Real.log_nonneg hc1
  nlinarith

/-- The cut, `+2`, is `O(x^{θ+2ε} log x)`. -/
theorem jqrCut_add_two_le {θ ε CM C x : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hε : 0 ≤ ε)
    (hCM : 0 ≤ CM) (hC : 0 ≤ C) (hx1 : 1 ≤ x) :
    jqrCut θ ε CM C x + 2 ≤
      (2 * (4 * (2 + CM) + 1) + 2 * (Real.log (11520 * Real.exp 1 * (C + 3)) + 1) + 2) *
        x ^ (θ + 2 * ε) * (1 + Real.log x) := by
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hP1 : 1 ≤ x ^ (θ + 2 * ε) := Real.one_le_rpow hx1 (by linarith)
  have h1 := jqrFarExponent_le hθ hθ1 hε hCM hx1
  have h2 := log_jqrCut_term_le hθ (by linarith) hC hx1
  have hK5 : 1 ≤ Real.log (11520 * Real.exp 1 * (C + 3)) + 1 := by
    have : (1 : ℝ) ≤ 11520 * Real.exp 1 * (C + 3) := by
      have := Real.one_le_exp (show (0 : ℝ) ≤ 1 by norm_num); nlinarith
    linarith [Real.log_nonneg this]
  have h3 : (1 + Real.log x) ≤ x ^ (θ + 2 * ε) * (1 + Real.log x) := by nlinarith
  have h4 : (1 : ℝ) ≤ x ^ (θ + 2 * ε) * (1 + Real.log x) := by nlinarith
  unfold jqrCut
  nlinarith

theorem jqrCut_add_two_nonneg {θ ε CM C x : ℝ} (hθ : 0 ≤ θ) (hCM : 0 ≤ CM) (hC : 0 ≤ C)
    (hx1 : 1 ≤ x) : 0 ≤ jqrCut θ ε CM C x + 2 := by
  have hx0 : 0 < x := by linarith
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hΓ := one_le_jqrHeight hθ hx0.le
  have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have h3 : (1 : ℝ) ≤ 640 * Real.exp 1 * (C + 3) := by nlinarith
  have h4 : (1 : ℝ) ≤ (jqrHeight θ x + 2) ^ 2 := by nlinarith
  have hlog := Real.log_nonneg (one_le_mul_of_one_le_of_one_le h3 h4)
  have hM0 : 0 ≤ jqrMassHi CM x := by unfold jqrMassHi; positivity
  have : 0 ≤ jqrFarExponent θ ε CM x := by unfold jqrFarExponent jqrScaleMax; positivity
  unfold jqrCut
  linarith

/-- **The Perron error at the cut height is small.** -/
theorem eventually_perron_small {θ ε CM C K σ₁ : ℝ} (hθ : 0 ≤ θ) (hε : 0 ≤ ε) (hσ₁0 : 0 ≤ σ₁)
    (hσ₁ : σ₁ < 1) (hθσ : θ ≤ (1 - σ₁) / 20) (hεσ : ε ≤ (1 - σ₁) / 20) (hCM : 0 ≤ CM)
    (hC : 0 ≤ C) (hK : 0 ≤ K) :
    ∀ᶠ x : ℝ in atTop,
      2 * K * (x + 1 / 2) ^ (σ₁ - 1 + ε) * (jqrCut θ ε CM C x + 2) ^ 2 ≤ 1 := by
  have hθ1 : θ ≤ 1 := by linarith
  have hs0 : 0 < 1 - σ₁ - ε - 2 * θ - 4 * ε := by linarith
  filter_upwards [eventually_mul_log_pow_mul_rpow_neg_le 2 hs0 (c := 1) (by norm_num)
    (2 * K * (2 * (4 * (2 + CM) + 1) + 2 * (Real.log (11520 * Real.exp 1 * (C + 3)) + 1) + 2) ^ 2),
    eventually_ge_atTop 1] with x hx hx1
  have hx0 : 0 < x := by linarith
  have hcut := jqrCut_add_two_le hθ hθ1 hε hCM hC hx1
  have hcut0 := jqrCut_add_two_nonneg (ε := ε) hθ hCM hC hx1
  have hpow : (x + 1 / 2) ^ (σ₁ - 1 + ε) ≤ x ^ (σ₁ - 1 + ε) :=
    Real.rpow_le_rpow_of_nonpos hx0 (by linarith) (by linarith)
  have hexp : x ^ (σ₁ - 1 + ε) * (x ^ (θ + 2 * ε)) ^ 2 =
      x ^ (-(1 - σ₁ - ε - 2 * θ - 4 * ε)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
    congr 1; push_cast; ring
  calc 2 * K * (x + 1 / 2) ^ (σ₁ - 1 + ε) * (jqrCut θ ε CM C x + 2) ^ 2
      ≤ 2 * K * x ^ (σ₁ - 1 + ε) *
          ((2 * (4 * (2 + CM) + 1) + 2 * (Real.log (11520 * Real.exp 1 * (C + 3)) + 1) + 2) *
            x ^ (θ + 2 * ε) * (1 + Real.log x)) ^ 2 := by
        gcongr
    _ = 2 * K * (2 * (4 * (2 + CM) + 1) + 2 * (Real.log (11520 * Real.exp 1 * (C + 3)) + 1) + 2) ^ 2 *
          (1 + Real.log x) ^ 2 * (x ^ (σ₁ - 1 + ε) * (x ^ (θ + 2 * ε)) ^ 2) := by ring
    _ = _ := by rw [hexp]
    _ ≤ 1 := hx

end

end RHTower
