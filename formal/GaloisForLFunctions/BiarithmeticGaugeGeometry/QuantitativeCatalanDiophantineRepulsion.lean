import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Quantitative Catalan–Diophantine Repulsion of the Liouville Vacuum off the Kronecker Line

Irrationality of `log 3 / log 2` implies qualitatively that no archimedean height twist `γ ∈ ℝ`
can simultaneously flip `cos(γ log 2) = -1` and `cos(γ log 3) = -1`, while Kronecker's density
theorem implies that `inf_{γ ∈ ℝ} ((1 + cos(γ log 2)) + (1 + cos(γ log 3))) = 0` as `|γ| → ∞`.
To control gauge-charged localizers quantitatively, one needs an **explicit all-height Diophantine
lower bound** naming the minimum conductor height `|γ|` required for an archimedean twist to
`ε`-approximate the Liouville vacuum on `{2, 3}`.

This module proves a Baker-free quantitative repulsion theorem directly from the parity gap
`|2^a - 3^b| ≥ 1` (`2 + 1 = 3`, `3 + 1 = 2²`):

1. **Logarithmic gap for distinct positive integers (`abs_log_nat_sub_ge`).**
   For any distinct integers `A, B ≥ 1`, `|log A - log B| ≥ 1 / (A + B)`.

2. **Parity separation of odd linear forms in `log 2` and `log 3`
   (`two_pow_ne_three_pow`, `abs_odd_mul_log_two_sub_odd_mul_log_three_ge`).**
   Since `2^a` is even for `a ≥ 1` and `3^b` is odd for all `b ≥ 0`, every pair of odd integers
   `u, v ∈ ℤ` satisfies
   `|u log 2 - v log 3| ≥ 1 / (2^{|u|} + 3^{|v|})`.

3. **Explicit all-height Kronecker–Liouville repulsion (`liouville_kronecker_repulsion_ge`,
   `abs_height_ge_of_liouville_approx`).**
   Eliminating `γ` between `δ₂ = γ log 2 - u₂ π` and `δ₃ = γ log 3 - u₃ π` (`u₂, u₃` odd) proves
   that for **every** `γ ∈ ℝ`:
   `(1 + cos(γ log 2)) + (1 + cos(γ log 3)) ≥ (1 / 50) * exp(-|γ|)`.
   Consequently, any archimedean twist with `(1 + cos(γ log 2)) + (1 + cos(γ log 3)) ≤ ε`
   (`0 < ε ≤ 1 / 50`) is forced above height `|γ| ≥ log(1 / (50 ε))`.
-/

open Real

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.BiarithmeticGaugeGeometry

/-! ## §1. Elementary logarithmic gap and parity separation of `2^a` and `3^b` -/

/-- Elementary rational lower bound `u / (1 + u) ≤ log(1 + u)` for `u ≥ 0`. -/
theorem div_one_add_le_log_one_add {u : ℝ} (hu : 0 ≤ u) :
    u / (1 + u) ≤ Real.log (1 + u) := by
  have h1u : 0 < 1 + u := by linarith
  set t : ℝ := u / (1 + u)
  have h1t : 1 - t = 1 / (1 + u) := by
    dsimp [t]; field_simp; ring
  have hexp_neg : 1 - t ≤ Real.exp (-t) := by
    have h := Real.add_one_le_exp (-t)
    linarith
  rw [h1t] at hexp_neg
  have hexp_le : Real.exp t ≤ 1 + u := by
    have hmul := mul_le_mul_of_nonneg_right hexp_neg (mul_nonneg h1u.le (Real.exp_pos t).le)
    have hlhs : 1 / (1 + u) * ((1 + u) * Real.exp t) = Real.exp t := by
      field_simp
    have hrhs : Real.exp (-t) * ((1 + u) * Real.exp t) = 1 + u := by
      calc Real.exp (-t) * ((1 + u) * Real.exp t)
          = (1 + u) * (Real.exp (-t) * Real.exp t) := by ring
        _ = (1 + u) * Real.exp (-t + t) := by rw [← Real.exp_add]
        _ = 1 + u := by simp
    linarith
  calc t = Real.log (Real.exp t) := (Real.log_exp t).symm
    _ ≤ Real.log (1 + u) := Real.log_le_log (Real.exp_pos t) hexp_le

/-- Distinct positive integers `A ≠ B` (`A, B ≥ 1`) satisfy `|log A - log B| ≥ 1 / (A + B)`. -/
theorem abs_log_nat_sub_ge {A B : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hne : A ≠ B) :
    1 / ((A : ℝ) + B) ≤ |Real.log A - Real.log B| := by
  have aux : ∀ {X Y : ℕ}, 1 ≤ Y → Y < X →
      1 / ((X : ℝ) + Y) ≤ Real.log X - Real.log Y := by
    intro X Y hY hYX
    have hY_pos : (0 : ℝ) < Y := Nat.cast_pos.mpr (by omega)
    have hX_pos : (0 : ℝ) < X := Nat.cast_pos.mpr (by omega)
    have hYX1 : (Y : ℝ) + 1 ≤ X := by exact_mod_cast hYX
    have hdiv' : 1 + 1 / (Y : ℝ) ≤ (X : ℝ) / Y := by
      rw [le_div_iff₀ hY_pos]
      calc (1 + 1 / (Y : ℝ)) * Y = (Y : ℝ) + 1 := by field_simp
        _ ≤ X := hYX1
    have hlog1 : (1 / (Y : ℝ)) / (1 + 1 / (Y : ℝ)) ≤ Real.log (1 + 1 / (Y : ℝ)) :=
      div_one_add_le_log_one_add (by positivity)
    have hsimp : (1 / (Y : ℝ)) / (1 + 1 / (Y : ℝ)) = 1 / ((Y : ℝ) + 1) := by
      field_simp
    rw [hsimp] at hlog1
    have hlog2 : Real.log (1 + 1 / (Y : ℝ)) ≤ Real.log ((X : ℝ) / Y) :=
      Real.log_le_log (by positivity) hdiv'
    rw [Real.log_div hX_pos.ne' hY_pos.ne'] at hlog2
    have hmono : 1 / ((X : ℝ) + Y) ≤ 1 / ((Y : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  rcases lt_or_gt_of_ne hne with hAB | hBA
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log (by positivity)
      (by exact_mod_cast hAB.le))), add_comm]
    exact aux hA hAB
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log (by positivity)
      (by exact_mod_cast hBA.le)))]
    exact aux hB hBA

/-- Positive powers of `2` are even and powers of `3` are odd, so `2^a ≠ 3^b` for all `a ≥ 1`. -/
theorem two_pow_ne_three_pow {a : ℕ} (ha : 1 ≤ a) (b : ℕ) : 2 ^ a ≠ 3 ^ b := by
  have heven : (2 ^ a) % 2 = 0 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
    rw [pow_succ']
    exact Nat.mul_mod_right 2 (2 ^ k)
  have hodd : (3 ^ b) % 2 = 1 := by
    induction b with
    | zero => rfl
    | succ b ih =>
      rw [pow_succ, Nat.mul_mod, ih]
  intro heq
  rw [heq] at heven
  omega

/-- **Parity-separated logarithmic linear form bound:** for every pair of odd integers `u, v ∈ ℤ`,
`|u log 2 - v log 3| ≥ 1 / (2^{|u|} + 3^{|v|})`. -/
theorem abs_odd_mul_log_two_sub_odd_mul_log_three_ge {u v : ℤ} (hu : Odd u) (hv : Odd v) :
    1 / ((2 : ℝ) ^ u.natAbs + (3 : ℝ) ^ v.natAbs) ≤
      |(u : ℝ) * Real.log 2 - (v : ℝ) * Real.log 3| := by
  have hu0 : u ≠ 0 := by rintro rfl; obtain ⟨k, hk⟩ := hu; omega
  have hv0 : v ≠ 0 := by rintro rfl; obtain ⟨k, hk⟩ := hv; omega
  have hu_pos : 1 ≤ u.natAbs := Int.natAbs_pos.mpr hu0
  have hv_pos : 1 ≤ v.natAbs := Int.natAbs_pos.mpr hv0
  have h2_ge : (2 : ℝ) ≤ (2 : ℝ) ^ u.natAbs := by
    have : 2 ^ 1 ≤ 2 ^ u.natAbs := Nat.pow_le_pow_right (by omega) hu_pos
    exact_mod_cast this
  have h3_ge : (3 : ℝ) ≤ (3 : ℝ) ^ v.natAbs := by
    have : 3 ^ 1 ≤ 3 ^ v.natAbs := Nat.pow_le_pow_right (by omega) hv_pos
    exact_mod_cast this
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have same_sign : ∀ (a b : ℕ), 1 ≤ a → 1 ≤ b →
      1 / ((2 : ℝ) ^ a + (3 : ℝ) ^ b) ≤ |(a : ℝ) * Real.log 2 - (b : ℝ) * Real.log 3| := by
    intro a b ha hb
    have hA1 : 1 ≤ 2 ^ a := Nat.one_le_pow a 2 (by omega)
    have hB1 : 1 ≤ 3 ^ b := Nat.one_le_pow b 3 (by omega)
    have hgap := abs_log_nat_sub_ge hA1 hB1 (two_pow_ne_three_pow ha b)
    simpa [Nat.cast_pow, Real.log_pow] using hgap
  rcases lt_or_gt_of_ne hu0 with hu_neg | hu_gt
  · rcases lt_or_gt_of_ne hv0 with hv_neg | hv_gt
    · have hu_eq : (u : ℝ) = -(u.natAbs : ℝ) := by
        have h : (u.natAbs : ℤ) = -u := Int.ofNat_natAbs_of_nonpos hu_neg.le
        have hR : ((u.natAbs : ℤ) : ℝ) = ((-u : ℤ) : ℝ) := congrArg Int.cast h
        rw [Int.cast_natCast, Int.cast_neg] at hR
        linarith
      have hv_eq : (v : ℝ) = -(v.natAbs : ℝ) := by
        have h' : (v.natAbs : ℤ) = -v := Int.ofNat_natAbs_of_nonpos hv_neg.le
        have hR : ((v.natAbs : ℤ) : ℝ) = ((-v : ℤ) : ℝ) := congrArg Int.cast h'
        rw [Int.cast_natCast, Int.cast_neg] at hR
        linarith
      rw [hu_eq, hv_eq, show -(u.natAbs : ℝ) * Real.log 2 - -(v.natAbs : ℝ) * Real.log 3 =
        -((u.natAbs : ℝ) * Real.log 2 - (v.natAbs : ℝ) * Real.log 3) by ring, abs_neg]
      exact same_sign u.natAbs v.natAbs hu_pos hv_pos
    · have hu_le : (u : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hu_neg
      have hv_ge : (1 : ℝ) ≤ v := by exact_mod_cast hv_gt
      have hval : (u : ℝ) * Real.log 2 - (v : ℝ) * Real.log 3 < 0 := by nlinarith
      rw [abs_of_neg hval]
      have h1 : 1 / ((2 : ℝ) ^ u.natAbs + (3 : ℝ) ^ v.natAbs) ≤ 1 / 5 :=
        one_div_le_one_div_of_le (by norm_num) (by linarith)
      have hl2 := Real.log_two_gt_d9
      nlinarith
  · rcases lt_or_gt_of_ne hv0 with hv_neg | hv_gt
    · have hu_ge : (1 : ℝ) ≤ u := by exact_mod_cast hu_gt
      have hv_le : (v : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hv_neg
      have hval : 0 < (u : ℝ) * Real.log 2 - (v : ℝ) * Real.log 3 := by nlinarith
      rw [abs_of_pos hval]
      have h1 : 1 / ((2 : ℝ) ^ u.natAbs + (3 : ℝ) ^ v.natAbs) ≤ 1 / 5 :=
        one_div_le_one_div_of_le (by norm_num) (by linarith)
      have hl2 := Real.log_two_gt_d9
      nlinarith
    · have hu_eq : (u : ℝ) = (u.natAbs : ℝ) := by
        have h : (u.natAbs : ℤ) = u := Int.natAbs_of_nonneg hu_gt.le
        have hR : ((u.natAbs : ℤ) : ℝ) = (u : ℝ) := congrArg Int.cast h
        simpa using hR.symm
      have hv_eq : (v : ℝ) = (v.natAbs : ℝ) := by
        have h : (v.natAbs : ℤ) = v := Int.natAbs_of_nonneg hv_gt.le
        have hR : ((v.natAbs : ℤ) : ℝ) = (v : ℝ) := congrArg Int.cast h
        simpa using hR.symm
      rw [hu_eq, hv_eq]
      exact same_sign u.natAbs v.natAbs hu_pos hv_pos

/-! ## §2. Quadratic floor on `1 + cos x` around odd multiples of `π` -/

/-- For `0 ≤ y ≤ π / 2`, `y / 2 ≤ sin y` via the cubic Taylor lower bound `y - y³/6 < sin y`. -/
theorem half_mul_le_sin_of_le_pi_div_two {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ Real.pi / 2) :
    y / 2 ≤ Real.sin y := by
  rcases eq_or_lt_of_le hy0 with rfl | hy_pos
  · simp
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hy_ub : y < 1.58 := by linarith
  have hy2 : y ^ 2 < 2.5 := by nlinarith
  have hcube := Real.sin_gt_sub_cube hy_pos
  nlinarith

/-- For `|θ| ≤ π`, `θ² / 8 ≤ 1 - cos θ`. -/
theorem sq_div_eight_le_one_sub_cos {θ : ℝ} (hθ : |θ| ≤ Real.pi) :
    θ ^ 2 / 8 ≤ 1 - Real.cos θ := by
  have hid : 1 - Real.cos θ = 2 * Real.sin (|θ| / 2) ^ 2 := by
    have hc : Real.cos θ = Real.cos |θ| := (Real.cos_abs θ).symm
    rw [hc, show |θ| = 2 * (|θ| / 2) by ring, Real.cos_two_mul, Real.cos_sq']
    ring
  rw [hid]
  have hy0 : 0 ≤ |θ| / 2 := by positivity
  have hy1 : |θ| / 2 ≤ Real.pi / 2 := by linarith
  have hsin := half_mul_le_sin_of_le_pi_div_two hy0 hy1
  have hsq : (|θ| / 4) ^ 2 ≤ Real.sin (|θ| / 2) ^ 2 := by
    have : |θ| / 4 = (|θ| / 2) / 2 := by ring
    rw [this]
    exact pow_le_pow_left₀ (by positivity) hsin 2
  have habs_sq : (|θ| / 4) ^ 2 = θ ^ 2 / 16 := by
    rw [div_pow, sq_abs]; norm_num
  linarith

/-- Every `x ∈ ℝ` admits an odd integer `u` with `|x - u π| ≤ π`, `|u| ≤ |x|/π + 1`, and
`(x - u π)² / 8 ≤ 1 + cos x`. -/
theorem exists_odd_int_one_add_cos_ge (x : ℝ) :
    ∃ u : ℤ, Odd u ∧ (u.natAbs : ℝ) ≤ |x| / Real.pi + 1 ∧
      (x - (u : ℝ) * Real.pi) ^ 2 / 8 ≤ 1 + Real.cos x := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have h2pi : 0 < 2 * Real.pi := by positivity
  set k : ℤ := ⌊x / (2 * Real.pi)⌋
  set u : ℤ := 2 * k + 1
  have hu_odd : Odd u := ⟨k, rfl⟩
  have hk_lo : (k : ℝ) * (2 * Real.pi) ≤ x :=
    (le_div_iff₀ h2pi).mp (Int.floor_le (x / (2 * Real.pi)))
  have hk_hi : x < ((k : ℝ) + 1) * (2 * Real.pi) :=
    (div_lt_iff₀ h2pi).mp (Int.lt_floor_add_one (x / (2 * Real.pi)))
  set δ : ℝ := x - (u : ℝ) * Real.pi
  have hu_cast : (u : ℝ) * Real.pi = 2 * (k : ℝ) * Real.pi + Real.pi := by
    dsimp [u]; push_cast; ring
  have hδ_abs : |δ| ≤ Real.pi := by
    dsimp [δ]; rw [hu_cast, abs_le]
    constructor <;> linarith
  have hu_bound : (u.natAbs : ℝ) ≤ |x| / Real.pi + 1 := by
    have h1 : (u.natAbs : ℝ) * Real.pi ≤ |x| + Real.pi := by
      have hnat : (u.natAbs : ℝ) * Real.pi = |(u : ℝ) * Real.pi| := by
        rw [abs_mul, abs_of_pos hpi]
        congr 1
        rcases le_or_gt 0 u with hu0 | hu0
        · have h : (u.natAbs : ℤ) = u := Int.natAbs_of_nonneg hu0
          have hR : ((u.natAbs : ℤ) : ℝ) = (u : ℝ) := congrArg Int.cast h
          rw [abs_of_nonneg (by exact_mod_cast hu0)]
          simpa using hR
        · have h : (u.natAbs : ℤ) = -u := Int.ofNat_natAbs_of_nonpos hu0.le
          have hR : ((u.natAbs : ℤ) : ℝ) = ((-u : ℤ) : ℝ) := congrArg Int.cast h
          rw [Int.cast_natCast, Int.cast_neg] at hR
          rw [abs_of_neg (by exact_mod_cast hu0)]
          linarith
      rw [hnat, show (u : ℝ) * Real.pi = x - δ by dsimp [δ]; ring]
      exact (abs_sub x δ).trans (add_le_add_right hδ_abs |x|)
    calc (u.natAbs : ℝ) = ((u.natAbs : ℝ) * Real.pi) / Real.pi := by field_simp
      _ ≤ (|x| + Real.pi) / Real.pi := div_le_div_of_nonneg_right h1 hpi.le
      _ = |x| / Real.pi + 1 := by field_simp
  have hcos : 1 + Real.cos x = 1 - Real.cos δ := by
    have hx_eq : x = (δ + Real.pi) + (k : ℝ) * (2 * Real.pi) := by
      dsimp [δ]; rw [hu_cast]; ring
    rw [hx_eq, Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
    ring
  refine ⟨u, hu_odd, hu_bound, ?_⟩
  rw [hcos]
  exact sq_div_eight_le_one_sub_cos hδ_abs

/-! ## §3. All-height quantitative Kronecker–Liouville repulsion and conductor floor -/

/-- Upper bound `log 3 < 6 / 5`. -/
theorem log_three_lt_six_fifths : Real.log 3 < 6 / 5 := by
  have hsplit : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have h32 : Real.log (3 / 2 : ℝ) ≤ 1 / 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
    linarith
  have hl2 := Real.log_two_lt_d9
  linarith

private theorem pow_eq_exp_nat_mul_log {b : ℝ} (hb : 0 < b) (n : ℕ) :
    b ^ n = Real.exp ((n : ℝ) * Real.log b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Nat.cast_succ, add_mul, one_mul, Real.exp_add, Real.exp_log hb]

/-- **Quantitative Catalan–Diophantine Twist-Repulsion Law (`liouville_kronecker_repulsion_ge`).**
For **every** archimedean height `γ ∈ ℝ`, the gauge-charge discrepancy between `kroneckerGauge γ`
and `liouvilleGauge` on `{2, 3}` satisfies
`(1 + cos(γ log 2)) + (1 + cos(γ log 3)) ≥ (1 / 50) * exp(-|γ|)`. -/
theorem liouville_kronecker_repulsion_ge (γ : ℝ) :
    (1 / 50 : ℝ) * Real.exp (-|γ|) ≤
      (1 + Real.cos (γ * Real.log 2)) + (1 + Real.cos (γ * Real.log 3)) := by
  obtain ⟨u₂, hu₂_odd, hu₂_bd, hcos₂⟩ := exists_odd_int_one_add_cos_ge (γ * Real.log 2)
  obtain ⟨u₃, hu₃_odd, hu₃_bd, hcos₃⟩ := exists_odd_int_one_add_cos_ge (γ * Real.log 3)
  set δ₂ : ℝ := γ * Real.log 2 - (u₂ : ℝ) * Real.pi
  set δ₃ : ℝ := γ * Real.log 3 - (u₃ : ℝ) * Real.pi
  have helim : Real.log 3 * δ₂ - Real.log 2 * δ₃ =
      Real.pi * ((u₃ : ℝ) * Real.log 2 - (u₂ : ℝ) * Real.log 3) := by
    dsimp [δ₂, δ₃]; ring
  have hcs : (Real.log 3 * δ₂ - Real.log 2 * δ₃) ^ 2 ≤
      (δ₂ ^ 2 + δ₃ ^ 2) * (Real.log 3 ^ 2 + Real.log 2 ^ 2) := by
    nlinarith [sq_nonneg (Real.log 2 * δ₂ + Real.log 3 * δ₃)]
  have hl2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hl2_ub : Real.log 2 < 7 / 10 := by linarith [Real.log_two_lt_d9]
  have hl3_ub : Real.log 3 < 6 / 5 := log_three_lt_six_fifths
  have hlogs_sq : Real.log 3 ^ 2 + Real.log 2 ^ 2 ≤ 2 := by nlinarith
  have hpi_gt : 3 < Real.pi := Real.pi_gt_three
  have hlin_gap := abs_odd_mul_log_two_sub_odd_mul_log_three_ge hu₃_odd hu₂_odd
  set D : ℝ := (2 : ℝ) ^ u₃.natAbs + (3 : ℝ) ^ u₂.natAbs
  have hD_pos : 0 < D := by dsimp [D]; positivity
  have hsq_gap : (Real.pi / D) ^ 2 ≤ (Real.log 3 * δ₂ - Real.log 2 * δ₃) ^ 2 := by
    rw [helim, mul_pow, div_pow]
    have h1 : (1 / D) ^ 2 ≤ ((u₃ : ℝ) * Real.log 2 - (u₂ : ℝ) * Real.log 3) ^ 2 := by
      rw [← sq_abs ((u₃ : ℝ) * Real.log 2 - (u₂ : ℝ) * Real.log 3)]
      exact pow_le_pow_left₀ (by positivity) hlin_gap 2
    have hrew : Real.pi ^ 2 / D ^ 2 = Real.pi ^ 2 * (1 / D) ^ 2 := by ring
    rw [hrew]
    exact mul_le_mul_of_nonneg_left h1 (sq_nonneg Real.pi)
  -- Bound `D ≤ 5 * exp(|γ| / 2)`
  have hprod_logs : Real.log 3 * Real.log 2 / Real.pi ≤ 1 / 2 := by
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith
  have h2_pow : (2 : ℝ) ^ u₃.natAbs ≤ 2 * Real.exp (|γ| / 2) := by
    have hrew : (2 : ℝ) ^ u₃.natAbs = Real.exp ((u₃.natAbs : ℝ) * Real.log 2) :=
      pow_eq_exp_nat_mul_log (by norm_num) u₃.natAbs
    have habs3 : |γ * Real.log 3| = |γ| * Real.log 3 := by
      rw [abs_mul, abs_of_pos hl3_pos]
    have hexp_le : (u₃.natAbs : ℝ) * Real.log 2 ≤ Real.log 2 + |γ| / 2 := by
      have h1 := mul_le_mul_of_nonneg_right hu₃_bd hl2_pos.le
      rw [habs3, add_mul, one_mul, div_mul_eq_mul_div, mul_assoc] at h1
      have h2 : |γ| * (Real.log 3 * Real.log 2) / Real.pi =
          |γ| * (Real.log 3 * Real.log 2 / Real.pi) := by ring
      rw [h2] at h1
      have h3 : |γ| * (Real.log 3 * Real.log 2 / Real.pi) ≤ |γ| * (1 / 2) :=
        mul_le_mul_of_nonneg_left ‹Real.log 3 * Real.log 2 / Real.pi ≤ 1 / 2› (abs_nonneg γ)
      linarith
    calc (2 : ℝ) ^ u₃.natAbs
        = Real.exp ((u₃.natAbs : ℝ) * Real.log 2) := hrew
      _ ≤ Real.exp (Real.log 2 + |γ| / 2) := Real.exp_le_exp.mpr hexp_le
      _ = 2 * Real.exp (|γ| / 2) := by rw [Real.exp_add, Real.exp_log (by norm_num)]
  have h3_pow : (3 : ℝ) ^ u₂.natAbs ≤ 3 * Real.exp (|γ| / 2) := by
    have hrew : (3 : ℝ) ^ u₂.natAbs = Real.exp ((u₂.natAbs : ℝ) * Real.log 3) :=
      pow_eq_exp_nat_mul_log (by norm_num) u₂.natAbs
    have habs2 : |γ * Real.log 2| = |γ| * Real.log 2 := by
      rw [abs_mul, abs_of_pos hl2_pos]
    have hexp_le : (u₂.natAbs : ℝ) * Real.log 3 ≤ Real.log 3 + |γ| / 2 := by
      have h1 := mul_le_mul_of_nonneg_right hu₂_bd hl3_pos.le
      rw [habs2, add_mul, one_mul, div_mul_eq_mul_div, mul_assoc] at h1
      have h2 : |γ| * (Real.log 2 * Real.log 3) / Real.pi =
          |γ| * (Real.log 3 * Real.log 2 / Real.pi) := by ring
      rw [h2] at h1
      have h3 : |γ| * (Real.log 3 * Real.log 2 / Real.pi) ≤ |γ| * (1 / 2) :=
        mul_le_mul_of_nonneg_left ‹Real.log 3 * Real.log 2 / Real.pi ≤ 1 / 2› (abs_nonneg γ)
      linarith
    calc (3 : ℝ) ^ u₂.natAbs
        = Real.exp ((u₂.natAbs : ℝ) * Real.log 3) := hrew
      _ ≤ Real.exp (Real.log 3 + |γ| / 2) := Real.exp_le_exp.mpr hexp_le
      _ = 3 * Real.exp (|γ| / 2) := by rw [Real.exp_add, Real.exp_log (by norm_num)]
  have hD_le : D ≤ 5 * Real.exp (|γ| / 2) := by dsimp [D]; linarith
  have hD_sq : D ^ 2 ≤ 25 * Real.exp |γ| := by
    calc D ^ 2 ≤ (5 * Real.exp (|γ| / 2)) ^ 2 := pow_le_pow_left₀ hD_pos.le hD_le 2
      _ = 25 * (Real.exp (|γ| / 2) * Real.exp (|γ| / 2)) := by ring
      _ = 25 * Real.exp |γ| := by rw [← Real.exp_add]; congr 2; ring
  have hpi_sq : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith
  have hdelta_lb : (9 / 50 : ℝ) * Real.exp (-|γ|) ≤ δ₂ ^ 2 + δ₃ ^ 2 := by
    have h1 : 9 / (25 * Real.exp |γ|) ≤ (Real.pi / D) ^ 2 := by
      rw [div_pow]
      calc 9 / (25 * Real.exp |γ|) ≤ Real.pi ^ 2 / (25 * Real.exp |γ|) :=
            div_le_div_of_nonneg_right hpi_sq (by positivity)
        _ ≤ Real.pi ^ 2 / D ^ 2 :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hD_sq
    have h2 : (Real.pi / D) ^ 2 ≤ 2 * (δ₂ ^ 2 + δ₃ ^ 2) := by
      calc (Real.pi / D) ^ 2 ≤ (Real.log 3 * δ₂ - Real.log 2 * δ₃) ^ 2 := hsq_gap
        _ ≤ (δ₂ ^ 2 + δ₃ ^ 2) * (Real.log 3 ^ 2 + Real.log 2 ^ 2) := hcs
        _ ≤ (δ₂ ^ 2 + δ₃ ^ 2) * 2 :=
            mul_le_mul_of_nonneg_left hlogs_sq (add_nonneg (sq_nonneg δ₂) (sq_nonneg δ₃))
        _ = 2 * (δ₂ ^ 2 + δ₃ ^ 2) := by ring
    have hrew : (9 / 50 : ℝ) * Real.exp (-|γ|) = (9 / (25 * Real.exp |γ|)) / 2 := by
      rw [Real.exp_neg]; field_simp; ring
    linarith
  have hsum_cos : (δ₂ ^ 2 + δ₃ ^ 2) / 8 ≤
      (1 + Real.cos (γ * Real.log 2)) + (1 + Real.cos (γ * Real.log 3)) := by
    dsimp [δ₂, δ₃] at hcos₂ hcos₃ ⊢
    linarith
  linarith [Real.exp_pos (-|γ|)]

/-- **Explicit Conductor Height Floor (`abs_height_ge_of_liouville_approx`).**
Any archimedean height `γ ∈ ℝ` whose prime phases on `{2, 3}` approximate the Liouville vacuum
within `(1 + cos(γ log 2)) + (1 + cos(γ log 3)) ≤ ε` (`0 < ε`) must satisfy
`|γ| ≥ log(1 / (50 ε))`. -/
theorem abs_height_ge_of_liouville_approx {γ ε : ℝ} (hε : 0 < ε)
    (happrox : (1 + Real.cos (γ * Real.log 2)) + (1 + Real.cos (γ * Real.log 3)) ≤ ε) :
    Real.log (1 / (50 * ε)) ≤ |γ| := by
  have hrep := liouville_kronecker_repulsion_ge γ
  have h1 : (1 / 50 : ℝ) * Real.exp (-|γ|) ≤ ε := hrep.trans happrox
  have h2 : 1 / (50 * ε) ≤ Real.exp |γ| := by
    rw [Real.exp_neg] at h1
    rw [div_le_iff₀ (by positivity)]
    have hmul := mul_le_mul_of_nonneg_right h1 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 50)
      (Real.exp_pos |γ|).le)
    calc (1 : ℝ) = (1 / 50 : ℝ) * (Real.exp |γ|)⁻¹ * (50 * Real.exp |γ|) := by
          field_simp
      _ ≤ ε * (50 * Real.exp |γ|) := hmul
      _ = Real.exp |γ| * (50 * ε) := by ring
  calc Real.log (1 / (50 * ε)) ≤ Real.log (Real.exp |γ|) :=
        Real.log_le_log (by positivity) h2
    _ = |γ| := Real.log_exp |γ|

end GaloisForLFunctions.BiarithmeticGaugeGeometry
