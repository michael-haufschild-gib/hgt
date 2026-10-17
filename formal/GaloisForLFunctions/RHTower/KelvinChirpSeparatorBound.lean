import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Bounded Kelvin-chirp separators die at a finite support ratio

For a continuous `1`-periodic `F` put `H(v) = e^{v/2} F(e^v) + e^{−v/2} F(e^{−v})` (the Kelvin
symmetrization in log coordinates).  If `H` is positive definite on `[−L, L]` — in particular if
`|H(v)| ≤ H(0)` for `|v| ≤ L` — and `F ≢ 0`, then (`exp_le_of_posDefOn`)

`e^L ≤ 4 + 2√2`.

Proof: `H(0) = 2F(1) ≤ 2‖F‖_∞`.  The interval `[e^L − 1, e^L]` contains a point `t ≡ x*` (mod 1)
where `|F(x*)| = ‖F‖_∞`; at `v = log t`, `|H(v)| ≥ (√t − 1/√t)‖F‖_∞ ≥ (√y − 1/√y)‖F‖_∞` with
`y = e^L − 1`.  So `√y − 1/√y ≤ 2`, i.e. `√y ≤ 1 + √2` and `e^L ≤ 1 + (1 + √2)² = 4 + 2√2`.
Hence beyond the support ratio `4 + 2√2` every separator built from a bounded periodic profile is
singular.
-/

open Real Set

namespace RHTower.KelvinSeparator

noncomputable section

/-- The Kelvin symmetrization `H(v) = e^{v/2} F(e^v) + e^{−v/2} F(e^{−v})`. -/
def kelvinSym (F : ℝ → ℝ) (v : ℝ) : ℝ :=
  Real.exp (v / 2) * F (Real.exp v) + Real.exp (-v / 2) * F (Real.exp (-v))

theorem kelvinSym_neg (F : ℝ → ℝ) (v : ℝ) : kelvinSym F (-v) = kelvinSym F v := by
  unfold kelvinSym
  rw [neg_neg]
  ring

theorem kelvinSym_zero (F : ℝ → ℝ) : kelvinSym F 0 = 2 * F 1 := by
  simp [kelvinSym]
  ring

/-- Positive definiteness of a real even kernel on `[−L, L]`. -/
def PosDefOn (H : ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ (n : ℕ) (c x : Fin n → ℝ), (∀ i, |x i| ≤ L / 2) →
    0 ≤ ∑ i, ∑ j, c i * c j * H (x i - x j)

/-- A positive-definite even kernel is dominated by its value at `0`. -/
theorem abs_le_of_posDefOn {H : ℝ → ℝ} {L : ℝ} (hH : PosDefOn H L) (heven : ∀ v, H (-v) = H v)
    {v : ℝ} (hv : |v| ≤ L) : |H v| ≤ H 0 := by
  have hx : ∀ i : Fin 2, |(![v / 2, -(v / 2)] : Fin 2 → ℝ) i| ≤ L / 2 := by
    intro i
    fin_cases i <;> simp [abs_div, abs_neg] <;> linarith [abs_nonneg v]
  have key : ∀ a b : ℝ, 0 ≤ (a ^ 2 + b ^ 2) * H 0 + 2 * a * b * H v := by
    intro a b
    have := hH 2 ![a, b] ![v / 2, -(v / 2)] hx
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      sub_self, show v / 2 - -(v / 2) = v by ring, show -(v / 2) - v / 2 = -v by ring,
      heven] at this
    nlinarith [this]
  have h1 := key 1 (-1)
  have h2 := key 1 1
  rw [abs_le]
  constructor <;> nlinarith

/-- **Bounded separators die beyond the ratio `4 + 2√2`.** -/
theorem exp_le_of_abs_le {F : ℝ → ℝ} (hF : Continuous F) (hper : Function.Periodic F 1)
    (hne : ∃ x, F x ≠ 0) {L : ℝ}
    (hdom : ∀ v, |v| ≤ L → |kelvinSym F v| ≤ kelvinSym F 0) :
    Real.exp L ≤ 4 + 2 * Real.sqrt 2 := by
  -- the maximum of `|F|` over a period bounds `|F|` everywhere
  obtain ⟨xs, -, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr zero_le_one)
    ((continuous_abs.comp hF).continuousOn (s := Icc (0 : ℝ) 1))
  have hbound : ∀ x, |F x| ≤ |F xs| := by
    intro x
    have h1 : F x = F (Int.fract x) := by
      have := (hper.int_mul ⌊x⌋) (Int.fract x)
      rw [mul_one, Int.fract_add_floor] at this
      exact this
    rw [h1]
    exact hmax ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  obtain ⟨x₀, hx₀⟩ := hne
  have hM : 0 < |F xs| := lt_of_lt_of_le (abs_pos.mpr hx₀) (hbound x₀)
  have hH0 : kelvinSym F 0 ≤ 2 * |F xs| := by
    rw [kelvinSym_zero]; linarith [le_abs_self (F 1), hbound 1]
  by_contra hcon
  push Not at hcon
  have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  -- a point `t ≡ xs (mod 1)` in `[e^L − 1, e^L)`
  set y := Real.exp L - 1 with hy
  have hy1 : 3 + 2 * Real.sqrt 2 < y := by rw [hy]; linarith
  set m : ℤ := ⌈y - xs⌉ with hm
  set t : ℝ := (m : ℝ) + xs with htdef
  have hty : y ≤ t := by have := Int.le_ceil (y - xs); rw [htdef]; linarith
  have htL : t < Real.exp L := by
    have := Int.ceil_lt_add_one (y - xs); rw [htdef]; rw [hy] at this; linarith
  have ht1 : 1 < t := by linarith
  have ht0 : 0 < t := by linarith
  have hFt : F t = F xs := by
    have := (hper.int_mul m) xs
    rw [mul_one] at this
    rw [htdef, add_comm]
    exact this
  -- evaluate `H` at `v = log t`
  set v := Real.log t with hv
  have hv0 : 0 < v := Real.log_pos ht1
  have hvL : v < L := by rw [hv, Real.log_lt_iff_lt_exp ht0]; exact htL
  have hexpv : Real.exp v = t := Real.exp_log ht0
  set a := Real.exp (v / 2) with ha
  have ha0 : 0 < a := Real.exp_pos _
  have ha2 : a ^ 2 = t := by
    rw [ha, ← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (v / 2) = v by push_cast; ring, hexpv]
  have hainv : Real.exp (-v / 2) = a⁻¹ := by
    rw [ha, ← Real.exp_neg, neg_div]
  have hexpnv : Real.exp (-v) = t⁻¹ := by rw [Real.exp_neg, hexpv]
  have hHv : kelvinSym F v = a * F t + a⁻¹ * F t⁻¹ := by
    rw [kelvinSym, hexpv, hexpnv, hainv]
  have hlow : a * |F xs| - a⁻¹ * |F xs| ≤ |kelvinSym F v| := by
    rw [hHv, hFt]
    have h1 := abs_sub_abs_le_abs_sub (a * F t) (-(a⁻¹ * F t⁻¹))
    rw [sub_neg_eq_add, abs_neg, abs_mul, abs_mul, abs_of_pos ha0,
      abs_of_pos (inv_pos.mpr ha0), hFt] at h1
    have h2 : a⁻¹ * |F t⁻¹| ≤ a⁻¹ * |F xs| :=
      mul_le_mul_of_nonneg_left (hbound _) (inv_pos.mpr ha0).le
    linarith
  have hup := hdom v (by rw [abs_of_pos hv0]; exact hvL.le)
  -- `a − 1/a ≤ 2`, hence `a ≤ 1 + √2` and `t = a² ≤ 3 + 2√2`
  have hdiv : a - a⁻¹ ≤ 2 := by
    have : (a - a⁻¹) * |F xs| ≤ 2 * |F xs| := by nlinarith
    exact le_of_mul_le_mul_right this hM
  have hquad : a ^ 2 - 2 * a - 1 ≤ 0 := by
    have : a * (a - a⁻¹) ≤ a * 2 := mul_le_mul_of_nonneg_left hdiv ha0.le
    rw [mul_sub, mul_inv_cancel₀ ha0.ne'] at this
    nlinarith
  have ha_le : a ≤ 1 + Real.sqrt 2 := by
    by_contra h
    push Not at h
    nlinarith [mul_pos (sub_pos.mpr h) (show 0 < a - 1 + Real.sqrt 2 by linarith)]
  have ht_le : t ≤ 3 + 2 * Real.sqrt 2 := by
    rw [← ha2]
    nlinarith [mul_le_mul ha_le ha_le ha0.le (by linarith)]
  linarith

/-- **Positive-definite form**: a bounded periodic profile whose Kelvin symmetrization is positive
definite on `[−L, L]` forces `e^L ≤ 4 + 2√2`. -/
theorem exp_le_of_posDefOn {F : ℝ → ℝ} (hF : Continuous F) (hper : Function.Periodic F 1)
    (hne : ∃ x, F x ≠ 0) {L : ℝ} (hpd : PosDefOn (kelvinSym F) L) :
    Real.exp L ≤ 4 + 2 * Real.sqrt 2 :=
  exp_le_of_abs_le hF hper hne fun _ hv => abs_le_of_posDefOn hpd (kelvinSym_neg F) hv

end

end RHTower.KelvinSeparator
