import GaloisForLFunctions.RHTower.STCPoissonThermalChirality
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Calculus of the thermal Poisson symbol

The Fourier symbol of `h(s) = sech²(s/2)` is `m(ξ) = 4πξ / sinh(πξ)`, `m(0) = 4`.  Here:

* `m` is positive, even, strictly decreasing in `|ξ|`, with maximum `4` at `0`;
* `m' (ξ) = 4π (sinh t - t cosh t) / sinh² t` (`t = πξ`), `m'(0) = 0`; `m'` is odd and has sign
  `-sgn ξ`, so `sgn m' = sgn(-1/ξ)`, and the joint symbol `(m, m')` is injective;
* with `F(t) = 4π / (t sinh(π/t))`, `G(t) = m'(-1/t)`, `F(0) = G(0) = 0`: `m(ξ) = F(-1/ξ)`,
  `m'(ξ) = G(-1/ξ)`; `F` is even with values in `[0, 4]`, `G` is odd with `sgn G(t) = sgn t`;
* at the top edge of the band, `4 - m(ξ) = (2π²/3) ξ² + O(ξ⁴)`, `m'(ξ) = -(4π²/3) ξ + O(ξ³)`,
  `(-1/ξ) m'(ξ) → 4π²/3` and `√(4 - m(ξ)) / |ξ| → π √(2/3)`.
-/

open Real Set Filter Topology Asymptotics

namespace RHTower

noncomputable section
set_option autoImplicit false

/-! ### Taylor bounds for `sinh` and `cosh` -/

theorem abs_sinh_sub_cubic_le {t : ℝ} (ht : |t| ≤ 1) :
    |Real.sinh t - (t + t ^ 3 / 6)| ≤ |t| ^ 5 := by
  have hs := Real.hasSum_sinh t
  have h1 := Real.hasSum_sinh 1
  have hsplit := hs.summable.sum_add_tsum_nat_add 2
  rw [hs.tsum_eq] at hsplit
  have hfirst : ∑ i ∈ Finset.range 2, t ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ) = t + t ^ 3 / 6 := by
    simp [Finset.sum_range_succ, Nat.factorial]
    norm_num
  rw [hfirst] at hsplit
  have htail : Real.sinh t - (t + t ^ 3 / 6) =
      ∑' n : ℕ, t ^ (2 * (n + 2) + 1) / ((2 * (n + 2) + 1).factorial : ℝ) := by
    linarith
  rw [htail]
  have hsum1 : Summable fun n : ℕ => (1 : ℝ) ^ (2 * (n + 2) + 1) / ((2 * (n + 2) + 1).factorial : ℝ) :=
    (summable_nat_add_iff 2).mpr h1.summable
  have hbound : ∀ n : ℕ, ‖t ^ (2 * (n + 2) + 1) / ((2 * (n + 2) + 1).factorial : ℝ)‖ ≤
      |t| ^ 5 * ((1 : ℝ) ^ (2 * (n + 2) + 1) / ((2 * (n + 2) + 1).factorial : ℝ)) := by
    intro n
    rw [Real.norm_eq_abs, abs_div, abs_pow, one_pow, Nat.abs_cast, mul_one_div]
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    calc |t| ^ (2 * (n + 2) + 1) = |t| ^ 5 * |t| ^ (2 * n) := by rw [← pow_add]; ring_nf
      _ ≤ |t| ^ 5 * 1 := by
          gcongr; exact pow_le_one₀ (abs_nonneg t) ht
      _ = |t| ^ 5 := mul_one _
  have htailsum : ∑' n : ℕ, (1 : ℝ) ^ (2 * (n + 2) + 1) / ((2 * (n + 2) + 1).factorial : ℝ) ≤ 1 := by
    have hsplit1 := h1.summable.sum_add_tsum_nat_add 2
    rw [h1.tsum_eq] at hsplit1
    have hf1 : ∑ i ∈ Finset.range 2, (1 : ℝ) ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ) = 7 / 6 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    rw [hf1] at hsplit1
    have hsinh1 : Real.sinh 1 < 3 / 2 := by
      rw [Real.sinh_eq]
      have h := Real.exp_pos (-1)
      have h3 := Real.exp_one_lt_three
      linarith
    linarith
  calc ‖∑' n : ℕ, t ^ (2 * (n + 2) + 1) / ((2 * (n + 2) + 1).factorial : ℝ)‖
      ≤ ∑' n : ℕ, |t| ^ 5 * ((1 : ℝ) ^ (2 * (n + 2) + 1) / ((2 * (n + 2) + 1).factorial : ℝ)) :=
        tsum_of_norm_bounded (hsum1.mul_left _).hasSum hbound
    _ = |t| ^ 5 * ∑' n : ℕ, (1 : ℝ) ^ (2 * (n + 2) + 1) / ((2 * (n + 2) + 1).factorial : ℝ) :=
        tsum_mul_left
    _ ≤ |t| ^ 5 * 1 := by gcongr
    _ = |t| ^ 5 := mul_one _

theorem abs_cosh_sub_quadratic_le {t : ℝ} (ht : |t| ≤ 1) :
    |Real.cosh t - (1 + t ^ 2 / 2)| ≤ |t| ^ 4 := by
  have hs := Real.hasSum_cosh t
  have h1 := Real.hasSum_cosh 1
  have hsplit := hs.summable.sum_add_tsum_nat_add 2
  rw [hs.tsum_eq] at hsplit
  have hfirst : ∑ i ∈ Finset.range 2, t ^ (2 * i) / ((2 * i).factorial : ℝ) = 1 + t ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hfirst] at hsplit
  have htail : Real.cosh t - (1 + t ^ 2 / 2) =
      ∑' n : ℕ, t ^ (2 * (n + 2)) / ((2 * (n + 2)).factorial : ℝ) := by
    linarith
  rw [htail]
  have hsum1 : Summable fun n : ℕ => (1 : ℝ) ^ (2 * (n + 2)) / ((2 * (n + 2)).factorial : ℝ) :=
    (summable_nat_add_iff 2).mpr h1.summable
  have hbound : ∀ n : ℕ, ‖t ^ (2 * (n + 2)) / ((2 * (n + 2)).factorial : ℝ)‖ ≤
      |t| ^ 4 * ((1 : ℝ) ^ (2 * (n + 2)) / ((2 * (n + 2)).factorial : ℝ)) := by
    intro n
    rw [Real.norm_eq_abs, abs_div, abs_pow, one_pow, Nat.abs_cast, mul_one_div]
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    calc |t| ^ (2 * (n + 2)) = |t| ^ 4 * |t| ^ (2 * n) := by rw [← pow_add]; ring_nf
      _ ≤ |t| ^ 4 * 1 := by
          gcongr; exact pow_le_one₀ (abs_nonneg t) ht
      _ = |t| ^ 4 := mul_one _
  have htailsum : ∑' n : ℕ, (1 : ℝ) ^ (2 * (n + 2)) / ((2 * (n + 2)).factorial : ℝ) ≤ 1 := by
    have hsplit1 := h1.summable.sum_add_tsum_nat_add 2
    rw [h1.tsum_eq] at hsplit1
    have hf1 : ∑ i ∈ Finset.range 2, (1 : ℝ) ^ (2 * i) / ((2 * i).factorial : ℝ) = 3 / 2 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    rw [hf1] at hsplit1
    have hcosh1 : Real.cosh 1 < 2 := by
      rw [Real.cosh_eq]
      have h := Real.exp_lt_one_iff.mpr (show (-1 : ℝ) < 0 by norm_num)
      have h3 := Real.exp_one_lt_three
      linarith
    linarith
  calc ‖∑' n : ℕ, t ^ (2 * (n + 2)) / ((2 * (n + 2)).factorial : ℝ)‖
      ≤ ∑' n : ℕ, |t| ^ 4 * ((1 : ℝ) ^ (2 * (n + 2)) / ((2 * (n + 2)).factorial : ℝ)) :=
        tsum_of_norm_bounded (hsum1.mul_left _).hasSum hbound
    _ = |t| ^ 4 * ∑' n : ℕ, (1 : ℝ) ^ (2 * (n + 2)) / ((2 * (n + 2)).factorial : ℝ) :=
        tsum_mul_left
    _ ≤ |t| ^ 4 * 1 := by gcongr
    _ = |t| ^ 4 := mul_one _

theorem abs_le_abs_sinh (t : ℝ) : |t| ≤ |Real.sinh t| := by
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg (Real.sinh_nonneg_iff.mpr h)]
    exact Real.self_le_sinh_iff.mpr h
  · rw [abs_of_nonpos h, abs_of_nonpos (Real.sinh_nonpos_iff.mpr h)]
    have := Real.self_le_sinh_iff.mpr (neg_nonneg.mpr h)
    rw [Real.sinh_neg] at this
    linarith

/-! ### The symbol -/

/-- The thermal symbol `m(ξ) = 4πξ / sinh(πξ)`, `m(0) = 4`. -/
def thermalSymbol (ξ : ℝ) : ℝ := if ξ = 0 then 4 else 4 * (π * ξ / Real.sinh (π * ξ))

theorem thermalSymbol_eq_stcPoissonThermalSymbol : thermalSymbol = stcPoissonThermalSymbol := rfl

theorem thermalSymbol_of_ne {ξ : ℝ} (hξ : ξ ≠ 0) :
    thermalSymbol ξ = 4 * (π * ξ / Real.sinh (π * ξ)) := if_neg hξ

theorem thermalSymbol_zero : thermalSymbol 0 = 4 := if_pos rfl

theorem thermalSymbol_even (ξ : ℝ) : thermalSymbol (-ξ) = thermalSymbol ξ := by
  rw [thermalSymbol_eq_stcPoissonThermalSymbol]; exact stcPoissonThermalSymbol_even ξ

theorem thermalSymbol_strictAntiOn_pos : StrictAntiOn thermalSymbol (Ioi 0) := by
  rw [thermalSymbol_eq_stcPoissonThermalSymbol]; exact stcPoissonThermalSymbol_strictAntiOn_pos

theorem pi_mul_ne_zero {ξ : ℝ} (hξ : ξ ≠ 0) : π * ξ ≠ 0 := mul_ne_zero pi_ne_zero hξ

theorem sinh_pi_mul_ne_zero {ξ : ℝ} (hξ : ξ ≠ 0) : Real.sinh (π * ξ) ≠ 0 :=
  Real.sinh_ne_zero.mpr (pi_mul_ne_zero hξ)

theorem thermalSymbol_pos (ξ : ℝ) : 0 < thermalSymbol ξ := by
  by_cases hξ : ξ = 0
  · rw [hξ, thermalSymbol_zero]; norm_num
  · rw [thermalSymbol_of_ne hξ]
    have h := abs_le_abs_sinh (π * ξ)
    have h0 : 0 < π * ξ / Real.sinh (π * ξ) := by
      rcases lt_or_gt_of_ne (pi_mul_ne_zero hξ) with h1 | h1
      · exact div_pos_of_neg_of_neg h1 (Real.sinh_neg_iff.mpr h1)
      · exact div_pos h1 (Real.sinh_pos_iff.mpr h1)
    positivity

theorem thermalSymbol_lt_four {ξ : ℝ} (hξ : ξ ≠ 0) : thermalSymbol ξ < 4 := by
  rw [thermalSymbol_of_ne hξ]
  have h := abs_le_abs_sinh (π * ξ)
  have hne := pi_mul_ne_zero hξ
  have hlt : |π * ξ| < |Real.sinh (π * ξ)| := by
    rcases lt_or_gt_of_ne hne with h1 | h1
    · rw [abs_of_neg h1, abs_of_neg (Real.sinh_neg_iff.mpr h1)]
      have := Real.self_lt_sinh_iff.mpr (neg_pos.mpr h1)
      rw [Real.sinh_neg] at this; linarith
    · rw [abs_of_pos h1, abs_of_pos (Real.sinh_pos_iff.mpr h1)]
      exact Real.self_lt_sinh_iff.mpr h1
  have hq : π * ξ / Real.sinh (π * ξ) < 1 := by
    have hpos : 0 < π * ξ / Real.sinh (π * ξ) := by
      have := thermalSymbol_pos ξ
      rw [thermalSymbol_of_ne hξ] at this; linarith
    rw [← abs_of_pos hpos, abs_div, div_lt_one (by positivity)]
    exact hlt
  linarith

theorem thermalSymbol_abs (ξ : ℝ) : thermalSymbol |ξ| = thermalSymbol ξ := by
  rcases le_total 0 ξ with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, thermalSymbol_even]

/-- `m` is strictly decreasing in `|ξ|`. -/
theorem thermalSymbol_lt_of_abs_lt {ξ η : ℝ} (h : |ξ| < |η|) : thermalSymbol η < thermalSymbol ξ := by
  rw [← thermalSymbol_abs η, ← thermalSymbol_abs ξ]
  have hη : 0 < |η| := lt_of_le_of_lt (abs_nonneg ξ) h
  rcases (abs_nonneg ξ).lt_or_eq with hξ | hξ
  · exact thermalSymbol_strictAntiOn_pos hξ hη h
  · rw [← hξ, thermalSymbol_zero]
    exact thermalSymbol_lt_four hη.ne'

theorem abs_eq_of_thermalSymbol_eq {ξ η : ℝ} (h : thermalSymbol ξ = thermalSymbol η) : |ξ| = |η| := by
  rcases lt_trichotomy |ξ| |η| with hlt | heq | hgt
  · exact absurd h (thermalSymbol_lt_of_abs_lt hlt).ne'
  · exact heq
  · exact absurd h (thermalSymbol_lt_of_abs_lt hgt).ne

/-! ### The derivative -/

/-- `sinh t - t cosh t < 0` for `t > 0`: it vanishes at `0` and has derivative `-t sinh t`. -/
theorem sinh_sub_mul_cosh_neg {t : ℝ} (ht : 0 < t) : Real.sinh t - t * Real.cosh t < 0 := by
  have hderiv : ∀ x, HasDerivAt (fun x => Real.sinh x - x * Real.cosh x) (-x * Real.sinh x) x := by
    intro x
    have h := (Real.hasDerivAt_sinh x).sub ((hasDerivAt_id' x).mul (Real.hasDerivAt_cosh x))
    refine h.congr_deriv ?_
    ring
  have hcont : ContinuousOn (fun x => Real.sinh x - x * Real.cosh x) (Ici 0) :=
    (Real.continuous_sinh.sub (continuous_id.mul Real.continuous_cosh)).continuousOn
  have hanti : StrictAntiOn (fun x => Real.sinh x - x * Real.cosh x) (Ici 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici 0) hcont
    intro x hx
    have hx0 : 0 < x := by simpa using hx
    rw [(hderiv x).deriv]
    have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx0
    nlinarith [mul_pos hx0 hs]
  have h := hanti (by simp : (0 : ℝ) ∈ Ici 0) (by simp [ht.le] : t ∈ Ici 0) ht
  simpa using h

/-- `m'(ξ) = 4π (sinh(πξ) - πξ cosh(πξ)) / sinh²(πξ)`, `m'(0) = 0`. -/
def thermalSymbolDeriv (ξ : ℝ) : ℝ :=
  if ξ = 0 then 0 else
    4 * π * (Real.sinh (π * ξ) - π * ξ * Real.cosh (π * ξ)) / Real.sinh (π * ξ) ^ 2

theorem thermalSymbolDeriv_of_ne {ξ : ℝ} (hξ : ξ ≠ 0) :
    thermalSymbolDeriv ξ =
      4 * π * (Real.sinh (π * ξ) - π * ξ * Real.cosh (π * ξ)) / Real.sinh (π * ξ) ^ 2 :=
  if_neg hξ

theorem thermalSymbolDeriv_zero : thermalSymbolDeriv 0 = 0 := if_pos rfl

/-- `m'` is odd. -/
theorem thermalSymbolDeriv_neg (ξ : ℝ) : thermalSymbolDeriv (-ξ) = -thermalSymbolDeriv ξ := by
  by_cases hξ : ξ = 0
  · subst hξ; simp [thermalSymbolDeriv_zero]
  · rw [thermalSymbolDeriv_of_ne hξ, thermalSymbolDeriv_of_ne (neg_ne_zero.mpr hξ),
      show π * -ξ = -(π * ξ) by ring, Real.sinh_neg, Real.cosh_neg]
    ring

/-- `m'(ξ) < 0` for `ξ > 0`. -/
theorem thermalSymbolDeriv_neg_of_pos {ξ : ℝ} (hξ : 0 < ξ) : thermalSymbolDeriv ξ < 0 := by
  rw [thermalSymbolDeriv_of_ne hξ.ne']
  have ht : 0 < π * ξ := mul_pos pi_pos hξ
  have hN := sinh_sub_mul_cosh_neg ht
  have hs : 0 < Real.sinh (π * ξ) ^ 2 := by
    have := Real.sinh_pos_iff.mpr ht; positivity
  exact div_neg_of_neg_of_pos (by nlinarith [pi_pos]) hs

/-- `m'(ξ) > 0` for `ξ < 0`. -/
theorem thermalSymbolDeriv_pos_of_neg {ξ : ℝ} (hξ : ξ < 0) : 0 < thermalSymbolDeriv ξ := by
  have h := thermalSymbolDeriv_neg_of_pos (neg_pos.mpr hξ)
  rw [thermalSymbolDeriv_neg] at h
  linarith

/-- **Orientation law**: `sgn m'(ξ) = sgn(-1/ξ)`. -/
theorem sign_thermalSymbolDeriv (ξ : ℝ) : SignType.sign (thermalSymbolDeriv ξ) = SignType.sign (-1 / ξ) := by
  rcases lt_trichotomy ξ 0 with h | h | h
  · rw [sign_pos (thermalSymbolDeriv_pos_of_neg h), sign_pos (by
      rw [neg_div]; exact neg_pos.mpr (one_div_neg.mpr h))]
  · subst h; simp [thermalSymbolDeriv_zero]
  · rw [sign_neg (thermalSymbolDeriv_neg_of_pos h), sign_neg (by
      rw [neg_div]; exact neg_neg_of_pos (one_div_pos.mpr h))]

/-- `m` has derivative `m'` away from `0`. -/
theorem hasDerivAt_thermalSymbol_of_ne {ξ : ℝ} (hξ : ξ ≠ 0) :
    HasDerivAt thermalSymbol (thermalSymbolDeriv ξ) ξ := by
  have hs := sinh_pi_mul_ne_zero hξ
  have hnum : HasDerivAt (fun x => π * x) π ξ := by
    simpa using (hasDerivAt_id' ξ).const_mul π
  have hden : HasDerivAt (fun x => Real.sinh (π * x)) (Real.cosh (π * ξ) * π) ξ :=
    (Real.hasDerivAt_sinh (π * ξ)).comp ξ hnum
  have h := (hnum.div hden hs).const_mul 4
  have heq : (fun x => 4 * (π * x / Real.sinh (π * x))) =ᶠ[𝓝 ξ] thermalSymbol := by
    filter_upwards [eventually_ne_nhds hξ] with x hx
    rw [thermalSymbol_of_ne hx]
  refine (h.congr_of_eventuallyEq heq.symm).congr_deriv ?_
  rw [thermalSymbolDeriv_of_ne hξ]
  field_simp

/-! ### The top edge of the band -/

/-- `|4 - m(ξ) - (2π²/3) ξ²| ≤ 5 π⁴ ξ⁴` for `|πξ| ≤ 1`. -/
theorem abs_four_sub_thermalSymbol_sub_le {ξ : ℝ} (hξ : |π * ξ| ≤ 1) :
    |4 - thermalSymbol ξ - 2 * π ^ 2 / 3 * ξ ^ 2| ≤ 5 * π ^ 4 * ξ ^ 4 := by
  by_cases h0 : ξ = 0
  · subst h0; simp [thermalSymbol_zero]
  rw [thermalSymbol_of_ne h0]
  set t := π * ξ with ht
  set s := Real.sinh t with hsdef
  have hs0 : s ≠ 0 := sinh_pi_mul_ne_zero h0
  have hts := abs_le_abs_sinh t
  have he := abs_sinh_sub_cubic_le hξ
  set e := s - (t + t ^ 3 / 6) with hedef
  have hkey : 4 - 4 * (t / s) - 2 * π ^ 2 / 3 * ξ ^ 2 =
      (4 * e - t ^ 5 / 9 - 2 / 3 * t ^ 2 * e) / s := by
    rw [hedef, ht]; field_simp; ring
  have ht1 : |t| ^ 2 ≤ 1 := by nlinarith [abs_nonneg t]
  have hnum : |4 * e - t ^ 5 / 9 - 2 / 3 * t ^ 2 * e| ≤ 5 * |t| ^ 5 := by
    have h1 : |4 * e| ≤ 4 * |t| ^ 5 := by rw [abs_mul]; norm_num; linarith
    have h2 : |t ^ 5 / 9| ≤ |t| ^ 5 / 9 := by rw [abs_div, abs_pow]; norm_num
    have h3 : |2 / 3 * t ^ 2 * e| ≤ 2 / 3 * |t| ^ 5 := by
      rw [abs_mul, abs_mul, abs_pow]
      have : |(2 / 3 : ℝ)| = 2 / 3 := by norm_num
      rw [this]
      have hte : |t| ^ 2 * |e| ≤ 1 * |t| ^ 5 := mul_le_mul ht1 he (abs_nonneg _) zero_le_one
      nlinarith [abs_nonneg e, pow_nonneg (abs_nonneg t) 2]
    have b1 := abs_sub (4 * e - t ^ 5 / 9) (2 / 3 * t ^ 2 * e)
    have b2 := abs_sub (4 * e) (t ^ 5 / 9)
    nlinarith [pow_nonneg (abs_nonneg t) 5]
  have htpos : 0 < |t| := abs_pos.mpr (pi_mul_ne_zero h0)
  rw [hkey, abs_div, div_le_iff₀ (abs_pos.mpr hs0)]
  calc |4 * e - t ^ 5 / 9 - 2 / 3 * t ^ 2 * e| ≤ 5 * |t| ^ 5 := hnum
    _ = 5 * |t| ^ 4 * |t| := by ring
    _ ≤ 5 * |t| ^ 4 * |s| := by gcongr
    _ = 5 * π ^ 4 * ξ ^ 4 * |s| := by
        rw [ht, abs_mul, abs_of_pos pi_pos, mul_pow]
        rw [show |ξ| ^ 4 = ξ ^ 4 by rw [← abs_pow]; exact abs_of_nonneg (by positivity)]
        ring

/-- `|m'(ξ) + (4π²/3) ξ| ≤ 15 π⁴ |ξ|³` for `|πξ| ≤ 1`. -/
theorem abs_thermalSymbolDeriv_add_le {ξ : ℝ} (hξ : |π * ξ| ≤ 1) :
    |thermalSymbolDeriv ξ + 4 * π ^ 2 / 3 * ξ| ≤ 15 * π ^ 4 * |ξ| ^ 3 := by
  by_cases h0 : ξ = 0
  · subst h0; simp [thermalSymbolDeriv_zero]
  rw [thermalSymbolDeriv_of_ne h0]
  set t := π * ξ with ht
  set s := Real.sinh t with hsdef
  set c := Real.cosh t with hcdef
  have hs0 : s ≠ 0 := sinh_pi_mul_ne_zero h0
  have hts := abs_le_abs_sinh t
  have he1 := abs_sinh_sub_cubic_le hξ
  have he2 := abs_cosh_sub_quadratic_le hξ
  set e₁ := s - (t + t ^ 3 / 6) with he1def
  set e₂ := c - (1 + t ^ 2 / 2) with he2def
  set u := t ^ 3 / 6 + e₁ with hudef
  have hkey : 4 * π * (s - t * c) / s ^ 2 + 4 * π ^ 2 / 3 * ξ =
      4 * π * (3 * e₁ - 3 * t * e₂ + t ^ 5 / 3 + 2 * t ^ 2 * e₁ + t * u ^ 2) / (3 * s ^ 2) := by
    rw [hudef, he1def, he2def, ht]; field_simp; ring
  have ht1 : |t| ≤ 1 := hξ
  have htp : 0 ≤ |t| := abs_nonneg t
  have hu : |u| ≤ 7 / 6 * |t| ^ 3 := by
    rw [hudef]
    refine (abs_add_le _ _).trans ?_
    rw [abs_div, abs_pow]
    have : |t| ^ 5 ≤ |t| ^ 3 := pow_le_pow_of_le_one htp ht1 (by norm_num)
    norm_num; linarith
  have hnum : |3 * e₁ - 3 * t * e₂ + t ^ 5 / 3 + 2 * t ^ 2 * e₁ + t * u ^ 2| ≤ 11 * |t| ^ 5 := by
    have h5 : |t| ^ 7 ≤ |t| ^ 5 := pow_le_pow_of_le_one htp ht1 (by norm_num)
    have a1 : |3 * e₁| ≤ 3 * |t| ^ 5 := by rw [abs_mul]; norm_num; linarith
    have a2 : |3 * t * e₂| ≤ 3 * |t| ^ 5 := by
      rw [abs_mul, abs_mul]; norm_num
      have : |t| * |e₂| ≤ |t| * |t| ^ 4 := mul_le_mul_of_nonneg_left he2 htp
      nlinarith
    have a3 : |t ^ 5 / 3| ≤ |t| ^ 5 / 3 := by rw [abs_div, abs_pow]; norm_num
    have a4 : |2 * t ^ 2 * e₁| ≤ 2 * |t| ^ 5 := by
      rw [abs_mul, abs_mul, abs_pow, sq_abs]
      have ht2 : t ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith
      have : t ^ 2 * |e₁| ≤ 1 * |t| ^ 5 := mul_le_mul ht2 he1 (abs_nonneg _) zero_le_one
      have h2 : |(2 : ℝ)| = 2 := by norm_num
      rw [h2]
      nlinarith
    have a5 : |t * u ^ 2| ≤ 2 * |t| ^ 5 := by
      rw [abs_mul, abs_pow]
      have hu2 : |u| ^ 2 ≤ (7 / 6 * |t| ^ 3) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hu 2
      have : |t| * |u| ^ 2 ≤ |t| * (7 / 6 * |t| ^ 3) ^ 2 := mul_le_mul_of_nonneg_left hu2 htp
      nlinarith
    have c1 := abs_add_le (3 * e₁ - 3 * t * e₂ + t ^ 5 / 3 + 2 * t ^ 2 * e₁) (t * u ^ 2)
    have c2 := abs_add_le (3 * e₁ - 3 * t * e₂ + t ^ 5 / 3) (2 * t ^ 2 * e₁)
    have c3 := abs_add_le (3 * e₁ - 3 * t * e₂) (t ^ 5 / 3)
    have c4 := abs_sub (3 * e₁) (3 * t * e₂)
    linarith [pow_nonneg htp 5]
  have htpos : 0 < |t| := abs_pos.mpr (pi_mul_ne_zero h0)
  have hs2 : t ^ 2 ≤ s ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) hts 2
    rwa [sq_abs, sq_abs] at this
  have hts2 : 0 < t ^ 2 := by positivity
  rw [hkey, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * π),
    abs_of_pos (by positivity : (0 : ℝ) < 3 * s ^ 2), div_le_iff₀ (by positivity)]
  calc 4 * π * |3 * e₁ - 3 * t * e₂ + t ^ 5 / 3 + 2 * t ^ 2 * e₁ + t * u ^ 2|
      ≤ 4 * π * (11 * |t| ^ 5) := by gcongr
    _ = 44 * π * |t| ^ 3 * t ^ 2 := by rw [← sq_abs t]; ring
    _ ≤ 44 * π * |t| ^ 3 * s ^ 2 := by gcongr
    _ ≤ 15 * π ^ 4 * |ξ| ^ 3 * (3 * s ^ 2) := by
        rw [ht, abs_mul, abs_of_pos pi_pos, mul_pow]
        have hX : 0 ≤ π ^ 4 * |ξ| ^ 3 * s ^ 2 := by positivity
        calc 44 * π * (π ^ 3 * |ξ| ^ 3) * s ^ 2 = 44 * (π ^ 4 * |ξ| ^ 3 * s ^ 2) := by ring
          _ ≤ 45 * (π ^ 4 * |ξ| ^ 3 * s ^ 2) := by linarith
          _ = 15 * π ^ 4 * |ξ| ^ 3 * (3 * s ^ 2) := by ring

theorem eventually_abs_pi_mul_le_one : ∀ᶠ ξ : ℝ in 𝓝 0, |π * ξ| ≤ 1 := by
  have h : Tendsto (fun ξ : ℝ => π * ξ) (𝓝 0) (𝓝 0) := by
    have := (continuous_const_mul π).tendsto 0
    simpa using this
  filter_upwards [h (Metric.closedBall_mem_nhds (0 : ℝ) one_pos)] with ξ hξ
  simpa [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hξ

/-- **(5)** `4 - m(ξ) = (2π²/3) ξ² + O(ξ⁴)`. -/
theorem isBigO_four_sub_thermalSymbol :
    (fun ξ => 4 - thermalSymbol ξ - 2 * π ^ 2 / 3 * ξ ^ 2) =O[𝓝 0] fun ξ => ξ ^ 4 := by
  refine IsBigO.of_bound (5 * π ^ 4) ?_
  filter_upwards [eventually_abs_pi_mul_le_one] with ξ hξ
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ξ ^ 4)]
  exact abs_four_sub_thermalSymbol_sub_le hξ

/-- **(5)** `m'(ξ) = -(4π²/3) ξ + O(ξ³)`. -/
theorem isBigO_thermalSymbolDeriv_add :
    (fun ξ => thermalSymbolDeriv ξ + 4 * π ^ 2 / 3 * ξ) =O[𝓝 0] fun ξ => ξ ^ 3 := by
  refine IsBigO.of_bound (15 * π ^ 4) ?_
  filter_upwards [eventually_abs_pi_mul_le_one] with ξ hξ
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
  exact abs_thermalSymbolDeriv_add_le hξ

/-- `m` is differentiable at `0` with `m'(0) = 0`. -/
theorem hasDerivAt_thermalSymbol_zero : HasDerivAt thermalSymbol 0 0 := by
  rw [hasDerivAt_iff_isLittleO]
  have hsq : (fun ξ : ℝ => thermalSymbol ξ - 4) =O[𝓝 0] fun ξ => ξ ^ 2 := by
    refine IsBigO.of_bound (2 * π ^ 2 / 3 + 5 * π ^ 4) ?_
    filter_upwards [eventually_abs_pi_mul_le_one] with ξ hξ
    have h := abs_four_sub_thermalSymbol_sub_le hξ
    have hξ1 : ξ ^ 4 ≤ ξ ^ 2 * (1 / π ^ 2) := by
      have hpi : 0 < π := pi_pos
      have h2 : π ^ 2 * ξ ^ 2 ≤ 1 := by
        have := pow_le_pow_left₀ (abs_nonneg _) hξ 2
        rw [sq_abs, mul_pow] at this; linarith
      rw [show ξ ^ 4 = ξ ^ 2 * ξ ^ 2 by ring]
      gcongr
      rw [le_div_iff₀ (by positivity)]; linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ξ)]
    have hpi2 : 0 < π ^ 2 := by positivity
    calc |thermalSymbol ξ - 4| ≤ |4 - thermalSymbol ξ - 2 * π ^ 2 / 3 * ξ ^ 2| +
          2 * π ^ 2 / 3 * ξ ^ 2 := by
          have := abs_add_le (-(4 - thermalSymbol ξ - 2 * π ^ 2 / 3 * ξ ^ 2))
            (2 * π ^ 2 / 3 * ξ ^ 2)
          rw [abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * π ^ 2 / 3 * ξ ^ 2)] at this
          have e : -(4 - thermalSymbol ξ - 2 * π ^ 2 / 3 * ξ ^ 2) + 2 * π ^ 2 / 3 * ξ ^ 2 =
            thermalSymbol ξ - 4 + 4 * π ^ 2 / 3 * ξ ^ 2 := by ring
          rw [abs_sub_comm] at *
          calc |4 - thermalSymbol ξ| = |(4 - thermalSymbol ξ - 2 * π ^ 2 / 3 * ξ ^ 2) +
              2 * π ^ 2 / 3 * ξ ^ 2| := by ring_nf
            _ ≤ _ := by
                refine (abs_add_le _ _).trans (le_of_eq ?_)
                rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * π ^ 2 / 3 * ξ ^ 2)]
      _ ≤ 5 * π ^ 4 * ξ ^ 4 + 2 * π ^ 2 / 3 * ξ ^ 2 := by linarith
      _ ≤ 5 * π ^ 4 * (ξ ^ 2 * (1 / π ^ 2)) + 2 * π ^ 2 / 3 * ξ ^ 2 := by gcongr
      _ ≤ (2 * π ^ 2 / 3 + 5 * π ^ 4) * ξ ^ 2 := by
          have : 5 * π ^ 4 * (ξ ^ 2 * (1 / π ^ 2)) = 5 * π ^ 2 * ξ ^ 2 := by field_simp
          rw [this]
          have h1 : π ^ 2 ≤ π ^ 4 := by
            have := Real.pi_gt_three
            have h9 : 1 ≤ π ^ 2 := by nlinarith
            have := mul_le_mul_of_nonneg_left h9 (sq_nonneg π)
            nlinarith
          nlinarith [sq_nonneg ξ]
  have hlo := hsq.trans_isLittleO (isLittleO_pow_id (by norm_num : 1 < 2))
  refine hlo.congr' (Eventually.of_forall fun ξ => ?_) (Eventually.of_forall fun ξ => ?_)
  · simp [thermalSymbol_zero]
  · simp

/-- `m` has derivative `m'` everywhere. -/
theorem hasDerivAt_thermalSymbol (ξ : ℝ) : HasDerivAt thermalSymbol (thermalSymbolDeriv ξ) ξ := by
  by_cases h : ξ = 0
  · subst h; rw [thermalSymbolDeriv_zero]; exact hasDerivAt_thermalSymbol_zero
  · exact hasDerivAt_thermalSymbol_of_ne h

/-- **(5)** `(-1/ξ) m'(ξ) → 4π²/3` at the top edge. -/
theorem tendsto_neg_inv_mul_thermalSymbolDeriv :
    Tendsto (fun ξ => (-1 / ξ) * thermalSymbolDeriv ξ) (𝓝[≠] 0) (𝓝 (4 * π ^ 2 / 3)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hδ : 0 < min (1 / π) (Real.sqrt (ε / (15 * π ^ 4))) := by
    have := pi_pos
    exact lt_min (by positivity) (Real.sqrt_pos.mpr (by positivity))
  refine ⟨_, hδ, fun ξ hξ hdist => ?_⟩
  have hξ0 : ξ ≠ 0 := hξ
  rw [dist_zero_right, Real.norm_eq_abs] at hdist
  have hpi := pi_pos
  have h1 : |π * ξ| ≤ 1 := by
    rw [abs_mul, abs_of_pos hpi]
    have := hdist.trans_le (min_le_left _ _)
    rw [lt_div_iff₀ hpi] at this; linarith
  have hb := abs_thermalSymbolDeriv_add_le h1
  rw [Real.dist_eq]
  have e : (-1 / ξ) * thermalSymbolDeriv ξ - 4 * π ^ 2 / 3 =
      -(thermalSymbolDeriv ξ + 4 * π ^ 2 / 3 * ξ) / ξ := by field_simp; ring
  rw [e, abs_div, abs_neg, div_lt_iff₀ (abs_pos.mpr hξ0)]
  have h2 : |ξ| ^ 2 < ε / (15 * π ^ 4) := by
    have := hdist.trans_le (min_le_right _ _)
    have h3 := pow_lt_pow_left₀ this (abs_nonneg ξ) two_ne_zero
    rwa [Real.sq_sqrt (by positivity)] at h3
  have hpos : 0 < |ξ| := abs_pos.mpr hξ0
  calc |thermalSymbolDeriv ξ + 4 * π ^ 2 / 3 * ξ| ≤ 15 * π ^ 4 * |ξ| ^ 3 := hb
    _ = 15 * π ^ 4 * |ξ| ^ 2 * |ξ| := by ring
    _ < 15 * π ^ 4 * (ε / (15 * π ^ 4)) * |ξ| := by gcongr
    _ = ε * |ξ| := by field_simp

/-- `(4 - m(ξ))/ξ² → 2π²/3`. -/
theorem tendsto_four_sub_thermalSymbol_div_sq :
    Tendsto (fun ξ => (4 - thermalSymbol ξ) / ξ ^ 2) (𝓝[≠] 0) (𝓝 (2 * π ^ 2 / 3)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hδ : 0 < min (1 / π) (Real.sqrt (ε / (5 * π ^ 4))) := by
    have := pi_pos
    exact lt_min (by positivity) (Real.sqrt_pos.mpr (by positivity))
  refine ⟨_, hδ, fun ξ hξ hdist => ?_⟩
  have hξ0 : ξ ≠ 0 := hξ
  rw [dist_zero_right, Real.norm_eq_abs] at hdist
  have hpi := pi_pos
  have h1 : |π * ξ| ≤ 1 := by
    rw [abs_mul, abs_of_pos hpi]
    have := hdist.trans_le (min_le_left _ _)
    rw [lt_div_iff₀ hpi] at this; linarith
  have hb := abs_four_sub_thermalSymbol_sub_le h1
  rw [Real.dist_eq]
  have hsq : 0 < ξ ^ 2 := by positivity
  have e : (4 - thermalSymbol ξ) / ξ ^ 2 - 2 * π ^ 2 / 3 =
      (4 - thermalSymbol ξ - 2 * π ^ 2 / 3 * ξ ^ 2) / ξ ^ 2 := by field_simp
  rw [e, abs_div, abs_of_pos hsq, div_lt_iff₀ hsq]
  have h2 : ξ ^ 2 < ε / (5 * π ^ 4) := by
    have := hdist.trans_le (min_le_right _ _)
    have h3 := pow_lt_pow_left₀ this (abs_nonneg ξ) two_ne_zero
    rwa [Real.sq_sqrt (by positivity), sq_abs] at h3
  calc |4 - thermalSymbol ξ - 2 * π ^ 2 / 3 * ξ ^ 2| ≤ 5 * π ^ 4 * ξ ^ 4 := hb
    _ = 5 * π ^ 4 * ξ ^ 2 * ξ ^ 2 := by ring
    _ < 5 * π ^ 4 * (ε / (5 * π ^ 4)) * ξ ^ 2 := by gcongr
    _ = ε * ξ ^ 2 := by field_simp

/-- **Square-root edge law** `|S| ∼ π √(2/3) / √(4 - W)`: `√(4 - m(ξ)) / |ξ| → π √(2/3)`. -/
theorem tendsto_sqrt_four_sub_thermalSymbol_div_abs :
    Tendsto (fun ξ => Real.sqrt (4 - thermalSymbol ξ) / |ξ|) (𝓝[≠] 0)
      (𝓝 (π * Real.sqrt (2 / 3))) := by
  have h := (Real.continuous_sqrt.tendsto _).comp tendsto_four_sub_thermalSymbol_div_sq
  have hval : Real.sqrt (2 * π ^ 2 / 3) = π * Real.sqrt (2 / 3) := by
    rw [show 2 * π ^ 2 / 3 = π ^ 2 * (2 / 3) by ring, Real.sqrt_mul (sq_nonneg π),
      Real.sqrt_sq pi_pos.le]
  rw [hval] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ξ hξ
  have hξ0 : ξ ≠ 0 := hξ
  simp only [Function.comp_apply]
  rw [Real.sqrt_div' _ (sq_nonneg ξ), Real.sqrt_sq_eq_abs]

/-! ### Regularity -/

theorem continuous_thermalSymbol : Continuous thermalSymbol :=
  continuous_iff_continuousAt.mpr fun ξ => (hasDerivAt_thermalSymbol ξ).continuousAt

theorem measurable_thermalSymbol : Measurable thermalSymbol := continuous_thermalSymbol.measurable

theorem deriv_thermalSymbol : deriv thermalSymbol = thermalSymbolDeriv :=
  funext fun ξ => (hasDerivAt_thermalSymbol ξ).deriv

theorem measurable_thermalSymbolDeriv : Measurable thermalSymbolDeriv := by
  rw [← deriv_thermalSymbol]; exact measurable_deriv _

theorem thermalSymbol_le_four (ξ : ℝ) : thermalSymbol ξ ≤ 4 := by
  by_cases h : ξ = 0
  · rw [h, thermalSymbol_zero]
  · exact (thermalSymbol_lt_four h).le

/-! ### Orientation: the joint symbol `(m, m')` -/

theorem thermalSymbolDeriv_ne_zero {ξ : ℝ} (hξ : ξ ≠ 0) : thermalSymbolDeriv ξ ≠ 0 := by
  rcases hξ.lt_or_gt with h | h
  · exact (thermalSymbolDeriv_pos_of_neg h).ne'
  · exact (thermalSymbolDeriv_neg_of_pos h).ne

/-- **`m` alone loses the orientation:** `m(ξ) = m(η)` iff `|ξ| = |η|`. -/
theorem thermalSymbol_eq_iff {ξ η : ℝ} : thermalSymbol ξ = thermalSymbol η ↔ |ξ| = |η| := by
  refine ⟨abs_eq_of_thermalSymbol_eq, fun h => ?_⟩
  rw [← thermalSymbol_abs ξ, h, thermalSymbol_abs]

/-- **The joint symbol `(m, m')` is injective.** -/
theorem thermalSymbol_joint_injective :
    Function.Injective fun ξ => (thermalSymbol ξ, thermalSymbolDeriv ξ) := by
  intro ξ η h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  rcases abs_eq_abs.mp (abs_eq_of_thermalSymbol_eq h1) with e | e
  · exact e
  · subst e
    by_contra hne
    have hη : η ≠ 0 := fun h0 => hne (by rw [h0, neg_zero])
    rw [thermalSymbolDeriv_neg] at h2
    exact thermalSymbolDeriv_ne_zero hη (by linarith)

/-! ### The symbols as functions of the flat primitive -/

/-- `F(t) = 4π / (t sinh(π/t))`, `F(0) = 0`: `m(ξ) = F(-1/ξ)`. -/
def primitiveThermalSymbol (t : ℝ) : ℝ := if t = 0 then 0 else thermalSymbol (-1 / t)

/-- `G(t) = m'(-1/t)`, `G(0) = 0`. -/
def primitiveThermalSymbolDeriv (t : ℝ) : ℝ := if t = 0 then 0 else thermalSymbolDeriv (-1 / t)

theorem primitiveThermalSymbol_of_ne {t : ℝ} (ht : t ≠ 0) :
    primitiveThermalSymbol t = 4 * π / (t * Real.sinh (π / t)) := by
  rw [primitiveThermalSymbol, if_neg ht, thermalSymbol_of_ne (by simpa [neg_div] using ht),
    show π * (-1 / t) = -(π / t) by ring, Real.sinh_neg]
  field_simp

theorem primitiveThermalSymbol_zero : primitiveThermalSymbol 0 = 0 := if_pos rfl

theorem primitiveThermalSymbolDeriv_zero : primitiveThermalSymbolDeriv 0 = 0 := if_pos rfl

/-- `m(ξ) = F(-1/ξ)` for `ξ ≠ 0`. -/
theorem primitiveThermalSymbol_neg_inv {ξ : ℝ} (hξ : ξ ≠ 0) :
    primitiveThermalSymbol (-1 / ξ) = thermalSymbol ξ := by
  rw [primitiveThermalSymbol, if_neg (by simpa [neg_div] using hξ)]
  congr 1
  field_simp

/-- `m'(ξ) = G(-1/ξ)` for `ξ ≠ 0`. -/
theorem primitiveThermalSymbolDeriv_neg_inv {ξ : ℝ} (hξ : ξ ≠ 0) :
    primitiveThermalSymbolDeriv (-1 / ξ) = thermalSymbolDeriv ξ := by
  rw [primitiveThermalSymbolDeriv, if_neg (by simpa [neg_div] using hξ)]
  congr 1
  field_simp

/-- `F` is even. -/
theorem primitiveThermalSymbol_neg (t : ℝ) : primitiveThermalSymbol (-t) = primitiveThermalSymbol t := by
  by_cases ht : t = 0
  · subst ht; simp
  · rw [primitiveThermalSymbol, if_neg (neg_ne_zero.mpr ht), primitiveThermalSymbol, if_neg ht,
      show -1 / -t = -(-1 / t) by ring, thermalSymbol_even]

/-- `G` is odd. -/
theorem primitiveThermalSymbolDeriv_neg (t : ℝ) :
    primitiveThermalSymbolDeriv (-t) = -primitiveThermalSymbolDeriv t := by
  by_cases ht : t = 0
  · subst ht; simp [primitiveThermalSymbolDeriv_zero]
  · rw [primitiveThermalSymbolDeriv, if_neg (neg_ne_zero.mpr ht), primitiveThermalSymbolDeriv,
      if_neg ht, show -1 / -t = -(-1 / t) by ring, thermalSymbolDeriv_neg]

theorem primitiveThermalSymbol_nonneg (t : ℝ) : 0 ≤ primitiveThermalSymbol t := by
  unfold primitiveThermalSymbol
  split_ifs
  · exact le_rfl
  · exact (thermalSymbol_pos _).le

theorem primitiveThermalSymbol_pos {t : ℝ} (ht : t ≠ 0) : 0 < primitiveThermalSymbol t := by
  rw [primitiveThermalSymbol, if_neg ht]; exact thermalSymbol_pos _

/-- `F` takes values in `[0, 4]`. -/
theorem primitiveThermalSymbol_le_four (t : ℝ) : primitiveThermalSymbol t ≤ 4 := by
  unfold primitiveThermalSymbol
  split_ifs
  · norm_num
  · exact thermalSymbol_le_four _

/-- **`sgn G(t) = sgn t`.** -/
theorem sign_primitiveThermalSymbolDeriv (t : ℝ) :
    SignType.sign (primitiveThermalSymbolDeriv t) = SignType.sign t := by
  by_cases ht : t = 0
  · subst ht; simp [primitiveThermalSymbolDeriv_zero]
  · rw [primitiveThermalSymbolDeriv, if_neg ht, sign_thermalSymbolDeriv]
    congr 1
    field_simp

theorem measurable_primitiveThermalSymbol : Measurable primitiveThermalSymbol :=
  Measurable.ite (measurableSet_singleton 0) measurable_const
    (measurable_thermalSymbol.comp (measurable_const.div measurable_id))

theorem measurable_primitiveThermalSymbolDeriv : Measurable primitiveThermalSymbolDeriv :=
  Measurable.ite (measurableSet_singleton 0) measurable_const
    (measurable_thermalSymbolDeriv.comp (measurable_const.div measurable_id))

end

end RHTower
