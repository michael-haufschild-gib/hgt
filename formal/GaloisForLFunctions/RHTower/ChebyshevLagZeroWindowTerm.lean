import GaloisForLFunctions.RHTower.ChebyshevLagWindow

/-!
# The zero side of a `ψ` window average

Dividing the window statistic `J(a, b)` by `1/a - 1/b = ∫_a^b t^{-2} dt` turns the genus-kernel zero
sum into a sum of window terms

`T(ρ; a, b) = (b^{ρ-1} - a^{ρ-1}) / (ρ(1-ρ)(1/a - 1/b)) = -(1/ρ) · (∫_a^b t^{ρ} t^{-2} dt)/(∫_a^b t^{-2} dt)`,

so `-ρ T(ρ; a, b)` is the `t^{-2}`-weighted mean of `t^ρ` over the window.  Two bounds follow.

* **Short range.**  If `x ≤ a < b`, the mean differs from `x^ρ` by at most `|ρ|(b - x)x^{β-1}`;
  hence two windows inside `[x, x + H]` have terms differing by at most `2H x^{β-1}`.
* **Long range.**  `|T(ρ; a, b)| ≤ (a^{β-1} + b^{β-1}) / (|ρ||1-ρ|(1/a - 1/b))`.

Combining the squeeze `ψ(a) ≤ J(a,b)/(1/a-1/b) ≤ ψ(b)` for a right window `[x+h-h', x+h]` and a left
window `[x, x+h']` gives the lower bound

`ψ(x+h) - ψ(x) ≥ h - 2h' - 4/(x h') - Σ_ρ |T(ρ; x+h-h', x+h) - T(ρ; x, x+h')|`.
-/

namespace RHTower

noncomputable section

open Complex Finset

/-- The window term of a zero `ρ` on the window `[a, b]`. -/
def lagWindowZeroTerm (ρ : ℂ) (a b : ℝ) : ℂ :=
  ((b : ℂ) ^ (ρ - 1) - (a : ℂ) ^ (ρ - 1)) / (ρ * (1 - ρ) * ((1 / a - 1 / b : ℝ) : ℂ))

/-- The mean-value bound `|t^ρ - x^ρ| ≤ |ρ|(t - x)x^{β-1}` for `0 < x ≤ t` and `0 < β ≤ 1`. -/
theorem norm_ofReal_cpow_sub_cpow_le {x t : ℝ} (hx : 0 < x) (hxt : x ≤ t) {ρ : ℂ}
    (hρ0 : 0 < ρ.re) (hρ1 : ρ.re ≤ 1) :
    ‖(t : ℂ) ^ ρ - (x : ℂ) ^ ρ‖ ≤ ‖ρ‖ * (t - x) * x ^ (ρ.re - 1) := by
  have hρne : ρ ≠ 0 := fun h => by rw [h, Complex.zero_re] at hρ0; exact lt_irrefl 0 hρ0
  have hint := integral_cpow (a := x) (b := t) (r := ρ - 1) (Or.inl (by simp; linarith))
  rw [sub_add_cancel] at hint
  have heq : (t : ℂ) ^ ρ - (x : ℂ) ^ ρ = ρ * ∫ s in x..t, (s : ℂ) ^ (ρ - 1) := by
    rw [hint]
    field_simp
  rw [heq, norm_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hbound : ∀ s ∈ Set.uIoc x t, ‖(s : ℂ) ^ (ρ - 1)‖ ≤ x ^ (ρ.re - 1) := by
    intro s hs
    rw [Set.uIoc_of_le hxt] at hs
    have hs0 : 0 < s := lt_trans hx hs.1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hs0, Complex.sub_re, Complex.one_re]
    exact Real.rpow_le_rpow_of_nonpos hx hs.1.le (by linarith)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [abs_of_nonneg (by linarith : 0 ≤ t - x)] at h
  linarith

/-- `∫_a^b t^{-2} dt = 1/a - 1/b`, complex form. -/
theorem integral_ofReal_cpow_neg_two {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b, (t : ℂ) ^ (-2 : ℂ) = ((1 / a - 1 / b : ℝ) : ℂ) := by
  have h0 : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    intro h
    linarith [h.1]
  rw [integral_cpow (Or.inr ⟨by norm_num, h0⟩)]
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have e1 : (-2 : ℂ) + 1 = -1 := by norm_num
  rw [e1, Complex.cpow_neg_one, Complex.cpow_neg_one]
  push_cast
  field_simp
  ring

/-- `∫_a^b t^{-2} dt = 1/a - 1/b`, real form. -/
theorem integral_zpow_neg_two {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b, t ^ (-2 : ℤ) = 1 / a - 1 / b := by
  have h0 : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    intro h
    linarith [h.1]
  rw [integral_zpow (Or.inr ⟨by norm_num, h0⟩)]
  have hb : 0 < b := lt_of_lt_of_le ha hab
  norm_num
  field_simp
  ring

/-- **Short range.**  `-ρ T(ρ; a, b)` is within `|ρ|(b - x)x^{β-1}` of `x^ρ` when `x ≤ a < b`. -/
theorem norm_mul_lagWindowZeroTerm_add_cpow_le {x a b : ℝ} (hx : 0 < x) (hxa : x ≤ a)
    (hab : a < b) {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    ‖ρ * lagWindowZeroTerm ρ a b + (x : ℂ) ^ ρ‖ ≤ ‖ρ‖ * (b - x) * x ^ (ρ.re - 1) := by
  have ha : 0 < a := lt_of_lt_of_le hx hxa
  have hb : 0 < b := lt_trans ha hab
  have hρne : ρ ≠ 0 := fun h => by rw [h, Complex.zero_re] at hρ0; exact lt_irrefl 0 hρ0
  have hρ1ne : 1 - ρ ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  have hw : 0 < 1 / a - 1 / b := by
    rw [sub_pos]
    exact one_div_lt_one_div_of_lt ha hab
  have hwC : ((1 / a - 1 / b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  have h0 : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab.le]
    intro h
    linarith [h.1]
  -- the two integrals
  have hI1 := integral_cpow (a := a) (b := b) (r := ρ - 2)
    (Or.inr ⟨fun h => by
      have := congrArg Complex.re h
      simp at this
      linarith, h0⟩)
  have e1 : ρ - 2 + 1 = ρ - 1 := by ring
  rw [e1] at hI1
  have hI0 := integral_ofReal_cpow_neg_two ha hab.le
  have hint1 : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (ρ - 2)) MeasureTheory.volume a b :=
    intervalIntegral.intervalIntegrable_cpow (Or.inr h0)
  have hint0 : IntervalIntegrable (fun t : ℝ => (x : ℂ) ^ ρ * (t : ℂ) ^ (-2 : ℂ))
      MeasureTheory.volume a b :=
    (intervalIntegral.intervalIntegrable_cpow (Or.inr h0)).const_mul _
  -- the centred representation
  set F : ℝ → ℂ := fun t => (t : ℂ) ^ (ρ - 2) - (x : ℂ) ^ ρ * (t : ℂ) ^ (-2 : ℂ) with hF
  have hIF : ∫ t in a..b, F t
      = ((b : ℂ) ^ (ρ - 1) - (a : ℂ) ^ (ρ - 1)) / (ρ - 1)
          - (x : ℂ) ^ ρ * ((1 / a - 1 / b : ℝ) : ℂ) := by
    rw [hF, intervalIntegral.integral_sub hint1 hint0, intervalIntegral.integral_const_mul, hI1,
      hI0]
  have hρm1 : ρ - 1 ≠ 0 := fun h => hρ1ne (by rw [← neg_sub, h, neg_zero])
  have hrep : ρ * lagWindowZeroTerm ρ a b + (x : ℂ) ^ ρ
      = -(∫ t in a..b, F t) / ((1 / a - 1 / b : ℝ) : ℂ) := by
    rw [hIF, lagWindowZeroTerm]
    generalize ((1 / a - 1 / b : ℝ) : ℂ) = W at hwC ⊢
    have hρ1ne' : (1 : ℂ) - ρ ≠ 0 := hρ1ne
    field_simp
    ring
  -- the pointwise bound
  set K : ℝ := ‖ρ‖ * (b - x) * x ^ (ρ.re - 1) with hK
  have hpt : ∀ t ∈ Set.Ioc a b, ‖F t‖ ≤ K * t ^ (-2 : ℤ) := by
    intro t ht
    have ht0 : 0 < t := lt_trans ha ht.1
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    have hsplit : F t = ((t : ℂ) ^ ρ - (x : ℂ) ^ ρ) * (t : ℂ) ^ (-2 : ℂ) := by
      rw [hF]
      simp only
      rw [show ρ - 2 = ρ + (-2 : ℂ) by ring, Complex.cpow_add _ _ htC]
      ring
    rw [hsplit, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hre : (-2 : ℂ).re = ((-2 : ℤ) : ℝ) := by norm_num
    rw [hre, Real.rpow_intCast]
    have hmv := norm_ofReal_cpow_sub_cpow_le hx (le_trans hxa ht.1.le) hρ0 hρ1.le
    have hmv' : ‖(t : ℂ) ^ ρ - (x : ℂ) ^ ρ‖ ≤ K := by
      refine le_trans hmv ?_
      rw [hK]
      have : 0 ≤ ‖ρ‖ := norm_nonneg _
      have : 0 ≤ x ^ (ρ.re - 1) := Real.rpow_nonneg hx.le _
      gcongr
      exact ht.2
    exact mul_le_mul_of_nonneg_right hmv' (zpow_nonneg ht0.le _)
  have hgint : IntervalIntegrable (fun t : ℝ => K * t ^ (-2 : ℤ)) MeasureTheory.volume a b :=
    (intervalIntegral.intervalIntegrable_zpow (Or.inr h0)).const_mul _
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le hab.le
    (MeasureTheory.ae_of_all _ hpt) hgint
  rw [intervalIntegral.integral_const_mul, integral_zpow_neg_two ha hab.le] at hnorm
  rw [hrep, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw,
    div_le_iff₀ hw]
  exact hnorm

/-- **Two windows in `[x, x + H]`.**  Their terms differ by at most `2H x^{β-1}`. -/
theorem norm_lagWindowZeroTerm_sub_le {x H a₁ b₁ a₂ b₂ : ℝ} (hx : 0 < x) (hxa₁ : x ≤ a₁)
    (hab₁ : a₁ < b₁) (hb₁ : b₁ ≤ x + H) (hxa₂ : x ≤ a₂) (hab₂ : a₂ < b₂) (hb₂ : b₂ ≤ x + H)
    {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    ‖lagWindowZeroTerm ρ a₁ b₁ - lagWindowZeroTerm ρ a₂ b₂‖ ≤ 2 * H * x ^ (ρ.re - 1) := by
  have hρne : ρ ≠ 0 := fun h => by rw [h, Complex.zero_re] at hρ0; exact lt_irrefl 0 hρ0
  have hρn : 0 < ‖ρ‖ := norm_pos_iff.mpr hρne
  have h1 := norm_mul_lagWindowZeroTerm_add_cpow_le hx hxa₁ hab₁ hρ0 hρ1
  have h2 := norm_mul_lagWindowZeroTerm_add_cpow_le hx hxa₂ hab₂ hρ0 hρ1
  have hxp : 0 ≤ x ^ (ρ.re - 1) := Real.rpow_nonneg hx.le _
  have hdiff : ρ * (lagWindowZeroTerm ρ a₁ b₁ - lagWindowZeroTerm ρ a₂ b₂)
      = (ρ * lagWindowZeroTerm ρ a₁ b₁ + (x : ℂ) ^ ρ)
          - (ρ * lagWindowZeroTerm ρ a₂ b₂ + (x : ℂ) ^ ρ) := by ring
  have hmain : ‖ρ‖ * ‖lagWindowZeroTerm ρ a₁ b₁ - lagWindowZeroTerm ρ a₂ b₂‖
      ≤ ‖ρ‖ * (2 * H * x ^ (ρ.re - 1)) := by
    rw [← norm_mul, hdiff]
    refine le_trans (norm_sub_le _ _) ?_
    have e1 : ‖ρ‖ * (b₁ - x) * x ^ (ρ.re - 1) ≤ ‖ρ‖ * H * x ^ (ρ.re - 1) := by
      gcongr
      linarith
    have e2 : ‖ρ‖ * (b₂ - x) * x ^ (ρ.re - 1) ≤ ‖ρ‖ * H * x ^ (ρ.re - 1) := by
      gcongr
      linarith
    nlinarith
  exact le_of_mul_le_mul_left hmain hρn

/-- **Long range.**  `|T(ρ; a, b)| ≤ (a^{β-1} + b^{β-1}) / (|ρ||1-ρ|(1/a - 1/b))`. -/
theorem norm_lagWindowZeroTerm_le {a b : ℝ} (ha : 0 < a) (hab : a < b) (ρ : ℂ) :
    ‖lagWindowZeroTerm ρ a b‖
      ≤ (a ^ (ρ.re - 1) + b ^ (ρ.re - 1)) / (‖ρ‖ * ‖1 - ρ‖ * (1 / a - 1 / b)) := by
  have hb : 0 < b := lt_trans ha hab
  have hw : 0 < 1 / a - 1 / b := by
    rw [sub_pos]
    exact one_div_lt_one_div_of_lt ha hab
  rw [lagWindowZeroTerm, norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hw]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  refine le_trans (norm_sub_le _ _) ?_
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hb, Complex.norm_cpow_eq_rpow_re_of_pos ha]
  simp only [Complex.sub_re, Complex.one_re]
  linarith

end

end RHTower
