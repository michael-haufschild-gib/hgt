import GaloisForLFunctions.RHTower.ChebyshevLagZeroWindowTerm

/-!
# A lower bound for `ψ(x + h) - ψ(x)` by a single absolutely convergent zero sum

For `1 < a < b` put `w = 1/a - 1/b`.  The genus-kernel explicit formula gives

`J(a, b)/w = L(a, b) + Re Σ_ρ T(ρ; a, b) - log 2π + (E(a)/a - E(b)/b)/w`,

with the logarithmic mean `L(a, b) = log(b/a)/w ∈ [a, b]` and the trivial-zero correction `E`.  The
squeeze `ψ(a) ≤ J(a,b)/w ≤ ψ(b)` on the right window `[x+h-h', x+h]` and the left window `[x, x+h']`
yields, for `2 ≤ x`, `0 < h'`, `2h' ≤ h ≤ x`,

`ψ(x+h) - ψ(x) ≥ h - 2h' - 4/(x h') - Σ_ρ |T(ρ; x+h-h', x+h) - T(ρ; x, x+h')|`,

and each summand is at most `2h · x^{β-1} · min(1, 8x²/(h h' |ρ||1-ρ|))`.
-/

namespace RHTower

noncomputable section

open Complex Finset

theorem summable_norm_inv_mul_one_sub :
    Summable (fun q : XiZeroCopy => ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) :=
  summable_norm_iff.mpr summable_inv_mul_one_sub

theorem norm_inv_mul_one_sub_eq (q : XiZeroCopy) :
    ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ = 1 / (‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖) := by
  rw [norm_div, norm_one, norm_mul]

/-- `X^{ρ-1}/(ρ(1-ρ))` is absolutely summable for `X ≥ 1`. -/
theorem norm_cpow_sub_one_div_le {X : ℝ} (hX : 1 ≤ X) (q : XiZeroCopy) :
    ‖(X : ℂ) ^ ((q.1 : ℂ) - 1) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖
      ≤ ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := by
  have hX0 : 0 < X := by linarith
  rw [div_eq_mul_one_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX0]
  have hle : X ^ (((q.1 : ℂ) - 1).re) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos hX ?_
    simp only [Complex.sub_re, Complex.one_re]
    linarith [xiZeroCopy_re_lt_one q]
  exact mul_le_of_le_one_left (norm_nonneg _) hle

theorem summable_cpow_sub_one_div {X : ℝ} (hX : 1 ≤ X) :
    Summable (fun q : XiZeroCopy => (X : ℂ) ^ ((q.1 : ℂ) - 1) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) :=
  Summable.of_norm_bounded summable_norm_inv_mul_one_sub (norm_cpow_sub_one_div_le hX)

theorem lagZeroSum_div_eq {X : ℝ} (hX : 1 ≤ X) :
    lagZeroSum X / X
      = ∑' q : XiZeroCopy, (X : ℂ) ^ ((q.1 : ℂ) - 1) / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) := by
  have hXC : (X : ℂ) ≠ 0 := by exact_mod_cast (by linarith : X ≠ 0)
  rw [lagZeroSum, ← tsum_div_const]
  refine tsum_congr fun q => ?_
  rw [Complex.cpow_sub _ _ hXC, Complex.cpow_one]
  ring

theorem norm_lagWindowZeroTerm_le_of_one_le {a b : ℝ} (ha : 1 ≤ a) (hab : a < b)
    (q : XiZeroCopy) :
    ‖lagWindowZeroTerm (q.1 : ℂ) a b‖
      ≤ 2 / (1 / a - 1 / b) * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := by
  have ha0 : 0 < a := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hw : 0 < 1 / a - 1 / b := by
    rw [sub_pos]
    exact one_div_lt_one_div_of_lt ha0 hab
  have hre : ((q.1 : ℂ)).re - 1 ≤ 0 := by linarith [xiZeroCopy_re_lt_one q]
  have h1 := Real.rpow_le_one_of_one_le_of_nonpos ha hre
  have h2 := Real.rpow_le_one_of_one_le_of_nonpos hb1 hre
  have hq0 : 0 < ‖(q.1 : ℂ)‖ := norm_pos_iff.mpr (xiZeroCopy_ne_zero q)
  have hq1 : 0 < ‖1 - (q.1 : ℂ)‖ := norm_pos_iff.mpr (xiZeroCopy_one_sub_ne_zero q)
  refine le_trans (norm_lagWindowZeroTerm_le ha0 hab _) ?_
  rw [norm_inv_mul_one_sub_eq]
  rw [div_le_iff₀ (by positivity)]
  have : (2 : ℝ) / (1 / a - 1 / b) * (1 / (‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖))
      * (‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖ * (1 / a - 1 / b)) = 2 := by
    have hwne : 1 / a - 1 / b ≠ 0 := hw.ne'
    generalize 1 / a - 1 / b = w at hwne ⊢
    field_simp
  rw [this]
  linarith

theorem summable_norm_lagWindowZeroTerm {a b : ℝ} (ha : 1 ≤ a) (hab : a < b) :
    Summable (fun q : XiZeroCopy => ‖lagWindowZeroTerm (q.1 : ℂ) a b‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_lagWindowZeroTerm_le_of_one_le ha hab)
    (summable_norm_inv_mul_one_sub.mul_left _)

/-- The zero sum of a window average. -/
theorem lagZeroSum_window_eq {a b : ℝ} (ha : 1 ≤ a) (hab : a < b) :
    lagZeroSum b / b - lagZeroSum a / a
      = ((1 / a - 1 / b : ℝ) : ℂ) * ∑' q : XiZeroCopy, lagWindowZeroTerm (q.1 : ℂ) a b := by
  have ha0 : 0 < a := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hw : 0 < 1 / a - 1 / b := by
    rw [sub_pos]
    exact one_div_lt_one_div_of_lt ha0 hab
  have hwC : ((1 / a - 1 / b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  rw [lagZeroSum_div_eq hb1, lagZeroSum_div_eq ha,
    ← (summable_cpow_sub_one_div hb1).tsum_sub (summable_cpow_sub_one_div ha), ← tsum_mul_left]
  refine tsum_congr fun q => ?_
  have hq0 := xiZeroCopy_ne_zero q
  have hq1 := xiZeroCopy_one_sub_ne_zero q
  rw [lagWindowZeroTerm]
  generalize ((1 / a - 1 / b : ℝ) : ℂ) = W at hwC ⊢
  field_simp

/-- **The window average.**  `J(a,b)/w = L(a,b) + Re Σ T - log 2π + (E(a)/a - E(b)/b)/w`. -/
theorem chebyshevLagWindow_div_eq {a b : ℝ} (ha : 1 < a) (hab : a < b) :
    chebyshevLagWindow a b / (1 / a - 1 / b)
      = Real.log (b / a) / (1 / a - 1 / b)
        + (∑' q : XiZeroCopy, lagWindowZeroTerm (q.1 : ℂ) a b).re - Real.log (2 * Real.pi)
        + (trivialZeroSeriesReal a / a - trivialZeroSeriesReal b / b) / (1 / a - 1 / b) := by
  have ha0 : 0 < a := by linarith
  have hw : 0 < 1 / a - 1 / b := by
    rw [sub_pos]
    exact one_div_lt_one_div_of_lt ha0 hab
  rw [chebyshevLagWindow_eq ha hab.le, lagZeroSum_window_eq ha.le hab, Complex.re_ofReal_mul,
    show 1 / b - 1 / a = -(1 / a - 1 / b) by ring]
  generalize 1 / a - 1 / b = W at hw ⊢
  field_simp
  ring

/-- The logarithmic mean lies in `[a, b]`. -/
theorem log_div_le_mul_inv_sub {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    a * (1 / a - 1 / b) ≤ Real.log (b / a) ∧ Real.log (b / a) ≤ b * (1 / a - 1 / b) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hba : 0 < b / a := div_pos hb ha
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos hba
    have : a * (1 / a - 1 / b) = 1 - (b / a)⁻¹ := by
      field_simp
    linarith
  · have h := Real.log_le_sub_one_of_pos hba
    have : b * (1 / a - 1 / b) = b / a - 1 := by
      field_simp
    linarith

theorem trivialZeroSeriesReal_div_anti {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    trivialZeroSeriesReal b / b ≤ trivialZeroSeriesReal a / a := by
  have ha0 : 0 < a := by linarith
  have hE := trivialZeroSeriesReal_anti ha hab
  have hE0 := trivialZeroSeriesReal_nonneg (ha.trans hab)
  calc trivialZeroSeriesReal b / b ≤ trivialZeroSeriesReal a / b :=
        div_le_div_of_nonneg_right hE (by linarith)
    _ ≤ trivialZeroSeriesReal a / a :=
        div_le_div_of_nonneg_left (trivialZeroSeriesReal_nonneg ha) ha0 hab

/-- **The `ψ` window lower bound.** -/
theorem psi_window_ge_sub_tsum {x h h' : ℝ} (hx : 2 ≤ x) (hh' : 0 < h') (hh'h : 2 * h' ≤ h)
    (hhx : h ≤ x) :
    h - 2 * h' - 4 / (x * h')
        - ∑' q : XiZeroCopy, ‖lagWindowZeroTerm (q.1 : ℂ) (x + h - h') (x + h)
            - lagWindowZeroTerm (q.1 : ℂ) x (x + h')‖
      ≤ Chebyshev.psi (x + h) - Chebyshev.psi x := by
  set a₁ := x + h - h' with ha₁
  set b₁ := x + h with hb₁
  set b₂ := x + h' with hb₂
  have hx1 : 1 < x := by linarith
  have ha₁1 : 1 < a₁ := by rw [ha₁]; linarith
  have hab₁ : a₁ < b₁ := by rw [ha₁, hb₁]; linarith
  have hab₂ : x < b₂ := by rw [hb₂]; linarith
  have ha₁0 : 0 < a₁ := by linarith
  have hx0 : 0 < x := by linarith
  have hw₁ : 0 < 1 / a₁ - 1 / b₁ := by
    rw [sub_pos]
    exact one_div_lt_one_div_of_lt ha₁0 hab₁
  have hw₂ : 0 < 1 / x - 1 / b₂ := by
    rw [sub_pos]
    exact one_div_lt_one_div_of_lt hx0 hab₂
  -- the squeeze
  have hsq₁ := (chebyshevLagWindow_bounds ha₁0 hab₁.le).2
  have hsq₂ := (chebyshevLagWindow_bounds hx0 hab₂.le).1
  have hψ₁ : chebyshevLagWindow a₁ b₁ / (1 / a₁ - 1 / b₁) ≤ Chebyshev.psi b₁ := by
    rw [div_le_iff₀ hw₁]
    exact hsq₁
  have hψ₂ : Chebyshev.psi x ≤ chebyshevLagWindow x b₂ / (1 / x - 1 / b₂) := by
    rw [le_div_iff₀ hw₂]
    exact hsq₂
  rw [chebyshevLagWindow_div_eq ha₁1 hab₁] at hψ₁
  rw [chebyshevLagWindow_div_eq hx1 hab₂] at hψ₂
  -- logarithmic means
  have hL₁ : a₁ ≤ Real.log (b₁ / a₁) / (1 / a₁ - 1 / b₁) := by
    rw [le_div_iff₀ hw₁]
    exact (log_div_le_mul_inv_sub ha₁0 hab₁.le).1
  have hL₂ : Real.log (b₂ / x) / (1 / x - 1 / b₂) ≤ b₂ := by
    rw [div_le_iff₀ hw₂]
    exact (log_div_le_mul_inv_sub hx0 hab₂.le).2
  -- trivial zeros
  have hE₁ : 0 ≤ (trivialZeroSeriesReal a₁ / a₁ - trivialZeroSeriesReal b₁ / b₁)
      / (1 / a₁ - 1 / b₁) :=
    div_nonneg (sub_nonneg.mpr (trivialZeroSeriesReal_div_anti ha₁1.le hab₁.le)) hw₁.le
  have hE₂ : (trivialZeroSeriesReal x / x - trivialZeroSeriesReal b₂ / b₂) / (1 / x - 1 / b₂)
      ≤ 4 / (x * h') := by
    have hEb := trivialZeroSeriesReal_nonneg (hx1.le.trans hab₂.le)
    have hEx := trivialZeroSeriesReal_le_two_div_sq hx
    have hb₂0 : 0 < b₂ := by linarith
    have hnum : trivialZeroSeriesReal x / x - trivialZeroSeriesReal b₂ / b₂ ≤ 2 / x ^ 2 / x := by
      have : 0 ≤ trivialZeroSeriesReal b₂ / b₂ := div_nonneg hEb hb₂0.le
      have : trivialZeroSeriesReal x / x ≤ 2 / x ^ 2 / x :=
        div_le_div_of_nonneg_right hEx hx0.le
      linarith
    have hweq : 1 / x - 1 / b₂ = h' / (x * b₂) := by
      rw [hb₂]
      field_simp
      ring
    rw [div_le_iff₀ hw₂, hweq]
    refine le_trans hnum ?_
    have hh'x : h' ≤ x := by linarith
    rw [show 4 / (x * h') * (h' / (x * b₂)) = 4 / (x ^ 2 * b₂) by field_simp, div_div,
      div_le_div_iff₀ (by positivity) (by positivity)]
    rw [hb₂]
    nlinarith
  -- the zero sums
  have hs₁ := summable_norm_lagWindowZeroTerm ha₁1.le hab₁
  have hs₂ := summable_norm_lagWindowZeroTerm hx1.le hab₂
  have hsd : Summable (fun q : XiZeroCopy => ‖lagWindowZeroTerm (q.1 : ℂ) a₁ b₁
      - lagWindowZeroTerm (q.1 : ℂ) x b₂‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_sub_le _ _) (hs₁.add hs₂)
  have hdiff : (∑' q : XiZeroCopy, lagWindowZeroTerm (q.1 : ℂ) a₁ b₁).re
      - (∑' q : XiZeroCopy, lagWindowZeroTerm (q.1 : ℂ) x b₂).re
      ≥ -∑' q : XiZeroCopy, ‖lagWindowZeroTerm (q.1 : ℂ) a₁ b₁
          - lagWindowZeroTerm (q.1 : ℂ) x b₂‖ := by
    rw [← Complex.sub_re, ← (Summable.of_norm hs₁).tsum_sub (Summable.of_norm hs₂)]
    have h1 := Complex.abs_re_le_norm (∑' q : XiZeroCopy, (lagWindowZeroTerm (q.1 : ℂ) a₁ b₁
      - lagWindowZeroTerm (q.1 : ℂ) x b₂))
    have h2 := norm_tsum_le_tsum_norm hsd
    have h3 := neg_abs_le (∑' q : XiZeroCopy, (lagWindowZeroTerm (q.1 : ℂ) a₁ b₁
      - lagWindowZeroTerm (q.1 : ℂ) x b₂)).re
    linarith
  have hab : a₁ - b₂ = h - 2 * h' := by rw [ha₁, hb₂]; ring
  linarith

/-- The zero weight `x^{β-1} min(1, Y/(|ρ||1-ρ|))`. -/
def zeroShortWeight (x Y : ℝ) (ρ : ℂ) : ℝ :=
  x ^ (ρ.re - 1) * min 1 (Y / (‖ρ‖ * ‖1 - ρ‖))

theorem zeroShortWeight_nonneg {x : ℝ} (hx : 0 ≤ x) {Y : ℝ} (hY : 0 ≤ Y) (ρ : ℂ) :
    0 ≤ zeroShortWeight x Y ρ :=
  mul_nonneg (Real.rpow_nonneg hx _) (le_min zero_le_one (by positivity))

theorem zeroShortWeight_le {x : ℝ} (hx : 1 ≤ x) {Y : ℝ} (hY : 0 ≤ Y) (q : XiZeroCopy) :
    zeroShortWeight x Y (q.1 : ℂ) ≤ Y * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := by
  rw [zeroShortWeight, norm_inv_mul_one_sub_eq]
  have hle : x ^ (((q.1 : ℂ)).re - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith [xiZeroCopy_re_lt_one q])
  have hm : min 1 (Y / (‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖)) ≤ Y * (1 / (‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖)) := by
    rw [mul_one_div]
    exact min_le_right _ _
  have hm0 : 0 ≤ min 1 (Y / (‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖)) := le_min zero_le_one (by positivity)
  calc x ^ (((q.1 : ℂ)).re - 1) * min 1 (Y / (‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖))
      ≤ 1 * min 1 (Y / (‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖)) :=
        mul_le_mul_of_nonneg_right hle hm0
    _ ≤ Y * (1 / (‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖)) := by rw [one_mul]; exact hm

theorem summable_zeroShortWeight {x : ℝ} (hx : 1 ≤ x) {Y : ℝ} (hY : 0 ≤ Y) :
    Summable (fun q : XiZeroCopy => zeroShortWeight x Y (q.1 : ℂ)) :=
  Summable.of_nonneg_of_le (fun _ => zeroShortWeight_nonneg (by linarith) hY _)
    (zeroShortWeight_le hx hY) (summable_norm_inv_mul_one_sub.mul_left _)

/-- **The per-zero majorant.** -/
theorem norm_window_diff_le_zeroShortWeight {x h h' : ℝ} (hx : 2 ≤ x) (hh' : 0 < h')
    (hh'h : 2 * h' ≤ h) (hhx : h ≤ x) (q : XiZeroCopy) :
    ‖lagWindowZeroTerm (q.1 : ℂ) (x + h - h') (x + h) - lagWindowZeroTerm (q.1 : ℂ) x (x + h')‖
      ≤ 2 * h * zeroShortWeight x (8 * x ^ 2 / (h * h')) (q.1 : ℂ) := by
  have hx0 : 0 < x := by linarith
  have hh : 0 < h := by linarith
  have hρ0 := xiZeroCopy_re_pos q
  have hρ1 := xiZeroCopy_re_lt_one q
  set β := ((q.1 : ℂ)).re with hβ
  set N := ‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖ with hN
  have hN0 : 0 < N := mul_pos (norm_pos_iff.mpr (xiZeroCopy_ne_zero q))
    (norm_pos_iff.mpr (xiZeroCopy_one_sub_ne_zero q))
  have hxβ : 0 ≤ x ^ (β - 1) := Real.rpow_nonneg hx0.le _
  -- short range
  have hshort : ‖lagWindowZeroTerm (q.1 : ℂ) (x + h - h') (x + h)
      - lagWindowZeroTerm (q.1 : ℂ) x (x + h')‖ ≤ 2 * h * x ^ (β - 1) :=
    norm_lagWindowZeroTerm_sub_le hx0 (by linarith) (by linarith) le_rfl le_rfl (by linarith)
      (by linarith) hρ0 hρ1
  -- long range, one window at a time
  have hlong : ∀ a b : ℝ, x ≤ a → b - a = h' → b ≤ 2 * x →
      ‖lagWindowZeroTerm (q.1 : ℂ) a b‖ ≤ 8 * x ^ (β - 1) * x ^ 2 / (h' * N) := by
    intro a b hxa hba hb2
    have ha0 : 0 < a := by linarith
    have hab : a < b := by linarith
    have hb0 : 0 < b := by linarith
    have hpa : a ^ (β - 1) ≤ x ^ (β - 1) := Real.rpow_le_rpow_of_nonpos hx0 hxa (by linarith)
    have hpb : b ^ (β - 1) ≤ x ^ (β - 1) :=
      Real.rpow_le_rpow_of_nonpos hx0 (by linarith) (by linarith)
    have hweq : 1 / a - 1 / b = h' / (a * b) := by
      rw [← hba]
      field_simp
    refine le_trans (norm_lagWindowZeroTerm_le ha0 hab _) ?_
    rw [← hβ, ← hN, hweq]
    have hab4 : a * b ≤ 4 * x ^ 2 := by nlinarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hsum : a ^ (β - 1) + b ^ (β - 1) ≤ 2 * x ^ (β - 1) := by linarith
    have e1 : (a ^ (β - 1) + b ^ (β - 1)) * (h' * N) ≤ 2 * x ^ (β - 1) * (h' * N) :=
      mul_le_mul_of_nonneg_right hsum (by positivity)
    have e2 : 8 * x ^ (β - 1) * x ^ 2 * (N * (h' / (a * b)))
        = 2 * x ^ (β - 1) * (h' * N) * (4 * x ^ 2 / (a * b)) := by
      field_simp
      ring
    have e3 : 1 ≤ 4 * x ^ 2 / (a * b) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    rw [e2]
    calc (a ^ (β - 1) + b ^ (β - 1)) * (h' * N) ≤ 2 * x ^ (β - 1) * (h' * N) := e1
      _ = 2 * x ^ (β - 1) * (h' * N) * 1 := by ring
      _ ≤ 2 * x ^ (β - 1) * (h' * N) * (4 * x ^ 2 / (a * b)) :=
          mul_le_mul_of_nonneg_left e3 (by positivity)
  have h1 := hlong (x + h - h') (x + h) (by linarith) (by ring) (by linarith)
  have h2 := hlong x (x + h') le_rfl (by ring) (by linarith)
  have hlong2 : ‖lagWindowZeroTerm (q.1 : ℂ) (x + h - h') (x + h)
      - lagWindowZeroTerm (q.1 : ℂ) x (x + h')‖ ≤ 16 * x ^ (β - 1) * x ^ 2 / (h' * N) := by
    refine le_trans (norm_sub_le _ _) ?_
    have : 16 * x ^ (β - 1) * x ^ 2 / (h' * N)
        = 8 * x ^ (β - 1) * x ^ 2 / (h' * N) + 8 * x ^ (β - 1) * x ^ 2 / (h' * N) := by ring
    rw [this]
    exact add_le_add h1 h2
  rw [zeroShortWeight, ← hβ, ← hN, ← mul_assoc, mul_min_of_nonneg _ _ (by positivity), mul_one]
  refine le_min hshort (le_of_le_of_eq hlong2 ?_)
  field_simp
  ring

/-- **The `ψ` window lower bound, weighted form.** -/
theorem psi_window_ge_sub_zeroShortWeight {x h h' : ℝ} (hx : 2 ≤ x) (hh' : 0 < h')
    (hh'h : 2 * h' ≤ h) (hhx : h ≤ x) :
    h - 2 * h' - 4 / (x * h')
        - 2 * h * ∑' q : XiZeroCopy, zeroShortWeight x (8 * x ^ 2 / (h * h')) (q.1 : ℂ)
      ≤ Chebyshev.psi (x + h) - Chebyshev.psi x := by
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hh : 0 < h := by linarith
  have hY : (0 : ℝ) ≤ 8 * x ^ 2 / (h * h') := by positivity
  have hmain := psi_window_ge_sub_tsum hx hh' hh'h hhx
  have hs₁ := summable_norm_lagWindowZeroTerm (a := x + h - h') (b := x + h) (by linarith)
    (by linarith)
  have hs₂ := summable_norm_lagWindowZeroTerm (a := x) (b := x + h') hx1 (by linarith)
  have hsd : Summable (fun q : XiZeroCopy => ‖lagWindowZeroTerm (q.1 : ℂ) (x + h - h') (x + h)
      - lagWindowZeroTerm (q.1 : ℂ) x (x + h')‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_sub_le _ _) (hs₁.add hs₂)
  have hcmp : ∑' q : XiZeroCopy, ‖lagWindowZeroTerm (q.1 : ℂ) (x + h - h') (x + h)
      - lagWindowZeroTerm (q.1 : ℂ) x (x + h')‖
      ≤ 2 * h * ∑' q : XiZeroCopy, zeroShortWeight x (8 * x ^ 2 / (h * h')) (q.1 : ℂ) := by
    rw [← tsum_mul_left]
    exact hsd.tsum_le_tsum (norm_window_diff_le_zeroShortWeight hx hh' hh'h hhx)
      ((summable_zeroShortWeight hx1 hY).mul_left _)
  linarith

end

end RHTower
