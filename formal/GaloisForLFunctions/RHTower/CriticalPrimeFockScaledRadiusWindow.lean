import GaloisForLFunctions.RHTower.CriticalPrimeFockRadiusWindow

/-!
# Prime mass in scaled polynomial-Fock radius windows (scales `0 < s ≤ 1`)

For the degree-`m` polynomial Fock potential the adapted radius at `x > 0` is
`r(x) = (√x)^(2 - m)`. This module studies the prime-log mass
`∑_{e^(x-sr) < p ≤ e^(x+sr)} (log p)²/p` of the window of radius `s·r(x)` around `x`, for a scale
`0 < s ≤ 1`. Using the unconditional remainder bound for `∑_{p ≤ e^y} (log p)²/p`, with error
`O(y e^(-c√y))`, it shows that this mass is asymptotic to the main term `2x · s r(x)` as
`x → ∞`, for every `m > 2`.

## Main results

- `tendsto_exp_neg_sqrt_sub_scaled_radius_div_criticalPrimeFockRadius`: for `m ≥ 2`, `a > 0`,
  `e^(-a√(x - s r(x))) / (s r(x)) → 0` as `x → ∞`.
- `tendsto_primeLogWindowMass_div_scaledCriticalPrimeFockModel`: for `m > 2`, the window mass
  divided by `2x · s r(x)` tends to `1`.

## Hypotheses

Unconditional. The premises are the parameter ranges `m > 2` (or `m ≥ 2`), `a > 0` and
`0 < s ≤ 1`; the prime-sum remainder bound is the proved `exists_primeLogSquareRemainder_bound`.
-/

open Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-- For `m ≥ 2`, `a > 0` and `0 < s ≤ 1`, the error ratio `e^(-a√(x - s r(x))) / (s r(x))` tends to `0`
as `x → ∞`, where `r(x) = (√x)^(2 - m)` is the Fock radius. -/
theorem tendsto_exp_neg_sqrt_sub_scaled_radius_div_criticalPrimeFockRadius
    {m a s : ℝ} (hm : 2 ≤ m) (ha : 0 < a) (hs : 0 < s) (hs1 : s ≤ 1) :
    Tendsto (fun x : ℝ =>
      Real.exp (-a * Real.sqrt (x - s * criticalPrimeFockRadius m x)) /
        (s * criticalPrimeFockRadius m x))
      atTop (nhds 0) := by
  have hzero := tendsto_exp_neg_sqrt_sub_radius_div_criticalPrimeFockRadius
    (m := m) hm ha
  have hmajor := hzero.const_mul s⁻¹
  have hnonneg : ∀ᶠ x : ℝ in atTop,
      0 ≤ Real.exp (-a * Real.sqrt (x - s * criticalPrimeFockRadius m x)) /
        (s * criticalPrimeFockRadius m x) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact div_nonneg (Real.exp_pos _).le
      (mul_nonneg hs.le
        (criticalPrimeFockRadius_pos (lt_of_lt_of_le zero_lt_one hx)).le)
  have hle : ∀ᶠ x : ℝ in atTop,
      Real.exp (-a * Real.sqrt (x - s * criticalPrimeFockRadius m x)) /
          (s * criticalPrimeFockRadius m x) ≤
        s⁻¹ *
          (Real.exp (-a * Real.sqrt (x - criticalPrimeFockRadius m x)) /
            criticalPrimeFockRadius m x) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hrpos : 0 < criticalPrimeFockRadius m x :=
      criticalPrimeFockRadius_pos hx0
    have harg : x - criticalPrimeFockRadius m x ≤
        x - s * criticalPrimeFockRadius m x := by
      nlinarith
    have hexp : Real.exp (-a * Real.sqrt (x - s * criticalPrimeFockRadius m x)) ≤
        Real.exp (-a * Real.sqrt (x - criticalPrimeFockRadius m x)) := by
      rw [Real.exp_le_exp]
      have hsqrt := Real.sqrt_le_sqrt harg
      nlinarith
    calc
      Real.exp (-a * Real.sqrt (x - s * criticalPrimeFockRadius m x)) /
          (s * criticalPrimeFockRadius m x)
          ≤ Real.exp (-a * Real.sqrt (x - criticalPrimeFockRadius m x)) /
              (s * criticalPrimeFockRadius m x) :=
            div_le_div_of_nonneg_right hexp (mul_pos hs hrpos).le
      _ = s⁻¹ *
          (Real.exp (-a * Real.sqrt (x - criticalPrimeFockRadius m x)) /
            criticalPrimeFockRadius m x) := by
            field_simp
  exact squeeze_zero' hnonneg hle (by simpa using hmajor)

/-- For `m > 2` and `0 < s ≤ 1`, the prime-log mass `∑ (log p)²/p` over `e^(x - s r(x)) < p ≤ e^(x + s r(x))`
is asymptotic to `2x · s r(x)` as `x → ∞`. -/
theorem tendsto_primeLogWindowMass_div_scaledCriticalPrimeFockModel
    {m s : ℝ} (hm : 2 < m) (hs : 0 < s) (hs1 : s ≤ 1) :
    Tendsto (fun x : ℝ =>
      primeLogWindowMass x (s * criticalPrimeFockRadius m x) /
        (2 * x * (s * criticalPrimeFockRadius m x)))
      atTop (nhds 1) := by
  obtain ⟨B, a, Y, ha, hB, hY, hrem⟩ := exists_primeLogSquareRemainder_bound
  let r : ℝ → ℝ := fun x => s * criticalPrimeFockRadius m x
  let err : ℝ → ℝ := fun x =>
    (primeLogSquareRemainder (x + r x) - primeLogSquareRemainder (x - r x)) /
      (2 * x * r x)
  have hmajor : Tendsto (fun x : ℝ =>
      2 * B * (Real.exp (-a * Real.sqrt (x - r x)) / r x))
      atTop (nhds 0) := by
    have hzero :=
      tendsto_exp_neg_sqrt_sub_scaled_radius_div_criticalPrimeFockRadius
        (m := m) (a := a) (s := s) (le_of_lt hm) ha hs hs1
    simpa [r] using hzero.const_mul (2 * B)
  have herr : Tendsto err atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) _ hmajor
    filter_upwards [eventually_ge_atTop (max 2 (Y + 1))] with x hx
    have hx2 : (2 : ℝ) ≤ x := le_trans (le_max_left _ _) hx
    have hx1 : (1 : ℝ) ≤ x := by linarith
    have hrho_pos : 0 < criticalPrimeFockRadius m x :=
      criticalPrimeFockRadius_pos (by linarith)
    have hrpos : 0 < r x := mul_pos hs hrho_pos
    have hr1 : r x ≤ 1 := by
      dsimp [r]
      calc
        s * criticalPrimeFockRadius m x ≤ 1 * criticalPrimeFockRadius m x := by
          gcongr
        _ ≤ 1 := by
          simpa using criticalPrimeFockRadius_le_one (m := m) (x := x) (le_of_lt hm) hx1
    have hminusY : Y ≤ x - r x := by
      have := le_trans (le_max_right (2 : ℝ) (Y + 1)) hx
      linarith
    have hplusY : Y ≤ x + r x := by linarith
    have hminus := hrem (x - r x) hminusY
    have hplus := hrem (x + r x) hplusY
    have hminus_pos : 0 < x - r x :=
      lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hY) hminusY
    have hplus_nonneg : 0 ≤ x + r x := by positivity
    have hsqrt : Real.sqrt (x - r x) ≤ Real.sqrt (x + r x) :=
      Real.sqrt_le_sqrt (by linarith)
    have hexp : Real.exp (-a * Real.sqrt (x + r x)) ≤
        Real.exp (-a * Real.sqrt (x - r x)) := by
      rw [Real.exp_le_exp]
      nlinarith
    have hplus' : |primeLogSquareRemainder (x + r x)| ≤
        2 * B * x * Real.exp (-a * Real.sqrt (x - r x)) := by
      calc
        |primeLogSquareRemainder (x + r x)|
            ≤ B * (x + r x) * Real.exp (-a * Real.sqrt (x + r x)) := hplus
        _ ≤ B * (2 * x) * Real.exp (-a * Real.sqrt (x - r x)) := by
          gcongr <;> linarith
        _ = 2 * B * x * Real.exp (-a * Real.sqrt (x - r x)) := by ring
    have hminus' : |primeLogSquareRemainder (x - r x)| ≤
        B * x * Real.exp (-a * Real.sqrt (x - r x)) := by
      calc
        |primeLogSquareRemainder (x - r x)|
            ≤ B * (x - r x) * Real.exp (-a * Real.sqrt (x - r x)) := hminus
        _ ≤ B * x * Real.exp (-a * Real.sqrt (x - r x)) := by
          gcongr <;> linarith
    have hnum : |primeLogSquareRemainder (x + r x) -
        primeLogSquareRemainder (x - r x)| ≤
        4 * B * x * Real.exp (-a * Real.sqrt (x - r x)) := by
      calc
        |primeLogSquareRemainder (x + r x) - primeLogSquareRemainder (x - r x)|
            ≤ |primeLogSquareRemainder (x + r x)| +
                |primeLogSquareRemainder (x - r x)| := abs_sub _ _
        _ ≤ 2 * B * x * Real.exp (-a * Real.sqrt (x - r x)) +
              B * x * Real.exp (-a * Real.sqrt (x - r x)) :=
            add_le_add hplus' hminus'
        _ ≤ 4 * B * x * Real.exp (-a * Real.sqrt (x - r x)) := by
          have ht : 0 ≤ B * x * Real.exp (-a * Real.sqrt (x - r x)) := by
            positivity
          nlinarith
    have hden : 0 < 2 * x * r x := by positivity
    dsimp [err]
    rw [abs_div, abs_of_pos hden]
    calc
      |primeLogSquareRemainder (x + r x) - primeLogSquareRemainder (x - r x)| /
            (2 * x * r x)
          ≤ (4 * B * x * Real.exp (-a * Real.sqrt (x - r x))) /
              (2 * x * r x) := div_le_div_of_nonneg_right hnum hden.le
      _ = 2 * B * (Real.exp (-a * Real.sqrt (x - r x)) / r x) := by
        field_simp
        ring
  have hmain : ∀ᶠ x : ℝ in atTop,
      primeLogWindowMass x (r x) / (2 * x * r x) = 1 + err x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hrpos : 0 < r x := mul_pos hs (criticalPrimeFockRadius_pos hx)
    rw [primeLogWindowMass_eq_main_add_remainders]
    dsimp [err]
    field_simp
    ring
  have hsum : Tendsto (fun x : ℝ => 1 + err x) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.add herr)
  apply hsum.congr'
  filter_upwards [hmain] with x hx
  exact hx.symm

end

end RHTower

