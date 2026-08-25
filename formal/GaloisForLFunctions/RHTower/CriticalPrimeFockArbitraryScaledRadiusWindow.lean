import GaloisForLFunctions.RHTower.CriticalPrimeFockScaledRadiusWindow
import GaloisForLFunctions.RHTower.PolynomialFockPrimeBallOverlap

open Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

theorem tendsto_exp_neg_sqrt_sub_scaled_radius_div_criticalPrimeFockRadius_of_pos
    {m a s : ℝ} (hm : 2 ≤ m) (ha : 0 < a) (hs : 0 < s) :
    Tendsto (fun x : ℝ =>
      Real.exp (-a * Real.sqrt (x - s * criticalPrimeFockRadius m x)) /
        (s * criticalPrimeFockRadius m x))
      atTop (nhds 0) := by
  have ha2 : 0 < a / 2 := by positivity
  have hzero := tendsto_exp_neg_sqrt_sub_radius_div_criticalPrimeFockRadius
    (m := m) hm ha2
  have hmajor := hzero.const_mul s⁻¹
  have hrevent : ∀ᶠ x : ℝ in atTop, criticalPrimeFockRadius m x ≤ 1 := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact criticalPrimeFockRadius_le_one hm hx
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
          (Real.exp (-(a / 2) * Real.sqrt (x - criticalPrimeFockRadius m x)) /
            criticalPrimeFockRadius m x) := by
    filter_upwards [eventually_ge_atTop (max 2 (2 * s)), hrevent] with x hx hr1
    have hx2 : 2 ≤ x := le_trans (le_max_left _ _) hx
    have hxs : 2 * s ≤ x := le_trans (le_max_right _ _) hx
    have hx0 : 0 < x := by linarith
    have hrpos : 0 < criticalPrimeFockRadius m x := criticalPrimeFockRadius_pos hx0
    have hsr : s * criticalPrimeFockRadius m x ≤ x / 2 := by
      calc
        s * criticalPrimeFockRadius m x ≤ s * 1 := mul_le_mul_of_nonneg_left hr1 hs.le
        _ ≤ x / 2 := by linarith
    have hbase0 : 0 ≤ x - criticalPrimeFockRadius m x := by linarith
    have hscaled0 : 0 ≤ x - s * criticalPrimeFockRadius m x := by linarith
    have harg : (x - criticalPrimeFockRadius m x) / 4 ≤
        x - s * criticalPrimeFockRadius m x := by linarith
    have hsqrt0 := Real.sqrt_le_sqrt harg
    have hsqrt : (1 / 2 : ℝ) * Real.sqrt (x - criticalPrimeFockRadius m x) ≤
        Real.sqrt (x - s * criticalPrimeFockRadius m x) := by
      rw [Real.sqrt_div hbase0 4] at hsqrt0
      norm_num at hsqrt0 ⊢
      simpa [div_eq_mul_inv, mul_comm] using hsqrt0
    have hexp : Real.exp (-a * Real.sqrt (x - s * criticalPrimeFockRadius m x)) ≤
        Real.exp (-(a / 2) * Real.sqrt (x - criticalPrimeFockRadius m x)) := by
      rw [Real.exp_le_exp]
      nlinarith
    calc
      Real.exp (-a * Real.sqrt (x - s * criticalPrimeFockRadius m x)) /
          (s * criticalPrimeFockRadius m x)
          ≤ Real.exp (-(a / 2) * Real.sqrt (x - criticalPrimeFockRadius m x)) /
              (s * criticalPrimeFockRadius m x) :=
            div_le_div_of_nonneg_right hexp (mul_pos hs hrpos).le
      _ = s⁻¹ *
          (Real.exp (-(a / 2) * Real.sqrt (x - criticalPrimeFockRadius m x)) /
            criticalPrimeFockRadius m x) := by field_simp
  exact squeeze_zero' hnonneg hle (by simpa using hmajor)

theorem tendsto_primeLogWindowMass_div_scaledCriticalPrimeFockModel_of_pos
    {m s : ℝ} (hm : 2 < m) (hs : 0 < s) :
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
      tendsto_exp_neg_sqrt_sub_scaled_radius_div_criticalPrimeFockRadius_of_pos
        (m := m) (a := a) (s := s) (le_of_lt hm) ha hs
    simpa [r] using hzero.const_mul (2 * B)
  have hrzero : Tendsto r atTop (nhds 0) := by
    simpa [r] using (tendsto_criticalPrimeFockRadius_zero hm).const_mul s
  have hrone : ∀ᶠ x : ℝ in atTop, r x ≤ 1 := by
    filter_upwards [hrzero.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with x hx
    exact hx.le
  have herr : Tendsto err atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) _ hmajor
    filter_upwards [eventually_ge_atTop (max 2 (Y + 1)), hrone] with x hx hr1
    have hx2 : (2 : ℝ) ≤ x := le_trans (le_max_left _ _) hx
    have hrho_pos : 0 < criticalPrimeFockRadius m x :=
      criticalPrimeFockRadius_pos (by linarith)
    have hrpos : 0 < r x := mul_pos hs hrho_pos
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
