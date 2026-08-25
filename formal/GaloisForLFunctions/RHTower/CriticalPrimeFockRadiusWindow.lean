import GaloisForLFunctions.RHTower.PrimeSamplingMicrolocalizationRate

/-!
# Critical-prime mass at a polynomial Fock radius

For the model adapted radius `rho_m(x) = (sqrt x) ^ (2 - m)`, the second-order logarithmic prime
window has the relative asymptotic

`primeLogWindowMass x (rho_m x) / (2 x rho_m x) -> 1`.

The exponential-rate Mertens remainder is essential: the qualitative additive `o(1)` window law
cannot be divided by `x rho_m(x)` when `m > 4`, since that main term tends to zero.
-/

open Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-- Exact power model for the positive-real adapted radius of the degree-`m` polynomial Fock
potential. -/
def criticalPrimeFockRadius (m x : ℝ) : ℝ :=
  (Real.sqrt x) ^ (2 - m)

theorem criticalPrimeFockRadius_pos {m x : ℝ} (hx : 0 < x) :
    0 < criticalPrimeFockRadius m x := by
  exact Real.rpow_pos_of_pos (Real.sqrt_pos.2 hx) _

/-- On the nonnegative ray, the square-root definition is exactly `x ^ (1 - m / 2)`. -/
theorem criticalPrimeFockRadius_eq_rpow {m x : ℝ} (hx : 0 ≤ x) :
    criticalPrimeFockRadius m x = x ^ (1 - m / 2) := by
  rw [criticalPrimeFockRadius, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  congr 1
  ring

theorem criticalPrimeFockRadius_le_one {m x : ℝ}
    (hm : 2 ≤ m) (hx : 1 ≤ x) :
    criticalPrimeFockRadius m x ≤ 1 := by
  have hs : 1 ≤ Real.sqrt x := Real.one_le_sqrt.2 hx
  rw [criticalPrimeFockRadius, show 2 - m = -(m - 2) by ring,
    Real.rpow_neg (Real.sqrt_nonneg x)]
  exact (inv_le_one₀ (Real.rpow_pos_of_pos
    (Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hx)) _)).2
    (Real.one_le_rpow hs (by linarith))

/-- A square-root exponential beats the reciprocal of every fixed polynomial Fock radius. -/
theorem tendsto_exp_neg_sqrt_div_criticalPrimeFockRadius
    {m c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ =>
      Real.exp (-c * Real.sqrt x) / criticalPrimeFockRadius m x)
      atTop (nhds 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (m - 2) c hc).comp
    Real.tendsto_sqrt_atTop
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  change (Real.sqrt x) ^ (m - 2) * Real.exp (-c * Real.sqrt x) =
    Real.exp (-c * Real.sqrt x) / (Real.sqrt x) ^ (2 - m)
  rw [div_eq_mul_inv, ← Real.rpow_neg (Real.sqrt_nonneg x)]
  ring_nf

/-- The same domination remains valid at the lower endpoint of the shrinking window. -/
theorem tendsto_exp_neg_sqrt_sub_radius_div_criticalPrimeFockRadius
    {m c : ℝ} (hm : 2 ≤ m) (hc : 0 < c) :
    Tendsto (fun x : ℝ =>
      Real.exp (-c * Real.sqrt (x - criticalPrimeFockRadius m x)) /
        criticalPrimeFockRadius m x)
      atTop (nhds 0) := by
  have hc' : 0 < c / Real.sqrt 2 := div_pos hc (Real.sqrt_pos.2 (by norm_num))
  have htop := tendsto_exp_neg_sqrt_div_criticalPrimeFockRadius (m := m) hc'
  have hnonneg : ∀ᶠ x : ℝ in atTop,
      0 ≤ Real.exp (-c * Real.sqrt (x - criticalPrimeFockRadius m x)) /
        criticalPrimeFockRadius m x := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact div_nonneg (Real.exp_pos _).le
      (criticalPrimeFockRadius_pos (lt_of_lt_of_le zero_lt_one hx)).le
  have hle : ∀ᶠ x : ℝ in atTop,
      Real.exp (-c * Real.sqrt (x - criticalPrimeFockRadius m x)) /
          criticalPrimeFockRadius m x ≤
        Real.exp (-(c / Real.sqrt 2) * Real.sqrt x) /
          criticalPrimeFockRadius m x := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hx1 : (1 : ℝ) ≤ x := by linarith
    have hr1 := criticalPrimeFockRadius_le_one hm hx1
    have hxhalf : x / 2 ≤ x - criticalPrimeFockRadius m x := by
      linarith
    have hsqrt : Real.sqrt x / Real.sqrt 2 ≤
        Real.sqrt (x - criticalPrimeFockRadius m x) := by
      rw [← Real.sqrt_div (by positivity : 0 ≤ x)]
      exact Real.sqrt_le_sqrt hxhalf
    have hexp : Real.exp (-c * Real.sqrt (x - criticalPrimeFockRadius m x)) ≤
        Real.exp (-(c / Real.sqrt 2) * Real.sqrt x) := by
      rw [Real.exp_le_exp]
      have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
      calc
        -c * Real.sqrt (x - criticalPrimeFockRadius m x)
            ≤ -c * (Real.sqrt x / Real.sqrt 2) := by nlinarith
        _ = -(c / Real.sqrt 2) * Real.sqrt x := by field_simp
    exact div_le_div_of_nonneg_right hexp
      (criticalPrimeFockRadius_pos (by linarith)).le
  exact squeeze_zero' hnonneg hle htop

/-- Relative prime-mass asymptotic at the shrinking polynomial Fock radius, with no lower bound on
the window width beyond its explicit polynomial form. -/
theorem tendsto_primeLogWindowMass_div_criticalPrimeFockModel
    {m : ℝ} (hm : 2 < m) :
    Tendsto (fun x : ℝ =>
      primeLogWindowMass x (criticalPrimeFockRadius m x) /
        (2 * x * criticalPrimeFockRadius m x))
      atTop (nhds 1) := by
  obtain ⟨B, c, Y, hc, hB, hY, hrem⟩ := exists_primeLogSquareRemainder_bound
  let r : ℝ → ℝ := criticalPrimeFockRadius m
  let err : ℝ → ℝ := fun x =>
    (primeLogSquareRemainder (x + r x) - primeLogSquareRemainder (x - r x)) /
      (2 * x * r x)
  have hmajor : Tendsto (fun x : ℝ =>
      2 * B * (Real.exp (-c * Real.sqrt (x - r x)) / r x))
      atTop (nhds 0) := by
    have hzero := tendsto_exp_neg_sqrt_sub_radius_div_criticalPrimeFockRadius
      (m := m) (le_of_lt hm) hc
    simpa [r] using hzero.const_mul (2 * B)
  have herr : Tendsto err atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _)
      _ hmajor
    filter_upwards [eventually_ge_atTop (max 2 (Y + 1))] with x hx
    have hx2 : (2 : ℝ) ≤ x := le_trans (le_max_left _ _) hx
    have hx1 : (1 : ℝ) ≤ x := by linarith
    have hrpos : 0 < r x := criticalPrimeFockRadius_pos (by linarith)
    have hr1 : r x ≤ 1 := criticalPrimeFockRadius_le_one (le_of_lt hm) hx1
    have hminusY : Y ≤ x - r x := by
      have := le_trans (le_max_right (2 : ℝ) (Y + 1)) hx
      linarith
    have hplusY : Y ≤ x + r x := by
      linarith
    have hminus := hrem (x - r x) hminusY
    have hplus := hrem (x + r x) hplusY
    have hminus_pos : 0 < x - r x :=
      lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hY) hminusY
    have hplus_nonneg : 0 ≤ x + r x := by positivity
    have hsqrt : Real.sqrt (x - r x) ≤ Real.sqrt (x + r x) := by
      exact Real.sqrt_le_sqrt (by linarith)
    have hexp : Real.exp (-c * Real.sqrt (x + r x)) ≤
        Real.exp (-c * Real.sqrt (x - r x)) := by
      rw [Real.exp_le_exp]
      nlinarith
    have hplus' : |primeLogSquareRemainder (x + r x)| ≤
        2 * B * x * Real.exp (-c * Real.sqrt (x - r x)) := by
      calc
        |primeLogSquareRemainder (x + r x)|
            ≤ B * (x + r x) * Real.exp (-c * Real.sqrt (x + r x)) := hplus
        _ ≤ B * (2 * x) * Real.exp (-c * Real.sqrt (x - r x)) := by
          gcongr <;> linarith
        _ = 2 * B * x * Real.exp (-c * Real.sqrt (x - r x)) := by ring
    have hminus' : |primeLogSquareRemainder (x - r x)| ≤
        B * x * Real.exp (-c * Real.sqrt (x - r x)) := by
      calc
        |primeLogSquareRemainder (x - r x)|
            ≤ B * (x - r x) * Real.exp (-c * Real.sqrt (x - r x)) := hminus
        _ ≤ B * x * Real.exp (-c * Real.sqrt (x - r x)) := by
          gcongr <;> linarith
    have hnum : |primeLogSquareRemainder (x + r x) -
        primeLogSquareRemainder (x - r x)| ≤
        4 * B * x * Real.exp (-c * Real.sqrt (x - r x)) := by
      calc
        |primeLogSquareRemainder (x + r x) - primeLogSquareRemainder (x - r x)|
            ≤ |primeLogSquareRemainder (x + r x)| +
                |primeLogSquareRemainder (x - r x)| := abs_sub _ _
        _ ≤ 2 * B * x * Real.exp (-c * Real.sqrt (x - r x)) +
              B * x * Real.exp (-c * Real.sqrt (x - r x)) := add_le_add hplus' hminus'
        _ ≤ 4 * B * x * Real.exp (-c * Real.sqrt (x - r x)) := by
          have ht : 0 ≤ B * x * Real.exp (-c * Real.sqrt (x - r x)) := by
            positivity
          nlinarith
    have hden : 0 < 2 * x * r x := by positivity
    dsimp [err]
    rw [abs_div, abs_of_pos hden]
    calc
      |primeLogSquareRemainder (x + r x) - primeLogSquareRemainder (x - r x)| /
            (2 * x * r x)
          ≤ (4 * B * x * Real.exp (-c * Real.sqrt (x - r x))) /
              (2 * x * r x) := div_le_div_of_nonneg_right hnum hden.le
      _ = 2 * B * (Real.exp (-c * Real.sqrt (x - r x)) / r x) := by
        field_simp
        <;> ring
  have hmain : ∀ᶠ x : ℝ in atTop,
      primeLogWindowMass x (r x) / (2 * x * r x) = 1 + err x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hrpos : 0 < r x := criticalPrimeFockRadius_pos hx
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
