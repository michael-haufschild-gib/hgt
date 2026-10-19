import GaloisForLFunctions.BiScaleUncertainty.EnergyControlledClosedCycleRecovery

/-!
# Quantitative decay of bounded-order closed-cycle ambiguity

For actual sources under a common singular-energy bound, matching cycles through
order n+2 forces equality on an interval of radius n times the energy collar.
On a fixed signed logarithmic-grid fibre, the global discrepancy has a weighted
square bound, hence an O(n^(-1/2)) diameter bound. No optimal rate is asserted.
-/

namespace GaloisForLFunctions.BiScaleUncertainty.EnergyCycle
noncomputable section
set_option autoImplicit false
variable {K : ℝ}

/-- Matching bounded-order closed products forces exact recovery on an
energy-controlled interval growing linearly with the observation order. -/
theorem equal_on_order_window (f g : LevyEnergySource K) (n : ℕ)
    (hcycles : ∀ l : List ℝ, l.length ≤ n + 2 → value f l = value g l)
    {x : ℝ} (hx : |x| ≤ (n : ℝ) * collarRadius K) :
    f.correlation x = g.correlation x := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hc := collar_pos K
  have hi : |x / ((n : ℝ) + 1)| < collarRadius K := by
    rw [abs_div, abs_of_pos hn]
    apply (div_lt_iff₀ hn).mpr
    nlinarith only [hx, hc]
  have hs := hcycles (spoke n x) (by rw [spoke_length])
  have hp := hcycles [x / ((n : ℝ) + 1), -(x / ((n : ℝ) + 1))] (by simp)
  have hr := correlation_recovery f g n x hi
  simp only [hs, hp, sub_self, abs_zero, mul_zero, add_zero] at hr
  have hl := le_abs_self (f.correlation x - g.correlation x)
  have hu := neg_le_abs (f.correlation x - g.correlation x)
  linarith only [hr, hl, hu]

/-- Equal signed logarithmic traces yield a global weighted square discrepancy bound. -/
theorem equal_grid_square_bound (f g : LevyEnergySource K)
    (hgrid : ∀ k : ℕ, f.correlation (Real.log k) = g.correlation (Real.log k)) (x : ℝ) :
    Real.exp (-(1 / 2 : ℝ)) * |x| * (f.correlation x - g.correlation x) ^ 2 ≤ 32 * K := by
  let c := Real.exp (-(1 / 2 : ℝ))
  let z := Real.log (logarithmicCeilNode |x| : ℝ)
  have hf := f.signed_sample_error_sq_le (abs_nonneg x)
  have hg := g.signed_sample_error_sq_le (abs_nonneg x)
  rw [f.correlation_abs] at hf
  rw [g.correlation_abs, ← hgrid (logarithmicCeilNode |x|)] at hg
  change c * |x| * (f.correlation x - f.correlation z) ^ 2 ≤ 8 * K at hf
  change c * |x| * (g.correlation x - f.correlation z) ^ 2 ≤ 8 * K at hg
  have hs : (f.correlation x - g.correlation x) ^ 2 ≤
      2 * ((f.correlation x - f.correlation z) ^ 2 +
        (g.correlation x - f.correlation z) ^ 2) := by
    nlinarith only [sq_nonneg ((f.correlation x - f.correlation z) +
      (g.correlation x - f.correlation z))]
  have hc : 0 ≤ c * |x| := mul_nonneg (Real.exp_pos _).le (abs_nonneg x)
  have hm := mul_le_mul_of_nonneg_left hs hc
  change c * |x| * (f.correlation x - g.correlation x) ^ 2 ≤ 32 * K
  nlinarith only [hf, hg, hm]

/-- Exact finite-order ambiguity on a fixed signed-grid fibre has diameter at
most a constant depending on K times n^(-1/2). No optimal-rate claim is made. -/
theorem order_ambiguity_square_bound (f g : LevyEnergySource K) (n : ℕ)
    (hcycles : ∀ l : List ℝ, l.length ≤ n + 2 → value f l = value g l)
    (hgrid : ∀ k : ℕ, f.correlation (Real.log k) = g.correlation (Real.log k)) (x : ℝ) :
    Real.exp (-(1 / 2 : ℝ)) * (n : ℝ) * collarRadius K *
      (f.correlation x - g.correlation x) ^ 2 ≤ 32 * max K 0 := by
  by_cases hx : |x| ≤ (n : ℝ) * collarRadius K
  · rw [equal_on_order_window f g n hcycles hx]
    simp only [sub_self, zero_pow (by omega : 2 ≠ 0), mul_zero]
    positivity
  · have ho : (n : ℝ) * collarRadius K ≤ |x| := le_of_not_ge hx
    have hc : 0 ≤ Real.exp (-(1 / 2 : ℝ)) := (Real.exp_pos _).le
    calc
      _ = (Real.exp (-(1 / 2 : ℝ)) * ((n : ℝ) * collarRadius K)) *
          (f.correlation x - g.correlation x) ^ 2 := by ring
      _ ≤ (Real.exp (-(1 / 2 : ℝ)) * |x|) *
          (f.correlation x - g.correlation x) ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ho hc) (sq_nonneg _)
      _ ≤ 32 * K := equal_grid_square_bound f g hgrid x
      _ ≤ 32 * max K 0 := mul_le_mul_of_nonneg_left (le_max_left K 0) (by norm_num)

end
end GaloisForLFunctions.BiScaleUncertainty.EnergyCycle
