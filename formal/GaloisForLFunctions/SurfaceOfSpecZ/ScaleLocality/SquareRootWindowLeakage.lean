import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.PositiveTailIsolation

/-!
# Exponentially small leakage from square-root windows

For every positive window coefficient `r`, deletion with square cost at
most `r²/(16(D+1))` transfers a local lower bound near height `T` with
error at most a constant times `exp(-T)`. The estimate is uniform over
any fixed bounded displacement of the center.
-/

open Complex Filter Topology
noncomputable section
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- Square-cost allowance for a window of radius proportional to `r√T`. -/
def windowSquareBudget (D r : ℝ) : ℝ := r ^ 2 / (16 * (D + 1))

theorem windowSquareBudget_pos {D r : ℝ} (hD : 0 ≤ D) (hr : 0 < r) :
    0 < windowSquareBudget D r := by
  unfold windowSquareBudget
  positivity

private theorem gaussian_squareRoot_exponent_le {D r V B T t : ℝ}
    (hD : 0 ≤ D) (hr : 0 < r) (hcost : V ≤ windowSquareBudget D r)
    (hT : 0 ≤ T) (ht : |t| ≤ T + B) :
    D * |t| - (4 * (D + 1) / r * Real.sqrt T) * (r * Real.sqrt T / 2) +
        (D + 4 * (D + 1) / r * Real.sqrt T) ^ 2 * V / 2 ≤
      D * B + D ^ 2 * windowSquareBudget D r - T := by
  let q : ℝ := 4 * (D + 1) / r * Real.sqrt T
  have hV₀ : 0 ≤ windowSquareBudget D r := (windowSquareBudget_pos hD hr).le
  have hsq : (D + q) ^ 2 ≤ 2 * D ^ 2 + 2 * q ^ 2 := by
    nlinarith only [sq_nonneg (D - q)]
  have hmgf : (D + q) ^ 2 * V / 2 ≤
      D ^ 2 * windowSquareBudget D r + q ^ 2 * windowSquareBudget D r := by
    have h₁ := mul_le_mul_of_nonneg_left hcost (sq_nonneg (D + q))
    have h₂ := mul_le_mul_of_nonneg_right hsq hV₀
    nlinarith only [h₁, h₂]
  have hpay : q * (r * Real.sqrt T / 2) = 2 * (D + 1) * T := by
    calc q * (r * Real.sqrt T / 2) = 2 * (D + 1) * Real.sqrt T ^ 2 := by
          dsimp only [q]
          field_simp [hr.ne']
          <;> ring
      _ = _ := by rw [Real.sq_sqrt hT]
  have hmoment : q ^ 2 * windowSquareBudget D r = (D + 1) * T := by
    have hD₁ : D + 1 ≠ 0 := ne_of_gt (by linarith only [hD])
    calc q ^ 2 * windowSquareBudget D r = (D + 1) * Real.sqrt T ^ 2 := by
          dsimp only [q, windowSquareBudget]
          field_simp [hr.ne', hD₁]
          <;> ring
      _ = _ := by rw [Real.sq_sqrt hT]
  have hheight := mul_le_mul_of_nonneg_left ht hD
  change D * |t| - q * (r * Real.sqrt T / 2) + (D + q) ^ 2 * V / 2 ≤ _
  rw [hpay]
  rw [hmoment] at hmgf
  nlinarith only [hmgf, hheight]

/-- Infinite positive deletion pays only exponentially small leakage on square-root windows. -/
theorem infinite_tail_squareRoot_floor {ι : Type*} (a h : ℕ → ℝ)
    (hsq : Summable fun i => h i ^ 2) (c w : ι → ℂ) {D r : ℝ}
    (hD : 0 ≤ D) (hr : 0 < r)
    (hc : Summable fun i => ‖c i‖) (hw : ∀ i, c i ≠ 0 → |(w i).re| ≤ D)
    (hcost : (∑' i, h i ^ 2) ≤ windowSquareBudget D r)
    {K B T t : ℝ} (hK : 0 ≤ K) (hT : 0 ≤ T) (ht : |t| ≤ T + B)
    (hlocal : ∀ u, |u - t| ≤ r * Real.sqrt T / 2 →
      -K ≤ ∑' i, (c i * Complex.exp (w i * u)).re) :
    -K - 2 * (∑' i, ‖c i‖) *
        Real.exp (D * B + D ^ 2 * windowSquareBudget D r - T) ≤
      ∑' i, (c i * (∏' n, quartetFactor (a n) (h n) (w i)) *
        Complex.exp (w i * t)).re := by
  have hq : 0 ≤ 4 * (D + 1) / r * Real.sqrt T := by positivity
  have h := infinite_tail_translated_floor a h hsq c w hD hc hw hK hq hlocal
  have hexp := Real.exp_le_exp.mpr
    (gaussian_squareRoot_exponent_le hD hr hcost hT ht)
  have hm := mul_le_mul_of_nonneg_left hexp
    (show 0 ≤ 2 * (∑' i, ‖c i‖) from mul_nonneg (by norm_num) (tsum_nonneg fun _ => norm_nonneg _))
  linarith only [h, hm]

#print axioms infinite_tail_squareRoot_floor

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
