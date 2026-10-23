import GaloisForLFunctions.TransThresholdPairCorrelation.FejerWeightedPrimeMeanSquare
import GaloisForLFunctions.RHTower.ZetaWeightedGramIntegral
import Zeta23.PrimeSideA.EndsE1

/-!
# The Grid Kernel of a Smooth Height Weight

For grid weights `W_k = W(τ_k)` sampled from a weight `0 ≤ W ≤ 1` on the grid `τ_k = T + kh`, the
weighted kernel `K_W(τ,τ') = Σ_{k<d} W(τ_k) φ̂(τ−τ_k) φ̂(τ'−τ_k)` differs from `W(τ)·K(τ,τ')`
(`K` the unweighted grid kernel) by
`Σ_k (W(τ_k) − W(τ)) φ̂(τ−τ_k) φ̂(τ'−τ_k)` (`KfunW_sub_mul_Kfun_eq`). With `|φ̂(r)| ≤ A/(1 + r²)`,
`A = L + c_ϱ/w`, and a Lipschitz weight, every coefficient is at most `min(ℓ|τ_k − τ|, 1)`.

The grid sums are controlled by one averaging lemma (`sum_grid_le_integral`): a profile that is
locally comparable on cells of length `h` sums to at most `C/h` times its integral. For Lorentz
profiles of width `1/c` this gives `Σ_{k<n} (1 + c²(x − τ_k)²)⁻¹ ≤ 4π/(ch)`
(`sum_lor_grid_le`), and the Lipschitz-weighted sums cost only `√ℓ`
(`min_mul_lor1_le`: `min(ℓ|r|, 1)/(1 + r²) ≤ 2ℓ/(1 + ℓr²)`).
-/

open MeasureTheory Real Set Finset Filter
open scoped BigOperators ArithmeticFunction
open Zeta23 Zeta23.PrimeSide RHTower

noncomputable section

namespace GaloisForLFunctions.TransThresholdPairCorrelation

/-! ## 1. Lorentz profiles -/

/-- The unit Lorentz profile `(1 + r²)⁻¹`. -/
def lor1 (r : ℝ) : ℝ := (1 + r ^ 2)⁻¹

theorem lor1_pos (r : ℝ) : 0 < lor1 r := by unfold lor1; positivity

theorem lor1_le_one (r : ℝ) : lor1 r ≤ 1 := by
  unfold lor1; exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg r])

theorem lor1_neg (r : ℝ) : lor1 (-r) = lor1 r := by unfold lor1; rw [neg_sq]

theorem continuous_lor1 : Continuous lor1 := by
  unfold lor1
  exact (continuous_const.add (continuous_pow 2)).inv₀ fun r =>
    (add_pos_of_pos_of_nonneg one_pos (sq_nonneg r)).ne'

theorem integrable_lor1 : Integrable lor1 := integrable_inv_one_add_sq

theorem integral_lor1 : ∫ r, lor1 r = π := integral_univ_inv_one_add_sq

/-- `lor1` is antitone in `|r|`. -/
theorem lor1_le_lor1_of_abs_le {a b : ℝ} (h : |a| ≤ |b|) : lor1 b ≤ lor1 a := by
  unfold lor1
  refine inv_anti₀ (by positivity) ?_
  have : a ^ 2 ≤ b ^ 2 := by rw [← sq_abs a, ← sq_abs b]; exact pow_le_pow_left₀ (abs_nonneg a) h 2
  linarith

/-- Local comparability: `lor1 a ≤ 4 lor1 b` when `|a − b| ≤ 1/2`. -/
theorem lor1_le_four_mul {a b : ℝ} (hab : |a - b| ≤ 1 / 2) : lor1 a ≤ 4 * lor1 b := by
  unfold lor1
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_eq_div, div_le_iff₀ (by positivity)]
  have hb : |b| ≤ |a| + 1 / 2 := by
    have := abs_sub_abs_le_abs_sub b a; rw [abs_sub_comm] at this; linarith
  have h2 : b ^ 2 ≤ (|a| + 1 / 2) ^ 2 := by
    rw [← sq_abs b]; exact pow_le_pow_left₀ (abs_nonneg b) hb 2
  nlinarith [sq_abs a, abs_nonneg a, sq_nonneg (|a| - 1 / 6)]

/-- `min(ℓ|r|, 1)/(1 + r²) ≤ 2ℓ/(1 + ℓr²)` for `0 < ℓ`. -/
theorem min_mul_lor1_le {ℓ : ℝ} (hℓ : 0 < ℓ) (r : ℝ) :
    min (ℓ * |r|) 1 * lor1 r ≤ 2 * ℓ * lor1 (Real.sqrt ℓ * r) := by
  have hs : Real.sqrt ℓ ^ 2 = ℓ := Real.sq_sqrt hℓ.le
  unfold lor1
  rw [mul_pow, hs]
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
  rcases le_total (ℓ * r ^ 2) 1 with h | h
  · -- inner region: `min ≤ ℓ|r| ≤ ℓ(1 + r²)/2`
    have h1 : min (ℓ * |r|) 1 ≤ ℓ * |r| := min_le_left _ _
    have h2 : |r| ≤ (1 + r ^ 2) / 2 := by nlinarith [sq_abs r, sq_nonneg (|r| - 1)]
    have h3 : 0 ≤ min (ℓ * |r|) 1 := le_min (by positivity) zero_le_one
    nlinarith [mul_le_mul_of_nonneg_left h2 hℓ.le]
  · -- outer region: `min ≤ 1` and `1 + ℓr² ≤ 2ℓr² ≤ 2ℓ(1 + r²)`
    have h1 : min (ℓ * |r|) 1 ≤ 1 := min_le_right _ _
    have h3 : 0 ≤ min (ℓ * |r|) 1 := le_min (by positivity) zero_le_one
    nlinarith

/-! ## 2. Grid sums by cell averaging -/

/-- **Cell averaging.** If `g(x − t) ≤ C g(x − s)` whenever `|s − t| ≤ h/2`, then the grid sum
over `t₀ + kh`, `k < n`, is at most `C/h` times the integral over the union of the cells. -/
theorem sum_grid_le_integral {g : ℝ → ℝ} (hg : Continuous g) {C h t₀ x : ℝ} (hh : 0 < h)
    (hloc : ∀ t s, |s - t| ≤ h / 2 → g (x - t) ≤ C * g (x - s)) (n : ℕ) :
    ∑ k ∈ Finset.range n, g (x - (t₀ + k * h))
      ≤ (C / h) * ∫ s in (t₀ - h / 2)..(t₀ + n * h - h / 2), g (x - s) := by
  set a : ℕ → ℝ := fun k => t₀ + k * h - h / 2 with ha
  have hgc : Continuous fun s => C * g (x - s) := continuous_const.mul (hg.comp (by fun_prop))
  have hcell : ∀ k : ℕ, g (x - (t₀ + k * h)) ≤ (1 / h) * ∫ s in a k..a (k + 1), C * g (x - s) := by
    intro k
    have hlen : a k ≤ a (k + 1) := by simp only [ha]; push_cast; linarith
    have hmono : ∫ s in a k..a (k + 1), g (x - (t₀ + k * h)) ≤ ∫ s in a k..a (k + 1), C * g (x - s) :=
      intervalIntegral.integral_mono_on hlen intervalIntegrable_const (hgc.intervalIntegrable _ _)
        fun s hs => hloc _ _ (by
          simp only [ha] at hs; push_cast at hs
          rw [abs_le]; constructor <;> linarith [hs.1, hs.2])
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    have e : a (k + 1) - a k = h := by simp only [ha]; push_cast; ring
    rw [e] at hmono
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hh, mul_comm]
    exact hmono
  calc ∑ k ∈ Finset.range n, g (x - (t₀ + k * h))
      ≤ ∑ k ∈ Finset.range n, (1 / h) * ∫ s in a k..a (k + 1), C * g (x - s) :=
        Finset.sum_le_sum fun k _ => hcell k
    _ = (1 / h) * ∫ s in a 0..a n, C * g (x - s) := by
        rw [← Finset.mul_sum, intervalIntegral.sum_integral_adjacent_intervals
          fun k _ => hgc.intervalIntegrable _ _]
    _ = (C / h) * ∫ s in (t₀ - h / 2)..(t₀ + n * h - h / 2), g (x - s) := by
        rw [intervalIntegral.integral_const_mul]; simp only [ha]; push_cast
        rw [zero_mul, add_zero]; ring

/-- **Lorentz grid sums.** For `0 < c ≤ 1` and `0 < h ≤ 1`:
`Σ_{k<n} (1 + c²(x − (t₀ + kh))²)⁻¹ ≤ 4π/(ch)`. -/
theorem sum_lor_grid_le {c h : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (t₀ x : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, lor1 (c * (x - (t₀ + k * h))) ≤ 4 * π / (c * h) := by
  have hgc : Continuous fun r => lor1 (c * r) := continuous_lor1.comp (continuous_const.mul continuous_id)
  have h1 := sum_grid_le_integral (g := fun r => lor1 (c * r)) hgc (C := 4) (t₀ := t₀) (x := x) hh
    (fun t s hts => lor1_le_four_mul (by
      rw [← mul_sub, abs_mul, abs_of_pos hc]
      calc c * |x - t - (x - s)| = c * |s - t| := by congr 1; ring_nf
        _ ≤ 1 * (h / 2) := mul_le_mul hc1 hts (abs_nonneg _) zero_le_one
        _ ≤ 1 / 2 := by linarith)) n
  refine h1.trans ?_
  have hint : Integrable fun s => lor1 (c * (x - s)) := by
    have := (integrable_lor1.comp_mul_left' hc.ne').comp_sub_left x
    simpa [Function.comp] using this
  have hle : (∫ s in (t₀ - h / 2)..(t₀ + n * h - h / 2), lor1 (c * (x - s))) ≤ π / c := by
    have hab : t₀ - h / 2 ≤ t₀ + n * h - h / 2 := by
      have : (0 : ℝ) ≤ n * h := by positivity
      linarith
    rw [intervalIntegral.integral_of_le hab]
    refine (setIntegral_le_integral hint (Eventually.of_forall fun s => (lor1_pos _).le)).trans
      (le_of_eq ?_)
    rw [integral_sub_left_eq_self (fun r => lor1 (c * r)) (μ := volume) x]
    have := Measure.integral_comp_mul_left (fun r => lor1 r) c
    rw [this, integral_lor1, smul_eq_mul, abs_of_pos (inv_pos.mpr hc)]
    field_simp
  calc 4 / h * ∫ s in (t₀ - h / 2)..(t₀ + n * h - h / 2), lor1 (c * (x - s))
      ≤ 4 / h * (π / c) := mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 4 * π / (c * h) := by field_simp

/-- Far from all grid points every term is at most `lor1(D)`. -/
theorem sum_lor1_grid_le_far {D t₀ h x : ℝ} {n : ℕ}
    (hD : ∀ k < n, D ≤ |x - (t₀ + k * h)|) (hD0 : 0 ≤ D) :
    ∑ k ∈ Finset.range n, lor1 (x - (t₀ + k * h)) ≤ n * lor1 D := by
  calc ∑ k ∈ Finset.range n, lor1 (x - (t₀ + k * h)) ≤ ∑ _k ∈ Finset.range n, lor1 D :=
        Finset.sum_le_sum fun k hk => lor1_le_lor1_of_abs_le (by
          rw [abs_of_nonneg hD0]; exact hD k (Finset.mem_range.mp hk))
    _ = n * lor1 D := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end GaloisForLFunctions.TransThresholdPairCorrelation
