import GaloisForLFunctions.RHTower.XiGaussianDebtDomination
import GaloisForLFunctions.RHTower.XiGaussianHeatHankelLadder

/-!
# Gaussian-norm coercivity of complete finite Xi Hankel forms

The full-divisor slope budget and the independent complex energy floor give a
coefficient-uniform positive margin at small time for each finite order. All
polynomial and Hankel cross terms are retained. The time neighborhood may depend
on order; this theorem does not establish the all-time RH criterion.
-/

open scoped Real SchwartzMap NNReal
open MeasureTheory Filter Topology GaloisForLFunctions
noncomputable section

namespace RHTower

/-- Exact transport of every coefficient under spatial heat scaling. -/
theorem xiGaussian_rangePolynomial_comp_scale (N : ℕ) (a : ℕ → ℝ) (r : ℝ) :
    (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j).comp
        (Polynomial.C (r ^ 2) * Polynomial.X) =
      ∑ j ∈ Finset.range N, Polynomial.C (a j * r ^ (2 * j)) * Polynomial.X ^ j := by
  rw [Polynomial.sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp,
    mul_pow, ← Polynomial.C_pow, ← mul_assoc, ← Polynomial.C_mul, ← pow_mul]

/-- Every finite order has one small-time Gaussian-norm floor for all coefficient vectors. -/
theorem exists_xiHeatHankelForm_eventually_gaussian_coercive :
    ∃ h : ℝ, 0 < h ∧ ∀ N : ℕ, ∀ᶠ τ : ℝ in atBot, ∀ a : ℕ → ℝ,
      (1 / 8 : ℝ) *
        ‖(polyGaussSchwartz (evenSquarePolynomial
          (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j))).toLp 2
            (volume : Measure ℝ)‖ ^ 2 ≤
      (Real.exp τ * h) * xiHeatHankelForm N (fun j => a j * (Real.exp τ) ^ (2 * j))
        (2 * π * (Real.exp τ) ^ 2) := by
  classical
  obtain ⟨h, hh, C, hC, hfloor⟩ := exists_xiGaussian_trace_slope_lower_bound
  refine ⟨h, hh, ?_⟩
  intro N
  have ht := (xiGaussianTraceLoss_tendsto_zero C h (2 * N)).comp Real.tendsto_exp_atBot
  have he := ht.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < 1 / 8))
  filter_upwards [he] with τ hτ a
  let P : Polynomial ℝ := ∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j
  let r : {r : ℝ // 0 < r} := ⟨Real.exp τ, Real.exp_pos τ⟩
  have hd : P.natDegree ≤ N := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    exact (Polynomial.natDegree_C_mul_X_pow_le (a j) j).trans (Finset.mem_range.mp hj).le
  have hd' : 2 * P.natDegree ≤ 2 * N := Nat.mul_le_mul_left _ hd
  have hmono := xiGaussianTraceLoss_mono (⟨C, hC.le⟩ : ℝ≥0) (⟨h, hh.le⟩ : ℝ≥0)
    (⟨Real.exp τ, (Real.exp_pos τ).le⟩ : ℝ≥0) hd'
  have hsmall : xiGaussianTraceLoss C h (2 * P.natDegree) (Real.exp τ) < 1 / 8 :=
    hmono.trans_lt hτ
  have hl := hfloor P r
  have hm := mul_le_mul_of_nonneg_right
    (show (1 / 8 : ℝ) ≤ 1 / 4 - xiGaussianTraceLoss C h (2 * P.natDegree) (Real.exp τ) by
      linarith only [hsmall])
    (sq_nonneg ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2 (volume : Measure ℝ)‖)
  have hall := hm.trans hl
  change (1 / 8 : ℝ) *
      ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2 (volume : Measure ℝ)‖ ^ 2 ≤
    (Real.exp τ * h) * xiPolynomialGaussianHeatTraceReal
      (P.comp (Polynomial.C ((Real.exp τ) ^ 2) * Polynomial.X))
      (2 * π * (Real.exp τ) ^ 2) at hall
  dsimp only [P] at hall
  rw [xiGaussian_rangePolynomial_comp_scale,
    xiPolynomialGaussianHeatTraceReal_rangeSum (by positivity)] at hall
  exact hall

/-- Undoing the diagonal scaling controls the literal Hankel form in every coefficient direction. -/
theorem exists_xiHeatHankelForm_eventually_gaussian_weighted_coercive :
    ∃ h : ℝ, 0 < h ∧ ∀ N : ℕ, ∀ᶠ τ : ℝ in atBot, ∀ a : ℕ → ℝ,
      (1 / 8 : ℝ) *
        ‖(polyGaussSchwartz (evenSquarePolynomial
          (∑ j ∈ Finset.range N, Polynomial.C (a j / (Real.exp τ) ^ (2 * j)) *
            Polynomial.X ^ j))).toLp 2 (volume : Measure ℝ)‖ ^ 2 ≤
      (Real.exp τ * h) * xiHeatHankelForm N a (2 * π * (Real.exp τ) ^ 2) := by
  obtain ⟨h, hh, hall⟩ := exists_xiHeatHankelForm_eventually_gaussian_coercive
  refine ⟨h, hh, ?_⟩
  intro N
  filter_upwards [hall N] with τ hτ a
  have hc (j : ℕ) : a j / (Real.exp τ) ^ (2 * j) * (Real.exp τ) ^ (2 * j) = a j :=
    div_mul_cancel₀ _ (pow_ne_zero _ (Real.exp_pos τ).ne')
  simpa only [hc] using hτ (fun j => a j / (Real.exp τ) ^ (2 * j))

end RHTower
