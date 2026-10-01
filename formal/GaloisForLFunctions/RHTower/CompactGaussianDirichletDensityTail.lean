import GaloisForLFunctions.RHTower.CompactGaussianDirichletDensityEnergy

open Complex MeasureTheory Filter Topology Finset
noncomputable section
namespace RHTower
open SteinhausModel

private theorem norm_finiteSteinhausPoly_le (S : Finset ℕ) (a : ℕ → ℂ) (ω : Omega) :
    ‖∑ n ∈ S, a n * X n ω‖ ≤ ∑ n ∈ S, ‖a n‖ := by
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro n _
  rw [norm_mul, norm_X, mul_one]

private theorem measurable_finiteSteinhausPoly (S : Finset ℕ) (a : ℕ → ℂ) :
    Measurable (fun ω => ∑ n ∈ S, a n * X n ω) :=
  Finset.measurable_sum S (fun n _ => (measurable_X n).const_mul _)

private theorem integrable_finiteSteinhausPoly_normSq (S : Finset ℕ) (a : ℕ → ℂ) :
    Integrable (fun ω => ‖∑ n ∈ S, a n * X n ω‖ ^ 2) steinhausMeasure := by
  apply Integrable.of_bound ((measurable_finiteSteinhausPoly S a).norm.pow_const 2).aestronglyMeasurable
    ((∑ n ∈ S, ‖a n‖) ^ 2)
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_finiteSteinhausPoly_le S a ω) 2

private theorem integrable_finiteSteinhausPoly_normSq_mul
    (P S : Finset ℕ) (v a : ℕ → ℂ) :
    Integrable (fun ω => ‖∑ p ∈ P, v p * X p ω‖ ^ 2 *
      ‖∑ n ∈ S, a n * X n ω‖ ^ 2) steinhausMeasure := by
  apply Integrable.of_bound
    (((measurable_finiteSteinhausPoly P v).norm.pow_const 2).mul
      ((measurable_finiteSteinhausPoly S a).norm.pow_const 2)).aestronglyMeasurable
    (((∑ p ∈ P, ‖v p‖) ^ 2) * ((∑ n ∈ S, ‖a n‖) ^ 2))
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  exact mul_le_mul
    (pow_le_pow_left₀ (norm_nonneg _) (norm_finiteSteinhausPoly_le P v ω) 2)
    (pow_le_pow_left₀ (norm_nonneg _) (norm_finiteSteinhausPoly_le S a ω) 2)
    (sq_nonneg _) (sq_nonneg _)

/-- Weighted Markov bound for the literal square density and actual finite
prime carrier. All integrability and measurability obligations are discharged. -/
theorem finiteSteinhausPoly_density_tail_sq_mul_le
    (P S : Finset ℕ) (v a : ℕ → ℂ) {r : ℝ} (hr : 0 ≤ r) :
    r ^ 2 * (∫ ω in {ω | r ≤ ‖∑ p ∈ P, v p * X p ω‖},
      ‖∑ n ∈ S, a n * X n ω‖ ^ 2 ∂steinhausMeasure) ≤
      ∫ ω, ‖∑ p ∈ P, v p * X p ω‖ ^ 2 *
        ‖∑ n ∈ S, a n * X n ω‖ ^ 2 ∂steinhausMeasure := by
  let E : Set Omega := {ω | r ≤ ‖∑ p ∈ P, v p * X p ω‖}
  have hE : MeasurableSet E := measurableSet_le measurable_const (measurable_finiteSteinhausPoly P v).norm
  have hD := integrable_finiteSteinhausPoly_normSq S a
  have hWD := integrable_finiteSteinhausPoly_normSq_mul P S v a
  have hm := setIntegral_mono_on ((hD.const_mul (r ^ 2)).integrableOn) hWD.integrableOn hE
    (fun ω hω => mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr hω 2) (sq_nonneg _))
  rw [integral_const_mul] at hm
  exact hm.trans (setIntegral_le_integral hWD (Filter.Eventually.of_forall
    (fun ω => mul_nonneg (sq_nonneg _) (sq_nonneg _))))

/-- Polynomial frequency-cost densities give vanishing weighted mass to every
fixed nonzero window-amplitude threshold. -/
theorem eventually_compactGaussian_polynomialDirichletCost_tail_small
    (b : ℝ) {D : ℕ} (hD : 0 < D) (A : ℝ) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ tau : ℝ, ∀ L : ℕ, ∀ ω : Omega,
      ∀ s : ℂ, 0 ≤ s.re → s.re ≤ b → ∀ S : Finset ℕ, ∀ a : ℕ → ℂ,
      (∀ n ∈ S, n ≠ 0) → (∑ n ∈ S, ‖a n‖ ^ 2 = 1) →
      (∑ n ∈ S, (n : ℝ) * ‖a n‖ ^ 2) ≤ (N : ℝ) ^ A →
      (∫ ξ in {ξ | r ≤ ‖∑ p ∈ largePrimes N (N / D),
        compactGaussianNormalizedPrimeChannel s N p tau (L / p) ω * X p ξ‖},
          ‖∑ n ∈ S, a n * X n ξ‖ ^ 2 ∂steinhausMeasure) < ε := by
  filter_upwards [eventually_compactGaussian_polynomialDirichletCost_energy_small b hD A
    (mul_pos (sq_pos_of_pos hr) hε)] with N hN
  intro tau L ω s hs0 hsb S a hS hnorm hbudget
  have h := hN tau L ω s hs0 hsb S a hS hnorm hbudget
  have hm := finiteSteinhausPoly_density_tail_sq_mul_le (largePrimes N (N / D)) S
    (fun p => compactGaussianNormalizedPrimeChannel s N p tau (L / p) ω) a hr.le
  exact (mul_lt_mul_iff_right₀ (sq_pos_of_pos hr)).mp (hm.trans_lt h)

end RHTower
