/-
Unconditional sharp floor-failure density bound: (APPROX) discharged.

Instantiating the abstract Weierstrass majorant (`exists_poly_majorant_expectation`) at the
carrier modulus-squared `Y = ‖∑ aₙ Xₙ‖²` produces, for every `δ > 0`, a polynomial in `‖F‖²`
that majorizes the line failure indicator and whose model expectation is within `δ` of the
model small-ball measure (`exists_poly_majorant_family`). Feeding this family into the
`δ → 0` collapse of `floorFailure_timeDensity_le_sharp` yields the sharp density bound with no
remaining approximation hypothesis: the Cesàro upper time density of any `[0,1]`-observable on
`{‖F‖ ≤ t₀}` is at most the model small-ball measure.
-/
import GaloisForLFunctions.RHTower.WeierstrassMajorant
import GaloisForLFunctions.RHTower.BohrMomentDensity

open MeasureTheory intervalIntegral Filter Topology Complex Finset
open scoped Classical

namespace RHTower

open Weyl SteinhausModel

/-- The model Dirichlet polynomial is bounded by `∑|aₙ|`. -/
theorem norm_modelSum_le (a : ℕ → ℝ) (s : Finset ℕ) (ω : Omega) :
    ‖∑ n ∈ s, (a n : ℂ) * X n ω‖ ≤ ∑ n ∈ s, |a n| := by
  refine le_trans (norm_sum_le _ _) ?_
  apply Finset.sum_le_sum
  intro n _
  rw [norm_mul, norm_X, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- The line Dirichlet polynomial is bounded by `∑|aₙ|`. -/
theorem norm_dpoly_le (a : ℕ → ℝ) (s : Finset ℕ) (τ : ℝ) :
    ‖dpoly a s τ‖ ≤ ∑ n ∈ s, |a n| := by
  rw [dpoly]
  refine le_trans (norm_sum_le _ _) ?_
  apply Finset.sum_le_sum
  intro n _
  rw [cterm, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hre : (-(τ : ℂ) * Complex.I * (Real.log n : ℂ)).re = 0 := by
    have : -(τ : ℂ) * Complex.I * (Real.log n : ℂ)
        = ((-(τ * Real.log n) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.mul_I_re, Complex.ofReal_im, neg_zero]
  have hnexp : ‖Complex.exp (-(τ : ℂ) * Complex.I * (Real.log n : ℂ))‖ = 1 := by
    rw [Complex.norm_exp, hre, Real.exp_zero]
  rw [hnexp, mul_one]

/-- **The polynomial-majorant family for the carrier small-ball.** For every `δ > 0` there is
a polynomial in `‖F‖²` majorizing the line failure indicator whose model expectation is within
`δ` of the model small-ball measure. Instantiates the abstract Weierstrass majorant at the
carrier modulus-squared. -/
theorem exists_poly_majorant_family
    (a : ℕ → ℝ) (s : Finset ℕ) (t₀ : ℝ) (ht0 : 0 ≤ t₀) (ht0R : t₀ ≤ ∑ n ∈ s, |a n|)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (d : ℕ) (c : ℕ → ℝ),
      (∀ τ : ℝ, ‖dpoly a s τ‖ ≤ t₀ →
        1 ≤ ∑ j ∈ range (d + 1), c j * ‖dpoly a s τ‖ ^ (2 * j)) ∧
      (∀ τ : ℝ, 0 ≤ ∑ j ∈ range (d + 1), c j * ‖dpoly a s τ‖ ^ (2 * j)) ∧
      (∑ j ∈ range (d + 1),
          c j * ∫ ω, ‖∑ n ∈ s, (a n : ℂ) * X n ω‖ ^ (2 * j) ∂steinhausMeasure)
        ≤ (steinhausMeasure {ω : Omega | ‖∑ n ∈ s, (a n : ℂ) * X n ω‖ ≤ t₀}).toReal + δ := by
  set Rb : ℝ := ∑ n ∈ s, |a n| with hRb
  have hRb0 : 0 ≤ Rb := Finset.sum_nonneg (fun n _ => abs_nonneg _)
  set Y : Omega → ℝ := fun ω => ‖∑ n ∈ s, (a n : ℂ) * X n ω‖ ^ 2 with hYdef
  have hSmeas : Measurable (fun ω : Omega => ∑ n ∈ s, (a n : ℂ) * X n ω) := by
    apply Finset.measurable_sum
    intro n _
    exact (measurable_X n).const_mul _
  have hYmeas : Measurable Y := by rw [hYdef]; exact (hSmeas.norm.pow_const 2)
  have hYR : ∀ ω, Y ω ∈ Set.Icc (0 : ℝ) (Rb ^ 2) := by
    intro ω
    refine ⟨by positivity, ?_⟩
    rw [hYdef]
    have hb := norm_modelSum_le a s ω
    nlinarith [norm_nonneg (∑ n ∈ s, (a n : ℂ) * X n ω)]
  have hθR : t₀ ^ 2 ≤ Rb ^ 2 := by nlinarith
  obtain ⟨q, hq1, hq0, hqE⟩ :=
    exists_poly_majorant_expectation (μ := steinhausMeasure) Y hYmeas (sq_nonneg t₀) hθR hYR hδ
  refine ⟨q.natDegree, q.coeff, ?_, ?_, ?_⟩
  · -- ≥ 1 on the failure set
    intro τ hτ
    have hexp : ∑ j ∈ range (q.natDegree + 1), q.coeff j * ‖dpoly a s τ‖ ^ (2 * j)
        = q.eval (‖dpoly a s τ‖ ^ 2) := by
      rw [Polynomial.eval_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_mul]
    rw [hexp]
    apply hq1
    refine ⟨by positivity, ?_⟩
    nlinarith [norm_nonneg (dpoly a s τ)]
  · -- ≥ 0 everywhere
    intro τ
    have hexp : ∑ j ∈ range (q.natDegree + 1), q.coeff j * ‖dpoly a s τ‖ ^ (2 * j)
        = q.eval (‖dpoly a s τ‖ ^ 2) := by
      rw [Polynomial.eval_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_mul]
    rw [hexp]
    apply hq0
    refine ⟨by positivity, ?_⟩
    have hb := norm_dpoly_le a s τ
    nlinarith [norm_nonneg (dpoly a s τ)]
  · -- expectation clause
    have hint : ∀ j : ℕ, Integrable
        (fun ω => q.coeff j * ‖∑ n ∈ s, (a n : ℂ) * X n ω‖ ^ (2 * j)) steinhausMeasure := by
      intro j
      apply (integrable_const (|q.coeff j| * Rb ^ (2 * j))).mono'
        ((hSmeas.norm.pow_const (2 * j)).const_mul _).aestronglyMeasurable
      filter_upwards with ω
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      have hb := norm_modelSum_le a s ω
      have : |‖∑ n ∈ s, (a n : ℂ) * X n ω‖| = ‖∑ n ∈ s, (a n : ℂ) * X n ω‖ :=
        abs_of_nonneg (norm_nonneg _)
      rw [this]
      gcongr
    have hlin : ∑ j ∈ range (q.natDegree + 1),
          q.coeff j * ∫ ω, ‖∑ n ∈ s, (a n : ℂ) * X n ω‖ ^ (2 * j) ∂steinhausMeasure
        = ∫ ω, q.eval (Y ω) ∂steinhausMeasure := by
      have h1 : ∀ j : ℕ,
          q.coeff j * ∫ ω, ‖∑ n ∈ s, (a n : ℂ) * X n ω‖ ^ (2 * j) ∂steinhausMeasure
            = ∫ ω, q.coeff j * ‖∑ n ∈ s, (a n : ℂ) * X n ω‖ ^ (2 * j) ∂steinhausMeasure :=
        fun j => (MeasureTheory.integral_const_mul _ _).symm
      simp_rw [h1]
      rw [← integral_finsetSum _ (fun j _ => hint j)]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with ω
      rw [hYdef, Polynomial.eval_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_mul]
    rw [hlin]
    have hset : {ω : Omega | Y ω ≤ t₀ ^ 2}
        = {ω : Omega | ‖∑ n ∈ s, (a n : ℂ) * X n ω‖ ≤ t₀} := by
      ext ω
      simp only [hYdef, Set.mem_setOf_eq]
      constructor
      · intro h; nlinarith [norm_nonneg (∑ n ∈ s, (a n : ℂ) * X n ω)]
      · intro h; nlinarith [norm_nonneg (∑ n ∈ s, (a n : ℂ) * X n ω)]
    rw [hset] at hqE
    exact hqE

/-- **Unconditional sharp floor-failure density bound.** The Cesàro upper time density of any
`[0,1]`-observable supported on the vertical floor-failure set `{‖F‖ ≤ t₀}` is at most
`B.toReal`, where `B` is any bound on the model small-ball measure. No approximation
hypothesis remains: the polynomial-majorant family is supplied by `exists_poly_majorant_family`,
so the `δ → 0` collapse of `floorFailure_timeDensity_le_sharp` runs unconditionally. -/
theorem floorFailure_timeDensity_le_unconditional
    (a : ℕ → ℝ) (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n) (t₀ : ℝ) (ht0 : 0 ≤ t₀)
    (ht0R : t₀ ≤ ∑ n ∈ s, |a n|) (B : ENNReal) (hBtop : B ≠ ⊤)
    (hmodel : steinhausMeasure {ω : Omega | ‖∑ n ∈ s, (a n : ℂ) * X n ω‖ ≤ t₀} ≤ B)
    (fail : ℝ → ℝ) (hfail0 : ∀ τ, 0 ≤ fail τ) (hfle1 : ∀ τ, fail τ ≤ 1)
    (hfsupp : ∀ τ, t₀ < ‖dpoly a s τ‖ → fail τ = 0)
    (hfail_int : ∀ T : ℝ, IntervalIntegrable fail volume 0 T) :
    cesaroUpperDensity fail ≤ B.toReal :=
  floorFailure_timeDensity_le_sharp a s hs t₀ B hBtop hmodel fail hfail0 hfle1 hfsupp hfail_int
    (fun δ hδ => exists_poly_majorant_family a s t₀ ht0 ht0R δ hδ)

end RHTower
