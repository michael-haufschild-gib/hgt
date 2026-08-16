import GaloisForLFunctions.RHTower.RealJetsOfHolomorphic

/-!
# Landau's theorem: the abscissa is a genuine singularity

If the Laplace transform of a nonnegative measure agreed, right of its abscissa, with a function
holomorphic on a whole disc centred at the abscissa, then the transform's Taylor series at a point
slightly right of the abscissa would converge on a radius exceeding the distance to it — which the
moment form of Landau's theorem forbids.

The bridge between the two sides is the jet transfer: the real jets of the transform are the complex
jets of the extension, and those are `(−1)^k` times the moments.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

set_option maxHeartbeats 1000000 in
/-- **The abscissa is a genuine singularity.** -/
theorem false_of_analyticAt_abscissa {ν : Measure ℝ} {c : ℝ} (hc : IsAbscissa ν c)
    {Φ : ℂ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hΦ : ∀ z ∈ Metric.ball ((c : ℂ)) δ, AnalyticAt ℂ Φ z)
    (hagree : ∀ σ : ℝ, c < σ → σ < c + δ → Φ ((σ : ℂ)) = ((laplaceReal ν σ : ℝ) : ℂ)) :
    False := by
  set a : ℝ := c + δ / 4 with hadef
  have hca : c < a := by rw [hadef]; linarith
  have haball : |a - c| < δ := by
    rw [hadef, abs_of_nonneg (by linarith : (0:ℝ) ≤ c + δ / 4 - c)]
    linarith
  have haC : ((a : ℂ)) ∈ Metric.ball ((c : ℂ)) δ := mem_ball_ofReal haball
  -- the real jets of the restriction are the moments
  set S : Set ℝ := Ioo c (c + δ) with hSdef
  have hSopen : IsOpen S := isOpen_Ioo
  have haS : a ∈ S := ⟨hca, by rw [hadef]; linarith⟩
  have hjet : ∀ n : ℕ, ∀ σ ∈ S,
      iteratedDeriv n (fun t : ℝ => Φ ((t : ℂ))) σ
        = ((((-1 : ℝ) ^ n * laplaceMomentReal ν σ n : ℝ)) : ℂ) := by
    intro n
    induction n with
    | zero =>
      intro σ hσ
      rw [iteratedDeriv_zero]
      have := hagree σ hσ.1 hσ.2
      rw [this, laplaceReal, laplaceMomentReal]
      norm_num
    | succ n ih =>
      intro σ hσ
      have hEq : iteratedDeriv n (fun t : ℝ => Φ ((t : ℂ)))
          =ᶠ[nhds σ] fun y : ℝ => ((((-1 : ℝ) ^ n * laplaceMomentReal ν y n : ℝ)) : ℂ) := by
        filter_upwards [hSopen.mem_nhds hσ] with y hy
        exact ih y hy
      have hd : HasDerivAt
          (fun y : ℝ => ((((-1 : ℝ) ^ n * laplaceMomentReal ν y n : ℝ)) : ℂ))
          ((((-1 : ℝ) ^ n * (-laplaceMomentReal ν σ (n + 1)) : ℝ)) : ℂ) σ :=
        HasDerivAt.ofReal_comp ((hasDerivAt_laplaceMomentReal hc hσ.1 n).const_mul _)
      rw [iteratedDeriv_succ, hEq.deriv_eq, hd.deriv]
      push_cast
      ring
  -- transfer to the complex jets
  have hjetC : ∀ n : ℕ,
      iteratedDeriv n Φ ((a : ℂ)) = ((((-1 : ℝ) ^ n * laplaceMomentReal ν a n : ℝ)) : ℂ) := by
    intro n
    rw [← iteratedDeriv_ofReal_comp hΦ n a haball]
    exact hjet n a haS
  -- the power series on a ball inside the disc
  set R : NNReal := (δ / 2).toNNReal with hRdef
  have hRval : ((R : ℝ)) = δ / 2 := Real.coe_toNNReal _ (by linarith)
  have hR0 : 0 < R := by
    rw [← NNReal.coe_pos, hRval]
    linarith
  have hsub : Metric.closedBall ((a : ℂ)) ((R : ℝ)) ⊆ Metric.ball ((c : ℂ)) δ := by
    intro z hz
    have h1 : dist z ((a : ℂ)) ≤ (R : ℝ) := Metric.mem_closedBall.mp hz
    have h2 : dist ((a : ℂ)) ((c : ℂ)) < δ := Metric.mem_ball.mp haC
    have h3 : dist ((a : ℂ)) ((c : ℂ)) = |a - c| := by
      rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have h4 : |a - c| = δ / 4 := by
      rw [hadef, abs_of_nonneg (by linarith : (0:ℝ) ≤ c + δ / 4 - c)]
      ring
    refine Metric.mem_ball.mpr ?_
    calc dist z ((c : ℂ)) ≤ dist z ((a : ℂ)) + dist ((a : ℂ)) ((c : ℂ)) := dist_triangle _ _ _
      _ ≤ (R : ℝ) + δ / 4 := add_le_add h1 (by rw [h3, h4])
      _ = δ / 2 + δ / 4 := by rw [hRval]
      _ < δ := by linarith
  have hdiff : DifferentiableOn ℂ Φ (Metric.closedBall ((a : ℂ)) ((R : ℝ))) := by
    intro z hz
    exact ((hΦ z (hsub hz)).differentiableAt).differentiableWithinAt
  have hball := hdiff.hasFPowerSeriesOnBall hR0
  have hcan : HasFPowerSeriesAt Φ
      (FormalMultilinearSeries.ofScalars ℂ
        fun n => iteratedDeriv n Φ ((a : ℂ)) / (n.factorial : ℂ)) ((a : ℂ)) :=
    (hΦ _ haC).hasFPowerSeriesAt
  have hpeq := hball.hasFPowerSeriesAt.eq_formalMultilinearSeries hcan
  have hrad : ((R : ℝ≥0∞)) ≤ (FormalMultilinearSeries.ofScalars ℂ
      fun n => iteratedDeriv n Φ ((a : ℂ)) / (n.factorial : ℂ)).radius := by
    rw [← hpeq]
    exact hball.r_le
  -- the Taylor radius exceeds the distance to the abscissa
  set t : NNReal := (3 * δ / 8).toNNReal with htdef
  have htval : ((t : ℝ)) = 3 * δ / 8 := Real.coe_toNNReal _ (by linarith)
  have htR : ((t : ℝ≥0∞)) < (FormalMultilinearSeries.ofScalars ℂ
      fun n => iteratedDeriv n Φ ((a : ℂ)) / (n.factorial : ℂ)).radius := by
    refine lt_of_lt_of_le ?_ hrad
    rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, htval, hRval]
    linarith
  have hsum := (FormalMultilinearSeries.ofScalars ℂ
    fun n => iteratedDeriv n Φ ((a : ℂ)) / (n.factorial : ℂ)).summable_norm_mul_pow htR
  -- rewrite the summand as the moment series
  have hterm : ∀ n : ℕ,
      ‖FormalMultilinearSeries.ofScalars ℂ
          (fun n => iteratedDeriv n Φ ((a : ℂ)) / (n.factorial : ℂ)) n‖ * ((t : ℝ)) ^ n
        = ((t : ℝ)) ^ n / (n.factorial : ℝ) * laplaceMomentReal ν a n := by
    intro n
    rw [FormalMultilinearSeries.ofScalars_norm, hjetC n]
    have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have hm : (0 : ℝ) ≤ laplaceMomentReal ν a n := laplaceMomentReal_nonneg a n
    rw [norm_div]
    have h1 : ‖((((-1 : ℝ) ^ n * laplaceMomentReal ν a n : ℝ)) : ℂ)‖
        = laplaceMomentReal ν a n := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
        one_mul, abs_of_nonneg hm]
    have h2 : ‖((n.factorial : ℂ))‖ = (n.factorial : ℝ) := by
      rw [← Complex.ofReal_natCast, Complex.norm_real, Real.norm_of_nonneg hfac.le]
    rw [h1, h2]
    field_simp
  refine not_summable_moment_beyond_abscissa hc hca (by positivity) ?_ (hsum.congr hterm)
  rw [hadef, htval]
  linarith

end GaloisForLFunctions.RHTower
