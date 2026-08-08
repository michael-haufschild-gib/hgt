import GaloisForLFunctions.RHTower.XiGuinandWeilRectangularFourier
import GaloisForLFunctions.HTGeometry.DigammaGaussSeries

/-!
# Resolvent evaluation against the sharp rectangular Fourier square

This is the Laplace--Fourier bridge needed for the archimedean edge.  Absolute integrability on
the product is proved directly from the `L¹` rectangular Fourier square and a decaying causal
exponential; no regularity beyond the already formalized piecewise-linear autocorrelation enters.
-/

open Complex MeasureTheory Set

noncomputable section

namespace RHTower

/-- A positive vertical resolvent paired with the sharp rectangular Fourier square is exactly the
causal Laplace transform of the exponentially tilted autocorrelation at half the time scale. -/
theorem integral_rectangularEulerFourierKernel_mul_verticalResolvent
    {L c : ℝ} (hL : 0 ≤ L) (hc : 0 < c) (a : ℝ) :
    (∫ ξ : ℝ,
        rectangularTwoEdgeTransform L a
            (1 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) ^ 2 *
          (((c : ℝ) : ℂ) - ((Real.pi * ξ : ℝ) : ℂ) * I)⁻¹) =
      ∫ t : ℝ in Ioi 0,
        Complex.exp (-(c : ℂ) * (t : ℂ)) *
          ((rectangularTwoEdgeAutocorrelation L a (t / 2) : ℂ) *
            Complex.exp (t / 2)) := by
  let F : ℝ → ℂ := fun ξ =>
    rectangularTwoEdgeTransform L a
      (1 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) ^ 2
  let e : ℝ → ℂ := (Ioi (0 : ℝ)).indicator
    (fun t : ℝ => Complex.exp (-(c : ℂ) * (t : ℂ)))
  let K : ℝ × ℝ → ℂ := fun p =>
    Complex.exp (((Real.pi * p.2 * p.1 : ℝ) : ℂ) * I) *
      (e p.1 * F p.2)
  have he : Integrable e := by
    dsimp only [e]
    rw [integrable_indicator_iff measurableSet_Ioi]
    exact integrableOn_exp_mul_complex_Ioi
      (a := -(c : ℂ)) (by simp only [Complex.neg_re, Complex.ofReal_re]; linarith) 0
  have hF : Integrable F := by
    simpa only [F] using integrable_rectangularTwoEdgeTransform_eulerLine_sq L a
  have hbase : Integrable (fun p : ℝ × ℝ => e p.1 * F p.2) :=
    he.mul_prod hF
  have hK : Integrable K := by
    dsimp only [K]
    refine hbase.norm.mono' ?_ ?_
    · exact
        (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable.mul
          hbase.aestronglyMeasurable
    · filter_upwards with p
      rw [norm_mul, Complex.norm_exp]
      have hre : ((((Real.pi * p.2 * p.1 : ℝ) : ℂ) * I)).re = 0 := by
        simp [Complex.mul_re]
      rw [hre, Real.exp_zero, one_mul]
  have hresolvent : ∀ ξ : ℝ,
      (((c : ℝ) : ℂ) - ((Real.pi * ξ : ℝ) : ℂ) * I)⁻¹ =
        ∫ t : ℝ in Ioi 0,
          Complex.exp (-(c : ℂ) * (t : ℂ)) *
            Complex.exp (((Real.pi * ξ * t : ℝ) : ℂ) * I) := by
    intro ξ
    let q : ℂ := -(((c : ℝ) : ℂ) - ((Real.pi * ξ : ℝ) : ℂ) * I)
    have hq : q.re < 0 := by
      dsimp only [q]
      simp [Complex.mul_re]
      exact hc
    have hfun : (fun t : ℝ =>
        Complex.exp (-(c : ℂ) * (t : ℂ)) *
          Complex.exp (((Real.pi * ξ * t : ℝ) : ℂ) * I)) =
        fun t : ℝ => Complex.exp (q * (t : ℂ)) := by
      funext t
      rw [← Complex.exp_add]
      congr 1
      dsimp only [q]
      push_cast
      ring
    rw [hfun, integral_exp_mul_complex_Ioi hq 0]
    simp only [ofReal_zero, mul_zero, exp_zero]
    dsimp only [q]
    rw [show -(((c : ℝ) : ℂ) - ((Real.pi * ξ : ℝ) : ℂ) * I) =
        -1 * (((c : ℝ) : ℂ) - ((Real.pi * ξ : ℝ) : ℂ) * I) by ring]
    field_simp
  rw [show (fun ξ : ℝ =>
      rectangularTwoEdgeTransform L a
          (1 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) ^ 2 *
        (((c : ℝ) : ℂ) - ((Real.pi * ξ : ℝ) : ℂ) * I)⁻¹) =
      fun ξ : ℝ => F ξ *
        ∫ t : ℝ in Ioi 0,
          Complex.exp (-(c : ℂ) * (t : ℂ)) *
            Complex.exp (((Real.pi * ξ * t : ℝ) : ℂ) * I) by
    funext ξ
    rw [hresolvent ξ]
    ]
  calc
    (∫ ξ : ℝ, F ξ *
        ∫ t : ℝ in Ioi 0,
          Complex.exp (-(c : ℂ) * (t : ℂ)) *
            Complex.exp (((Real.pi * ξ * t : ℝ) : ℂ) * I)) =
        ∫ ξ : ℝ, ∫ t : ℝ, K (t, ξ) := by
      congr with ξ
      rw [← integral_indicator measurableSet_Ioi]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      by_cases ht : t ∈ Ioi (0 : ℝ)
      · simp only [K, e, Set.indicator_of_mem ht]
        ring
      · simp [K, e, ht]
    _ = ∫ t : ℝ, ∫ ξ : ℝ, K (t, ξ) := by
      apply integral_integral_swap
      change Integrable (K ∘ Prod.swap) (volume.prod volume)
      exact hK.swap
    _ = ∫ t : ℝ in Ioi 0,
        Complex.exp (-(c : ℂ) * (t : ℂ)) *
          ((rectangularTwoEdgeAutocorrelation L a (t / 2) : ℂ) *
            Complex.exp (t / 2)) := by
      rw [← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      filter_upwards with t
      by_cases ht : t ∈ Ioi (0 : ℝ)
      · rw [Set.indicator_of_mem ht]
        rw [show (fun ξ : ℝ => K (t, ξ)) = fun ξ : ℝ =>
            Complex.exp (-(c : ℂ) * (t : ℂ)) *
              (Complex.exp ((((2 * Real.pi * ξ * (t / 2) : ℝ) : ℂ)) * I) *
                F ξ) by
          funext ξ
          dsimp only [K]
          rw [show e t = Complex.exp (-(c : ℂ) * (t : ℂ)) by
            simp [e, ht]]
          push_cast
          ring]
        rw [integral_const_mul, integral_rectangularEulerFourierKernel hL a (t / 2)]
        push_cast
        rfl
      · rw [Set.indicator_of_notMem ht]
        have he0 : e t = 0 := Set.indicator_of_notMem ht _
        simp [K, he0]

/-- The vertical resolvent multiplier is bounded, so its product with the rectangular Fourier
square is absolutely integrable. -/
theorem integrable_rectangularEulerFourierKernel_mul_verticalResolvent
    {c : ℝ} (hc : 0 < c) (L a : ℝ) :
    Integrable (fun ξ : ℝ =>
      rectangularTwoEdgeTransform L a
          (1 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) ^ 2 *
        (((c : ℝ) : ℂ) - ((Real.pi * ξ : ℝ) : ℂ) * I)⁻¹) := by
  let F : ℝ → ℂ := fun ξ =>
    rectangularTwoEdgeTransform L a
      (1 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) ^ 2
  let d : ℝ → ℂ := fun ξ =>
    ((c : ℂ) - ((Real.pi * ξ : ℝ) : ℂ) * I)⁻¹
  have hF : Integrable F := by
    simpa only [F] using integrable_rectangularTwoEdgeTransform_eulerLine_sq L a
  have hdenne : ∀ ξ : ℝ,
      (c : ℂ) - ((Real.pi * ξ : ℝ) : ℂ) * I ≠ 0 := by
    intro ξ h
    have hre := congrArg Complex.re h
    simp [Complex.mul_re] at hre
    linarith
  have hdcont : Continuous d := by
    dsimp only [d]
    exact (by fun_prop : Continuous (fun ξ : ℝ =>
      (c : ℂ) - ((Real.pi * ξ : ℝ) : ℂ) * I)).inv₀ hdenne
  have hdbound : ∀ ξ : ℝ, ‖d ξ‖ ≤ 1 / c := by
    intro ξ
    have hre : c ≤ ‖(c : ℂ) - ((Real.pi * ξ : ℝ) : ℂ) * I‖ := by
      have h := Complex.re_le_norm ((c : ℂ) - ((Real.pi * ξ : ℝ) : ℂ) * I)
      simpa [Complex.mul_re] using h
    dsimp only [d]
    rw [norm_inv]
    simpa only [one_div] using one_div_le_one_div_of_le hc hre
  simpa only [F, d] using
    hF.mul_bdd hdcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hdbound)

theorem integrable_rectangularEulerFourierKernel_mul_gaussDigammaSeriesTerm
    (L a : ℝ) (n : ℕ) :
    Integrable (fun ξ : ℝ =>
      rectangularTwoEdgeTransform L a
          (1 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) ^ 2 *
        gaussDigammaSeriesTerm
          (((3 / 4 : ℝ) : ℂ) - ((Real.pi * ξ : ℝ) : ℂ) * I) n) := by
  let F : ℝ → ℂ := fun ξ =>
    rectangularTwoEdgeTransform L a
      (1 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) ^ 2
  let c : ℝ := (n : ℝ) + 3 / 4
  have hc : 0 < c := by dsimp only [c]; positivity
  have hF : Integrable F := by
    simpa only [F] using integrable_rectangularTwoEdgeTransform_eulerLine_sq L a
  have hconst : Integrable (fun ξ : ℝ => F ξ * (1 / ((n : ℂ) + 1))) :=
    hF.mul_const _
  have hres : Integrable (fun ξ : ℝ =>
      F ξ * (((c : ℝ) : ℂ) - ((Real.pi * ξ : ℝ) : ℂ) * I)⁻¹) := by
    simpa only [F] using
      integrable_rectangularEulerFourierKernel_mul_verticalResolvent hc L a
  apply (hconst.sub hres).congr
  filter_upwards with ξ
  simp only [Pi.sub_apply, F, c, gaussDigammaSeriesTerm]
  push_cast
  ring

/-- One Gauss-series summand paired with the rectangular Fourier square is the difference between
the zero-lag autocorrelation and one positive vertical-resolvent Laplace value. -/
theorem integral_rectangularEulerFourierKernel_mul_gaussDigammaSeriesTerm
    {L : ℝ} (hL : 0 ≤ L) (a : ℝ) (n : ℕ) :
    (∫ ξ : ℝ,
        rectangularTwoEdgeTransform L a
            (1 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) ^ 2 *
          gaussDigammaSeriesTerm
            (((3 / 4 : ℝ) : ℂ) - ((Real.pi * ξ : ℝ) : ℂ) * I) n) =
      (rectangularTwoEdgeAutocorrelation L a 0 : ℂ) / ((n : ℂ) + 1) -
        ∫ t : ℝ in Ioi 0,
          Complex.exp (-(((n : ℝ) + 3 / 4 : ℝ) : ℂ) * (t : ℂ)) *
            ((rectangularTwoEdgeAutocorrelation L a (t / 2) : ℂ) *
              Complex.exp (t / 2)) := by
  let F : ℝ → ℂ := fun ξ =>
    rectangularTwoEdgeTransform L a
      (1 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) ^ 2
  let c : ℝ := (n : ℝ) + 3 / 4
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  have hF : Integrable F := by
    simpa only [F] using integrable_rectangularTwoEdgeTransform_eulerLine_sq L a
  have hconst : Integrable (fun ξ : ℝ => F ξ * (1 / ((n : ℂ) + 1))) :=
    hF.mul_const _
  have hres : Integrable (fun ξ : ℝ =>
      F ξ * (((c : ℝ) : ℂ) - ((Real.pi * ξ : ℝ) : ℂ) * I)⁻¹) := by
    simpa only [F] using
      integrable_rectangularEulerFourierKernel_mul_verticalResolvent hc L a
  have hzero := integral_rectangularEulerFourierKernel hL a 0
  have hFzero : (∫ ξ : ℝ, F ξ) =
      (rectangularTwoEdgeAutocorrelation L a 0 : ℂ) := by
    simpa only [F, mul_zero, ofReal_zero, zero_mul, Complex.exp_zero, one_mul,
      mul_one, zero_div] using hzero
  rw [show (fun ξ : ℝ =>
      rectangularTwoEdgeTransform L a
          (1 - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) ^ 2 *
        gaussDigammaSeriesTerm
          (((3 / 4 : ℝ) : ℂ) - ((Real.pi * ξ : ℝ) : ℂ) * I) n) =
      fun ξ : ℝ => F ξ * (1 / ((n : ℂ) + 1)) -
        F ξ * (((c : ℝ) : ℂ) - ((Real.pi * ξ : ℝ) : ℂ) * I)⁻¹ by
    funext ξ
    simp only [F, c, gaussDigammaSeriesTerm]
    push_cast
    ring]
  rw [integral_sub hconst hres, integral_mul_const, hFzero,
    integral_rectangularEulerFourierKernel_mul_verticalResolvent hL hc a]
  dsimp only [c]
  push_cast
  ring

end RHTower
