import GaloisForLFunctions.HTGeometry.QuadraticTransportCost

/-!
# Second moments of arithmetic clocks

The quadratic transport layer consumes one arithmetic input per clock: the second moment of the
thermally scaled law.  For a logarithmic clock that moment is the second logarithmic Dirichlet
sum, which is the second derivative of the `L`-series of the weight.

The identification of the sum with the second derivative is the derivative formula
`(LSeries f)' = -LSeries (log · f)` applied twice; the second application needs the first to hold
on a whole half plane, which the abscissa of absolute convergence supplies.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology ArithmeticFunction

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### Second moment of a logarithmic clock -/

/-- A logarithmic clock whose squared logarithmic series converges has a finite second moment. -/
theorem integrable_sq_logClockLaw {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (hsum : Summable fun n : ℕ => w n * Real.log n ^ 2) :
    Integrable (fun x : ℝ => x ^ 2) (logClockLaw w) := by
  refine integrable_weightedPointLaw _ _ (fun n => ENNReal.ofReal_ne_top) ?_
  refine hsum.congr fun n => ?_
  rw [ENNReal.toReal_ofReal (hw n), Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]

/-- **Second moment of a logarithmic clock law.**  It is the squared logarithmic weighted sum. -/
theorem integral_sq_logClockLaw {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (hint : Integrable (fun x : ℝ => x ^ 2) (logClockLaw w)) :
    (∫ y, y ^ 2 ∂(logClockLaw w)) = ∑' n : ℕ, w n * Real.log n ^ 2 := by
  have h := integral_weightedPointLaw (fun n : ℕ => Real.log n)
    (fun n => ENNReal.ofReal (w n)) hint
  rw [logClockLaw, h]
  exact tsum_congr fun n => by rw [ENNReal.toReal_ofReal (hw n)]

/-! ### Second moment of a Dirichlet clock -/

variable {f : ℕ → ℝ} {σ : ℝ}

/-- A Dirichlet clock whose squared logarithmic series converges has a finite second moment. -/
theorem integrable_sq_dirichletClockLaw (hf : ∀ n, 0 ≤ f n) (hpos : 0 < dirichletTotal f σ)
    (hlog : Summable fun n : ℕ => (Real.log n ^ 2 * f n) * (n : ℝ) ^ (-σ)) :
    Integrable (fun x : ℝ => x ^ 2) (dirichletClockLaw f σ) := by
  rw [dirichletClockLaw]
  refine integrable_sq_logClockLaw (dirichletClockWeight_nonneg hf hpos) ?_
  refine (hlog.div_const (dirichletTotal f σ)).congr fun n => ?_
  simp only [dirichletClockWeight]
  ring

/-- **The second moment of a Dirichlet clock is the ratio of the squared logarithmic total to the
plain total.** -/
theorem integral_sq_dirichletClockLaw (hf : ∀ n, 0 ≤ f n) (hpos : 0 < dirichletTotal f σ)
    (hlog : Summable fun n : ℕ => (Real.log n ^ 2 * f n) * (n : ℝ) ^ (-σ)) :
    (∫ y, y ^ 2 ∂(dirichletClockLaw f σ))
      = (∑' n : ℕ, (Real.log n ^ 2 * f n) * (n : ℝ) ^ (-σ)) / dirichletTotal f σ := by
  rw [dirichletClockLaw, integral_sq_logClockLaw (dirichletClockWeight_nonneg hf hpos)
    (by rw [← dirichletClockLaw]; exact integrable_sq_dirichletClockLaw hf hpos hlog),
    ← tsum_div_const]
  refine tsum_congr fun n => ?_
  simp only [dirichletClockWeight]
  ring

/-! ### Second moment under rescaling -/

/-- **Rescaling multiplies the second moment by the square of the scale.** -/
theorem integral_sq_scaleLaw (c : ℝ) (μ : Measure ℝ) :
    (∫ y, y ^ 2 ∂(scaleLaw c μ)) = c ^ 2 * ∫ x, x ^ 2 ∂μ := by
  rw [scaleLaw]
  have h : ∫ (y : ℝ), y ^ 2 ∂(Measure.map (fun x : ℝ => c * x) μ) = ∫ x, (c * x) ^ 2 ∂μ :=
    integral_map (measurable_scale c).aemeasurable
      (measurable_id.pow_const 2).aestronglyMeasurable
  rw [h, ← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [mul_pow])

/-- A rescaled law with a finite second moment has a finite second moment. -/
theorem integrable_sq_scaleLaw (c : ℝ) {μ : Measure ℝ}
    (hint : Integrable (fun x : ℝ => x ^ 2) μ) :
    Integrable (fun x : ℝ => x ^ 2) (scaleLaw c μ) := by
  rw [scaleLaw]
  refine (integrable_map_measure (measurable_id.pow_const 2).aestronglyMeasurable
    (measurable_scale c).aemeasurable).mpr ?_
  exact (hint.const_mul (c ^ 2)).congr
    (Filter.Eventually.of_forall fun x => by simp [mul_pow])

/-! ### The second logarithmic Dirichlet series -/

/-- The coefficients of the twice logarithmically multiplied `L`-series. -/
theorem logMul_logMul_ofReal (g : ℕ → ℝ) :
    (LSeries.logMul (LSeries.logMul fun n => ((g n : ℝ) : ℂ)))
      = fun n : ℕ => ((Real.log n ^ 2 * g n : ℝ) : ℂ) := by
  funext n
  have hlogn : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast n, ← Complex.ofReal_log (Nat.cast_nonneg n)]
  simp only [LSeries.logMul, hlogn, ← Complex.ofReal_mul]
  norm_cast
  ring

/-- The squared logarithmic Dirichlet series of a real weight converges past its abscissa. -/
theorem summable_logSq_mul_rpow {g : ℕ → ℝ}
    (habs : LSeries.abscissaOfAbsConv (fun n => ((g n : ℝ) : ℂ)) < ((σ : ℂ)).re) :
    Summable fun n : ℕ => (Real.log n ^ 2 * g n) * (n : ℝ) ^ (-σ) := by
  have h1 : LSeriesSummable (LSeries.logMul (LSeries.logMul fun n => ((g n : ℝ) : ℂ)))
      (σ : ℂ) := by
    refine LSeriesSummable_logMul_of_lt_re ?_
    rwa [LSeries.abscissaOfAbsConv_logMul]
  rw [logMul_logMul_ofReal] at h1
  exact summable_real_of_lseriesSummable (by simp) h1

/-- **The squared logarithmic Dirichlet sum is the second derivative of the `L`-series.**  The
derivative formula is applied twice, the first time on a whole half plane. -/
theorem ofReal_tsum_logSq_mul_eq {g : ℕ → ℝ} {a : ℝ} (ha : a < σ)
    (habs : LSeries.abscissaOfAbsConv (fun n => ((g n : ℝ) : ℂ)) ≤ (a : EReal)) :
    ((∑' n : ℕ, (Real.log n ^ 2 * g n) * (n : ℝ) ^ (-σ) : ℝ) : ℂ)
      = deriv (deriv (LSeries fun n => ((g n : ℝ) : ℂ))) (σ : ℂ) := by
  have hmem : ∀ s : ℂ, a < s.re →
      LSeries.abscissaOfAbsConv (fun n => ((g n : ℝ) : ℂ)) < (s.re : EReal) := by
    intro s hs
    refine lt_of_le_of_lt habs ?_
    exact_mod_cast hs
  have hopen : IsOpen {s : ℂ | a < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hσmem : (σ : ℂ) ∈ {s : ℂ | a < s.re} := by simpa using ha
  have hderiv2 : deriv (deriv (LSeries fun n => ((g n : ℝ) : ℂ))) (σ : ℂ)
      = deriv (fun s => -LSeries (LSeries.logMul fun n => ((g n : ℝ) : ℂ)) s) (σ : ℂ) := by
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [hopen.mem_nhds hσmem] with s hs
    exact LSeries_deriv (hmem s hs)
  have habs' : LSeries.abscissaOfAbsConv (LSeries.logMul fun n => ((g n : ℝ) : ℂ))
      < ((σ : ℂ)).re := by
    rw [LSeries.abscissaOfAbsConv_logMul]
    exact hmem (σ : ℂ) (by simpa using ha)
  have hneg : deriv (fun s => -LSeries (LSeries.logMul fun n => ((g n : ℝ) : ℂ)) s) (σ : ℂ)
      = -deriv (LSeries (LSeries.logMul fun n => ((g n : ℝ) : ℂ))) (σ : ℂ) := deriv.neg
  rw [hderiv2, hneg, LSeries_deriv habs', neg_neg,
    ofReal_tsum_eq_lseries (f := fun n => Real.log n ^ 2 * g n) (by simp)]
  refine congrArg (fun h => LSeries h (σ : ℂ)) ?_
  rw [logMul_logMul_ofReal]

/-! ### The two arithmetic clocks -/

/-- The squared logarithmic von Mangoldt series converges past abscissa one. -/
theorem summable_vonMangoldt_logSq_rpow (hσ : 1 < σ) :
    Summable fun n : ℕ => (Real.log n ^ 2 * Λ n) * (n : ℝ) ^ (-σ) := by
  refine summable_logSq_mul_rpow (g := fun n => Λ n) ?_
  have hmid : (1 : ℝ) < (1 + σ) / 2 := by linarith
  have hsummable : LSeriesSummable (fun n => (Λ n : ℂ)) (((1 + σ) / 2 : ℝ) : ℂ) :=
    LSeriesSummable_vonMangoldt (by simpa using hmid)
  refine lt_of_le_of_lt hsummable.abscissaOfAbsConv_le ?_
  simp only [Complex.ofReal_re]
  exact_mod_cast by linarith

/-- **The squared logarithmic von Mangoldt sum is the second derivative of the von Mangoldt
`L`-series.** -/
theorem ofReal_tsum_vonMangoldt_logSq_eq (hσ : 1 < σ) :
    ((∑' n : ℕ, (Real.log n ^ 2 * Λ n) * (n : ℝ) ^ (-σ) : ℝ) : ℂ)
      = deriv (deriv (LSeries fun n => (Λ n : ℂ))) (σ : ℂ) := by
  have hmid : (1 : ℝ) < (1 + σ) / 2 := by linarith
  have hsummable : LSeriesSummable (fun n => (Λ n : ℂ)) (((1 + σ) / 2 : ℝ) : ℂ) :=
    LSeriesSummable_vonMangoldt (by simpa using hmid)
  refine ofReal_tsum_logSq_mul_eq (g := fun n => Λ n) (a := (1 + σ) / 2) (by linarith) ?_
  simpa using hsummable.abscissaOfAbsConv_le

/-- The squared logarithmic squarefree series converges past abscissa one. -/
theorem summable_squarefreeWeight_logSq_rpow (hσ : 1 < σ) :
    Summable fun n : ℕ => (Real.log n ^ 2 * squarefreeWeight n) * (n : ℝ) ^ (-σ) :=
  summable_logSq_mul_rpow (g := squarefreeWeight) (abscissa_squarefreeWeight_lt hσ)

/-- The Euler clock has a finite second moment. -/
theorem integrable_sq_eulerClockLaw (hσ : 1 < σ) :
    Integrable (fun x : ℝ => x ^ 2) (eulerClockLaw σ) := by
  refine integrable_sq_logClockLaw (eulerClockWeight_nonneg hσ) ?_
  have hsummable := summable_vonMangoldt_logSq_rpow hσ
  refine ((hsummable.div_const (∑' m : ℕ, Λ m * (m : ℝ) ^ (-σ))).congr fun n => ?_)
  simp only [eulerClockWeight]
  ring

/-- **The second moment of the Euler clock is the ratio of the squared logarithmic and plain von
Mangoldt sums.** -/
theorem integral_sq_eulerClockLaw (hσ : 1 < σ) :
    (∫ y, y ^ 2 ∂(eulerClockLaw σ))
      = (∑' n : ℕ, (Real.log n ^ 2 * Λ n) * (n : ℝ) ^ (-σ))
        / ∑' n : ℕ, Λ n * (n : ℝ) ^ (-σ) := by
  rw [eulerClockLaw, integral_sq_logClockLaw (eulerClockWeight_nonneg hσ)
    (by rw [← eulerClockLaw]; exact integrable_sq_eulerClockLaw hσ), ← tsum_div_const]
  refine tsum_congr fun n => ?_
  simp only [eulerClockWeight]
  ring

/-- The squarefree clock has a finite second moment. -/
theorem integrable_sq_squarefreeClockLaw (hσ : 1 < σ) :
    Integrable (fun x : ℝ => x ^ 2) (squarefreeClockLaw σ) :=
  integrable_sq_dirichletClockLaw squarefreeWeight_nonneg
    (dirichletTotal_squarefreeWeight_pos hσ) (summable_squarefreeWeight_logSq_rpow hσ)

/-- **The second moment of the squarefree clock.** -/
theorem integral_sq_squarefreeClockLaw (hσ : 1 < σ) :
    (∫ y, y ^ 2 ∂(squarefreeClockLaw σ))
      = (∑' n : ℕ, (Real.log n ^ 2 * squarefreeWeight n) * (n : ℝ) ^ (-σ))
        / dirichletTotal squarefreeWeight σ :=
  integral_sq_dirichletClockLaw squarefreeWeight_nonneg
    (dirichletTotal_squarefreeWeight_pos hσ) (summable_squarefreeWeight_logSq_rpow hσ)

/-! ### The thermally scaled clocks -/

theorem integrable_sq_scaledEulerClockLaw (hσ : 1 < σ) :
    Integrable (fun x : ℝ => x ^ 2) (scaledEulerClockLaw σ) :=
  integrable_sq_scaleLaw _ (integrable_sq_eulerClockLaw hσ)

theorem integrable_sq_scaledSquarefreeClockLaw (hσ : 1 < σ) :
    Integrable (fun x : ℝ => x ^ 2) (scaledSquarefreeClockLaw σ) :=
  integrable_sq_scaleLaw _ (integrable_sq_squarefreeClockLaw hσ)

/-- **The second moment of the scaled Euler clock.** -/
theorem integral_sq_scaledEulerClockLaw (hσ : 1 < σ) :
    (∫ y, y ^ 2 ∂(scaledEulerClockLaw σ))
      = (σ - 1) ^ 2 * ((∑' n : ℕ, (Real.log n ^ 2 * Λ n) * (n : ℝ) ^ (-σ))
        / ∑' n : ℕ, Λ n * (n : ℝ) ^ (-σ)) := by
  rw [scaledEulerClockLaw, integral_sq_scaleLaw, integral_sq_eulerClockLaw hσ]

/-- **The second moment of the scaled squarefree clock.** -/
theorem integral_sq_scaledSquarefreeClockLaw (hσ : 1 < σ) :
    (∫ y, y ^ 2 ∂(scaledSquarefreeClockLaw σ))
      = (σ - 1) ^ 2 * ((∑' n : ℕ, (Real.log n ^ 2 * squarefreeWeight n) * (n : ℝ) ^ (-σ))
        / dirichletTotal squarefreeWeight σ) := by
  rw [scaledSquarefreeClockLaw, integral_sq_scaleLaw, integral_sq_squarefreeClockLaw hσ]

end

end GaloisForLFunctions.HTGeometry
