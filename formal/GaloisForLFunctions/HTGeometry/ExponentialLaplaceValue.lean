import GaloisForLFunctions.HTGeometry.HalfLineScaling

/-!
# The Laplace transform of the mean-one exponential law

The transport layer compares the Laplace transforms of the arithmetic clocks with those of the
mean-one exponential law.  This file computes the latter: it is `1 / (1 + u)`, the limit the
critical boundary-layer statement produces.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The exponential law is the Lebesgue measure weighted by the exponential density. -/
theorem expMeasure_one_eq_withDensity :
    expMeasure 1 = volume.withDensity (exponentialPDF 1) := rfl

/-- The integral of a decaying exponential over the half line. -/
theorem integral_exp_neg_mul_Ioi_zero {b : ℝ} (hb : 0 < b) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(b * x))) = 1 / b := by
  have h := integral_comp_mul_left_Ioi (fun y : ℝ => Real.exp (-y)) 0 hb
  simp only [mul_zero] at h
  rw [h, integral_exp_neg_Ioi_zero, smul_eq_mul, mul_one, one_div]

/-- The lower integral of a decaying exponential over the half line. -/
theorem lintegral_exp_neg_mul_Ioi_zero {b : ℝ} (hb : 0 < b) :
    (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(b * x)))) = ENNReal.ofReal (1 / b) := by
  rw [← integral_exp_neg_mul_Ioi_zero hb]
  refine (ofReal_integral_eq_lintegral_ofReal ?_ ?_).symm
  · exact (exp_neg_integrableOn_Ioi 0 hb).congr_fun (fun x _ => by simp [neg_mul])
      measurableSet_Ioi
  · exact Filter.Eventually.of_forall fun x => (Real.exp_pos _).le

/-- **The Laplace transform of the mean-one exponential law.** -/
theorem lintegral_exp_neg_expMeasure_one {u : ℝ} (hu : 0 ≤ u) :
    (∫⁻ y, ENNReal.ofReal (Real.exp (-(u * y))) ∂(expMeasure 1))
      = ENNReal.ofReal (1 / (1 + u)) := by
  have hb : (0 : ℝ) < 1 + u := by linarith
  have hmeasPDF : Measurable (exponentialPDF 1) :=
    (measurable_exponentialPDFReal 1).ennreal_ofReal
  have hmeasExp : Measurable fun y : ℝ => ENNReal.ofReal (Real.exp (-(u * y))) :=
    (Real.measurable_exp.comp ((measurable_const.mul measurable_id).neg)).ennreal_ofReal
  rw [expMeasure_one_eq_withDensity,
    lintegral_withDensity_eq_lintegral_mul _ hmeasPDF hmeasExp]
  have hsplit : (∫⁻ y, (exponentialPDF 1 * fun y : ℝ => ENNReal.ofReal (Real.exp (-(u * y)))) y)
      = ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-((1 + u) * y))) := by
    rw [← lintegral_add_compl _ measurableSet_Ioi]
    have hzero : (∫⁻ y in (Ioi (0 : ℝ))ᶜ,
        (exponentialPDF 1 * fun y : ℝ => ENNReal.ofReal (Real.exp (-(u * y)))) y) = 0 := by
      rw [compl_Ioi, setLIntegral_congr (Iio_ae_eq_Iic (a := (0 : ℝ))).symm]
      refine setLIntegral_eq_zero measurableSet_Iio fun y hy => ?_
      simp [Pi.mul_apply, exponentialPDF_of_neg hy]
    rw [hzero, add_zero]
    refine setLIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    rw [Pi.mul_apply, exponentialPDF_of_nonneg (le_of_lt hy), one_mul,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    ring_nf
  rw [hsplit, lintegral_exp_neg_mul_Ioi_zero hb]

/-- **The Laplace transform of the mean-one exponential law, as a real integral.** -/
theorem integral_exp_neg_expMeasure_one {u : ℝ} (hu : 0 ≤ u) :
    (∫ y, Real.exp (-(u * y)) ∂(expMeasure 1)) = 1 / (1 + u) := by
  haveI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  have hb : (0 : ℝ) < 1 + u := by linarith
  have hnn : 0 ≤ᵐ[expMeasure 1] fun y => Real.exp (-(u * y)) :=
    Filter.Eventually.of_forall fun y => (Real.exp_pos _).le
  have hmeas : AEStronglyMeasurable (fun y : ℝ => Real.exp (-(u * y))) (expMeasure 1) :=
    (Real.measurable_exp.comp ((measurable_const.mul measurable_id).neg)).aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas, lintegral_exp_neg_expMeasure_one hu,
    ENNReal.toReal_ofReal (by positivity)]

/-- **Critical transport from the explicit boundary-layer limits.**  Half-line laws whose Laplace
transforms converge at every natural argument to `1/(1+k)` — the mean-one exponential value the
critical boundary-layer statement produces — and whose means converge to one, have monotone
couplings with the exponential law of vanishing transport cost. -/
theorem tendsto_integral_monotoneCoupling_of_tendsto_laplace_value {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] (μs : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μs i)]
    (hsupp : ∀ i, (μs i) (Iio 0) = 0) (hint : ∀ i, Integrable (id : ℝ → ℝ) (μs i))
    (hlap : ∀ k : ℕ, Tendsto (fun i => ∫ x, Real.exp (-((k : ℝ) * x)) ∂(μs i)) l
      (𝓝 (1 / (1 + (k : ℝ)))))
    (hmean : Tendsto (fun i => ∫ x, x ∂(μs i)) l (𝓝 1)) :
    Tendsto (fun i => ∫ z, |z.1 - z.2| ∂(monotoneCoupling (μs i) (expMeasure 1))) l (𝓝 0) := by
  refine tendsto_integral_monotoneCoupling_of_tendsto_laplace μs hsupp hint ?_ hmean
  intro k
  rw [integral_exp_neg_expMeasure_one (by positivity : (0 : ℝ) ≤ (k : ℝ))]
  exact hlap k

/-- **The critical two-clock transport statement.**  Two families of half-line laws whose Laplace
transforms converge at every natural argument to the mean-one exponential values `1/(1+k)` and
whose means converge to one are coupled to each other, by their monotone coupling, with vanishing
transport cost.  This is the closed form of the card's critical transport claim: its hypotheses are
exactly the boundary-layer limit and the first-moment limit. -/
theorem tendsto_integral_monotoneCoupling_pair_of_tendsto_laplace_value {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] (μs κs : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μs i)] [∀ i, IsProbabilityMeasure (κs i)]
    (hsuppμ : ∀ i, (μs i) (Iio 0) = 0) (hsuppκ : ∀ i, (κs i) (Iio 0) = 0)
    (hintμ : ∀ i, Integrable (id : ℝ → ℝ) (μs i)) (hintκ : ∀ i, Integrable (id : ℝ → ℝ) (κs i))
    (hlapμ : ∀ k : ℕ, Tendsto (fun i => ∫ x, Real.exp (-((k : ℝ) * x)) ∂(μs i)) l
      (𝓝 (1 / (1 + (k : ℝ)))))
    (hlapκ : ∀ k : ℕ, Tendsto (fun i => ∫ x, Real.exp (-((k : ℝ) * x)) ∂(κs i)) l
      (𝓝 (1 / (1 + (k : ℝ)))))
    (hmeanμ : Tendsto (fun i => ∫ x, x ∂(μs i)) l (𝓝 1))
    (hmeanκ : Tendsto (fun i => ∫ x, x ∂(κs i)) l (𝓝 1)) :
    Tendsto (fun i => ∫ z, |z.1 - z.2| ∂(monotoneCoupling (μs i) (κs i))) l (𝓝 0) := by
  haveI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  exact tendsto_integral_monotoneCoupling_pair μs κs (expMeasure 1) hintμ hintκ
    integrable_id_expMeasure_one
    (tendsto_integral_monotoneCoupling_of_tendsto_laplace_value μs hsuppμ hintμ hlapμ hmeanμ)
    (tendsto_integral_monotoneCoupling_of_tendsto_laplace_value κs hsuppκ hintκ hlapκ hmeanκ)

/-- **The `W₁` form of the critical transport statement.**  Half-line laws whose Laplace transforms
converge at every natural argument to the mean-one exponential values and whose means converge to
one converge to the exponential law in the half-line transport distance. -/
theorem tendsto_halfLineW1_expMeasure_one_of_tendsto_laplace_value {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] (μs : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μs i)]
    (hsupp : ∀ i, (μs i) (Iio 0) = 0) (hint : ∀ i, Integrable (id : ℝ → ℝ) (μs i))
    (hlap : ∀ k : ℕ, Tendsto (fun i => ∫ x, Real.exp (-((k : ℝ) * x)) ∂(μs i)) l
      (𝓝 (1 / (1 + (k : ℝ)))))
    (hmean : Tendsto (fun i => ∫ x, x ∂(μs i)) l (𝓝 1)) :
    Tendsto (fun i => halfLineW1 (μs i) (expMeasure 1)) l (𝓝 0) := by
  haveI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  have hcdf : ∀ t : ℝ, Tendsto (fun i => cdf (μs i) t) l (𝓝 (cdf (expMeasure 1) t)) := by
    refine tendsto_cdf_expMeasure_one_of_tendsto_laplace μs hsupp fun k => ?_
    rw [integral_exp_neg_expMeasure_one (by positivity : (0 : ℝ) ≤ (k : ℝ))]
    exact hlap k
  refine tendsto_halfLineW1_of_tendsto_survival μs (expMeasure 1) hint
    (fun i => ae_nonneg_of_Iio_zero (hsupp i)) integrable_id_expMeasure_one
    expMeasure_one_nonneg_ae ?_ ?_
  · refine Filter.Eventually.of_forall fun t => ?_
    have h := (tendsto_const_nhds (x := (1 : ℝ)) (f := l)).sub (hcdf t)
    simpa only [survival_eq_one_sub_cdf] using h
  · rw [integral_id_expMeasure_one]
    exact hmean

end

end GaloisForLFunctions.HTGeometry
