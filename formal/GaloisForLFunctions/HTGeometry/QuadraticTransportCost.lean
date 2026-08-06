import GaloisForLFunctions.HTGeometry.ExponentialLaplaceValue

/-!
# Quadratic transport cost of the monotone coupling

The first-order transport layer compares half-line laws through the `L¹` cost of their monotone
coupling.  This file carries the same comparison to second order.

The mechanism is one pointwise inequality: for nonnegative reals `|a - b|² ≤ |a² - b²|`.  It turns
the `L²` cost into an `L¹` cost of the squared quantile functions, where the Scheffé cancellation
of the first-order layer applies verbatim.  Consequently a family of half-line laws whose
distribution functions converge to the mean-one exponential law and whose second moments converge
to `2` is coupled to it with vanishing quadratic cost, and two such families are coupled to each
other.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### Two elementary inequalities -/

/-- For nonnegative reals the squared distance is dominated by the distance of the squares. -/
theorem sq_abs_sub_le_abs_sq_sub {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |a - b| ^ 2 ≤ |a ^ 2 - b ^ 2| := by
  have hle : |a - b| ≤ a + b := abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  have hsum : (0 : ℝ) ≤ a + b := by linarith
  calc |a - b| ^ 2 = |a - b| * |a - b| := sq _
    _ ≤ |a - b| * (a + b) := mul_le_mul_of_nonneg_left hle (abs_nonneg _)
    _ = |(a - b) * (a + b)| := by rw [abs_mul, abs_of_nonneg hsum]
    _ = |a ^ 2 - b ^ 2| := by
        congr 1
        ring

/-- The quadratic triangle inequality with the parallelogram constant. -/
theorem sq_abs_sub_le_two_mul_add (a b c : ℝ) :
    |a - c| ^ 2 ≤ 2 * |a - b| ^ 2 + 2 * |b - c| ^ 2 := by
  rw [sq_abs, sq_abs, sq_abs]
  nlinarith [sq_nonneg (a - 2 * b + c)]

/-- The squared distance is dominated by twice the sum of the squares. -/
theorem sq_abs_sub_le_two_mul_sq_add (a b : ℝ) : |a - b| ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  rw [sq_abs]
  nlinarith [sq_nonneg (a + b)]

/-! ### Scheffé cancellation at second order -/

/-- **Quadratic Scheffé cancellation.**  Nonnegative integrands converging almost everywhere with
converging squared integrals converge in `L²`.  The proof applies the first-order cancellation to
the squares and then the pointwise domination of the squared distance. -/
theorem tendsto_integral_sq_sub_of_tendsto {α : Type*} [MeasurableSpace α] {m : Measure α}
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {f : ι → α → ℝ} {g : α → ℝ}
    (hfm : ∀ i, AEStronglyMeasurable (f i) m) (hgm : AEStronglyMeasurable g m)
    (hfi : ∀ i, Integrable (fun x => f i x ^ 2) m) (hgi : Integrable (fun x => g x ^ 2) m)
    (hfnn : ∀ i, 0 ≤ᵐ[m] f i) (hgnn : 0 ≤ᵐ[m] g)
    (hae : ∀ᵐ x ∂m, Tendsto (fun i => f i x) l (𝓝 (g x)))
    (hint : Tendsto (fun i => ∫ x, f i x ^ 2 ∂m) l (𝓝 (∫ x, g x ^ 2 ∂m))) :
    Tendsto (fun i => ∫ x, |f i x - g x| ^ 2 ∂m) l (𝓝 0) := by
  have hsq : Tendsto (fun i => ∫ x, |f i x ^ 2 - g x ^ 2| ∂m) l (𝓝 0) := by
    refine tendsto_integral_abs_sub_of_tendsto hfi hgi
      (fun i => Filter.Eventually.of_forall fun x => sq_nonneg _)
      (Filter.Eventually.of_forall fun x => sq_nonneg _) ?_ hint
    filter_upwards [hae] with x hx
    exact hx.pow 2
  have hbound : ∀ i, ∀ᵐ x ∂m, |f i x - g x| ^ 2 ≤ |f i x ^ 2 - g x ^ 2| := by
    intro i
    filter_upwards [hfnn i, hgnn] with x hx hgx
    exact sq_abs_sub_le_abs_sq_sub hx hgx
  have hmeasDiff : ∀ i, AEStronglyMeasurable (fun x => |f i x - g x| ^ 2) m := by
    intro i
    exact (((hfm i).sub hgm).pow 2).congr
      (Filter.Eventually.of_forall fun x => (sq_abs (f i x - g x)).symm)
  have hdiffInt : ∀ i, Integrable (fun x => |f i x - g x| ^ 2) m := by
    intro i
    refine Integrable.mono ((hfi i).sub hgi).abs (hmeasDiff i) ?_
    filter_upwards [hbound i] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), abs_abs]
    exact hx
  refine squeeze_zero (fun i => integral_nonneg fun x => sq_nonneg _) (fun i => ?_) hsq
  exact integral_mono_ae (hdiffInt i) ((hfi i).sub hgi).abs (hbound i)

/-! ### The quadratic cost of the monotone coupling -/

/-- **Quadratic transport cost of the monotone coupling.**  It is the `L²` distance of the two
quantile functions. -/
theorem integral_monotoneCoupling_sq_sub (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    (∫ z, |z.1 - z.2| ^ 2 ∂(monotoneCoupling μ ν))
      = ∫ p in Ioo (0 : ℝ) 1, |quantile μ p - quantile ν p| ^ 2 := by
  have h : ∫ (z : ℝ × ℝ), |z.1 - z.2| ^ 2 ∂(Measure.map (fun p => (quantile μ p, quantile ν p))
        (volume.restrict (Ioo (0 : ℝ) 1)))
      = ∫ p, |quantile μ p - quantile ν p| ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) 1)) :=
    integral_map (measurable_quantilePair μ ν).aemeasurable
      ((measurable_fst.sub measurable_snd).abs.pow_const 2).aestronglyMeasurable
  rw [monotoneCoupling]
  exact h

/-- A law with a finite second moment has a square-integrable quantile function. -/
theorem integrableOn_quantile_sq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (fun x : ℝ => x ^ 2) μ) :
    IntegrableOn (fun p => quantile μ p ^ 2) (Ioo (0 : ℝ) 1) := by
  have hmap : Integrable (fun x : ℝ => x ^ 2)
      (Measure.map (quantile μ) (volume.restrict (Ioo (0 : ℝ) 1))) := by
    rwa [map_quantile_eq μ]
  exact (integrable_map_measure (measurable_id.pow_const 2).aestronglyMeasurable
    (measurable_quantile μ).aemeasurable).mp hmap

/-- The second moment of a law is the integral of the square of its quantile function. -/
theorem integral_quantile_sq_eq_second_moment (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∫ p in Ioo (0 : ℝ) 1, quantile μ p ^ 2 = ∫ x, x ^ 2 ∂μ := by
  have h : ∫ (y : ℝ), y ^ 2 ∂(Measure.map (quantile μ) (volume.restrict (Ioo (0 : ℝ) 1)))
      = ∫ p, quantile μ p ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) 1)) :=
    integral_map (measurable_quantile μ).aemeasurable
      (measurable_id.pow_const 2).aestronglyMeasurable
  rw [map_quantile_eq μ] at h
  exact h.symm

/-- The squared distance of two square-integrable quantile functions is integrable. -/
theorem integrableOn_quantile_sub_sq (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : Integrable (fun x : ℝ => x ^ 2) μ)
    (hν : Integrable (fun x : ℝ => x ^ 2) ν) :
    IntegrableOn (fun p => |quantile μ p - quantile ν p| ^ 2) (Ioo (0 : ℝ) 1) := by
  refine Integrable.mono (((integrableOn_quantile_sq μ hμ).const_mul 2).add
    ((integrableOn_quantile_sq ν hν).const_mul 2))
    (((measurable_quantile μ).sub (measurable_quantile ν)).abs.pow_const
      2).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun p => ?_
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * quantile μ p ^ 2 + 2 * quantile ν p ^ 2)]
  exact sq_abs_sub_le_two_mul_sq_add _ _

/-- **Vanishing quadratic monotone-coupling cost.**  If the quantile functions converge almost
everywhere on `(0,1)` and the second moments converge, the quadratic transport cost of the
monotone coupling tends to zero. -/
theorem tendsto_integral_monotoneCoupling_sq_sub {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] (μ : ι → Measure ℝ) (ν : Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] [IsProbabilityMeasure ν]
    (hsupp : ∀ i, (μ i) (Iio 0) = 0) (hsuppν : ν (Iio 0) = 0)
    (hint : ∀ i, Integrable (fun x : ℝ => x ^ 2) (μ i))
    (hintν : Integrable (fun x : ℝ => x ^ 2) ν)
    (hae : ∀ᵐ p ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      Tendsto (fun i => quantile (μ i) p) l (𝓝 (quantile ν p)))
    (hmom : Tendsto (fun i => ∫ x, x ^ 2 ∂(μ i)) l (𝓝 (∫ x, x ^ 2 ∂ν))) :
    Tendsto (fun i => ∫ z, |z.1 - z.2| ^ 2 ∂(monotoneCoupling (μ i) ν)) l (𝓝 0) := by
  have hnnν : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] quantile ν :=
    (ae_restrict_iff' measurableSet_Ioo).mpr
      (Filter.Eventually.of_forall fun p hp => quantile_nonneg hsuppν hp.1 hp.2)
  have hnn : ∀ i, 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] quantile (μ i) := fun i =>
    (ae_restrict_iff' measurableSet_Ioo).mpr
      (Filter.Eventually.of_forall fun p hp => quantile_nonneg (hsupp i) hp.1 hp.2)
  have hmomQ : Tendsto (fun i => ∫ p, quantile (μ i) p ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) 1))) l
      (𝓝 (∫ p, quantile ν p ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) 1)))) := by
    rw [integral_quantile_sq_eq_second_moment ν]
    exact hmom.congr fun i => (integral_quantile_sq_eq_second_moment (μ i)).symm
  refine (tendsto_integral_sq_sub_of_tendsto
    (fun i => (measurable_quantile (μ i)).aestronglyMeasurable)
    (measurable_quantile ν).aestronglyMeasurable
    (fun i => integrableOn_quantile_sq (μ i) (hint i)) (integrableOn_quantile_sq ν hintν)
    hnn hnnν hae hmomQ).congr fun i => ?_
  exact (integral_monotoneCoupling_sq_sub (μ i) ν).symm

/-- **Mutual quadratic transport cost.**  Two families of laws each coupled to a common law with
vanishing quadratic cost are coupled to each other with vanishing quadratic cost.  The mechanism is
the quadratic triangle inequality at the level of quantile functions. -/
theorem tendsto_integral_monotoneCoupling_pair_sq {ι : Type*} {l : Filter ι}
    (μ κ : ι → Measure ℝ) (ν : Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (κ i)] [IsProbabilityMeasure ν]
    (hintμ : ∀ i, Integrable (fun x : ℝ => x ^ 2) (μ i))
    (hintκ : ∀ i, Integrable (fun x : ℝ => x ^ 2) (κ i))
    (hintν : Integrable (fun x : ℝ => x ^ 2) ν)
    (hμ : Tendsto (fun i => ∫ z, |z.1 - z.2| ^ 2 ∂(monotoneCoupling (μ i) ν)) l (𝓝 0))
    (hκ : Tendsto (fun i => ∫ z, |z.1 - z.2| ^ 2 ∂(monotoneCoupling (κ i) ν)) l (𝓝 0)) :
    Tendsto (fun i => ∫ z, |z.1 - z.2| ^ 2 ∂(monotoneCoupling (μ i) (κ i))) l (𝓝 0) := by
  have hlim : Tendsto (fun i => 2 * (∫ z, |z.1 - z.2| ^ 2 ∂(monotoneCoupling (μ i) ν))
      + 2 * ∫ z, |z.1 - z.2| ^ 2 ∂(monotoneCoupling (κ i) ν)) l (𝓝 0) := by
    have h := (hμ.const_mul 2).add (hκ.const_mul 2)
    simpa using h
  refine squeeze_zero (fun i => integral_nonneg fun z => sq_nonneg _) (fun i => ?_) hlim
  rw [integral_monotoneCoupling_sq_sub (μ i) (κ i), integral_monotoneCoupling_sq_sub (μ i) ν,
    integral_monotoneCoupling_sq_sub (κ i) ν]
  have hcost : ∫ p in Ioo (0 : ℝ) 1, |quantile (κ i) p - quantile ν p| ^ 2
      = ∫ p in Ioo (0 : ℝ) 1, |quantile ν p - quantile (κ i) p| ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    exact congrArg (fun t : ℝ => t ^ 2) (abs_sub_comm _ _)
  rw [hcost, ← integral_const_mul, ← integral_const_mul, ← integral_add
    ((integrableOn_quantile_sub_sq (μ i) ν (hintμ i) hintν).const_mul 2)
    ((integrableOn_quantile_sub_sq ν (κ i) hintν (hintκ i)).const_mul 2)]
  refine integral_mono_ae (integrableOn_quantile_sub_sq (μ i) (κ i) (hintμ i) (hintκ i))
    (((integrableOn_quantile_sub_sq (μ i) ν (hintμ i) hintν).const_mul 2).add
      ((integrableOn_quantile_sub_sq ν (κ i) hintν (hintκ i)).const_mul 2))
    (Filter.Eventually.of_forall fun p => ?_)
  exact sq_abs_sub_le_two_mul_add _ _ _

/-! ### The second moment of the mean-one exponential law -/

/-- The second-moment integrand of the mean-one exponential law is the third Gamma integrand. -/
theorem integrableOn_exp_neg_mul_sq : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ 2) (Ioi 0) := by
  have h := Real.GammaIntegral_convergent (s := 3) (by norm_num)
  refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp only [show (3 : ℝ) - 1 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- The third Gamma integral. -/
theorem integral_exp_neg_mul_sq_Ioi : (∫ x in Ioi (0 : ℝ), Real.exp (-x) * x ^ 2) = 2 := by
  have hgamma := Real.Gamma_eq_integral (s := 3) (by norm_num)
  have hval : Real.Gamma 3 = 2 := by
    have h := Real.Gamma_nat_eq_factorial 2
    rw [show (3 : ℝ) = ((2 : ℕ) : ℝ) + 1 by norm_num, h]
    norm_num
  have hcongr : (∫ x in Ioi (0 : ℝ), Real.exp (-x) * x ^ ((3 : ℝ) - 1))
      = ∫ x in Ioi (0 : ℝ), Real.exp (-x) * x ^ 2 := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [show (3 : ℝ) - 1 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [← hcongr, ← hgamma, hval]

/-- **The second moment of the mean-one exponential law**, as a lower integral. -/
theorem lintegral_sq_expMeasure_one :
    (∫⁻ x, ENNReal.ofReal (x ^ 2) ∂(expMeasure 1)) = ENNReal.ofReal 2 := by
  have hmeasPDF : Measurable (exponentialPDF 1) :=
    (measurable_exponentialPDFReal 1).ennreal_ofReal
  have hmeasSq : Measurable fun x : ℝ => ENNReal.ofReal (x ^ 2) :=
    (measurable_id.pow_const 2).ennreal_ofReal
  rw [expMeasure_one_eq_withDensity,
    lintegral_withDensity_eq_lintegral_mul _ hmeasPDF hmeasSq]
  have hsplit : (∫⁻ y, (exponentialPDF 1 * fun y : ℝ => ENNReal.ofReal (y ^ 2)) y)
      = ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-y) * y ^ 2) := by
    rw [← lintegral_add_compl _ measurableSet_Ioi]
    have hzero : (∫⁻ y in (Ioi (0 : ℝ))ᶜ,
        (exponentialPDF 1 * fun y : ℝ => ENNReal.ofReal (y ^ 2)) y) = 0 := by
      rw [compl_Ioi, setLIntegral_congr (Iio_ae_eq_Iic (a := (0 : ℝ))).symm]
      refine setLIntegral_eq_zero measurableSet_Iio fun y hy => ?_
      simp [Pi.mul_apply, exponentialPDF_of_neg hy]
    rw [hzero, add_zero]
    refine setLIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    rw [Pi.mul_apply, exponentialPDF_of_nonneg (le_of_lt hy), one_mul,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, one_mul]
  rw [hsplit, ← integral_exp_neg_mul_sq_Ioi,
    ← ofReal_integral_eq_lintegral_ofReal integrableOn_exp_neg_mul_sq
      (Filter.Eventually.of_forall fun x => by positivity)]

/-- The mean-one exponential law has a finite second moment. -/
theorem integrable_sq_expMeasure_one : Integrable (fun x : ℝ => x ^ 2) (expMeasure 1) := by
  refine ⟨(measurable_id.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => sq_nonneg x),
    lintegral_sq_expMeasure_one]
  exact ENNReal.ofReal_lt_top

/-- **The second moment of the mean-one exponential law is two.** -/
theorem integral_sq_expMeasure_one : (∫ x, x ^ 2 ∂(expMeasure 1)) = 2 := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => sq_nonneg x)
      (measurable_id.pow_const 2).aestronglyMeasurable,
    lintegral_sq_expMeasure_one, ENNReal.toReal_ofReal (by norm_num)]

/-! ### The second-order critical transport statements -/

/-- **Vanishing quadratic transport cost against the exponential law.**  Half-line laws whose
distribution functions converge to the mean-one exponential law and whose second moments converge
to two have monotone couplings with vanishing quadratic transport cost. -/
theorem tendsto_integral_monotoneCoupling_sq_expMeasure_one {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hsupp : ∀ i, (μ i) (Iio 0) = 0) (hint : ∀ i, Integrable (fun x : ℝ => x ^ 2) (μ i))
    (hcdf : ∀ t : ℝ, Tendsto (fun i => cdf (μ i) t) l (𝓝 (cdf (expMeasure 1) t)))
    (hmom : Tendsto (fun i => ∫ x, x ^ 2 ∂(μ i)) l (𝓝 2)) :
    Tendsto (fun i => ∫ z, |z.1 - z.2| ^ 2 ∂(monotoneCoupling (μ i) (expMeasure 1))) l (𝓝 0) := by
  haveI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  refine tendsto_integral_monotoneCoupling_sq_sub μ (expMeasure 1) hsupp expMeasure_one_Iio_zero
    hint integrable_sq_expMeasure_one ?_ ?_
  · refine (ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall fun p hp => ?_)
    exact tendsto_quantile_expMeasure_one μ hcdf hp.1 hp.2
  · rw [integral_sq_expMeasure_one]
    exact hmom

/-- **Second-order critical transport from the boundary-layer limits.**  Half-line laws whose
Laplace transforms converge at every natural argument to the mean-one exponential values and whose
second moments converge to two are coupled to the exponential law with vanishing quadratic
cost. -/
theorem tendsto_integral_monotoneCoupling_sq_of_tendsto_laplace_value {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] (μs : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μs i)]
    (hsupp : ∀ i, (μs i) (Iio 0) = 0) (hint : ∀ i, Integrable (fun x : ℝ => x ^ 2) (μs i))
    (hlap : ∀ k : ℕ, Tendsto (fun i => ∫ x, Real.exp (-((k : ℝ) * x)) ∂(μs i)) l
      (𝓝 (1 / (1 + (k : ℝ)))))
    (hmom : Tendsto (fun i => ∫ x, x ^ 2 ∂(μs i)) l (𝓝 2)) :
    Tendsto (fun i => ∫ z, |z.1 - z.2| ^ 2 ∂(monotoneCoupling (μs i) (expMeasure 1))) l (𝓝 0) := by
  refine tendsto_integral_monotoneCoupling_sq_expMeasure_one μs hsupp hint ?_ hmom
  refine tendsto_cdf_expMeasure_one_of_tendsto_laplace μs hsupp fun k => ?_
  rw [integral_exp_neg_expMeasure_one (by positivity : (0 : ℝ) ≤ (k : ℝ))]
  exact hlap k

/-- **The second-order critical two-clock transport statement.**  Two families of half-line laws
whose Laplace transforms converge at every natural argument to the mean-one exponential values and
whose second moments converge to two are coupled to each other, by their monotone coupling, with
vanishing quadratic transport cost. -/
theorem tendsto_integral_monotoneCoupling_pair_sq_of_tendsto_laplace_value {ι : Type*}
    {l : Filter ι} [l.IsCountablyGenerated] (μs κs : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μs i)] [∀ i, IsProbabilityMeasure (κs i)]
    (hsuppμ : ∀ i, (μs i) (Iio 0) = 0) (hsuppκ : ∀ i, (κs i) (Iio 0) = 0)
    (hintμ : ∀ i, Integrable (fun x : ℝ => x ^ 2) (μs i))
    (hintκ : ∀ i, Integrable (fun x : ℝ => x ^ 2) (κs i))
    (hlapμ : ∀ k : ℕ, Tendsto (fun i => ∫ x, Real.exp (-((k : ℝ) * x)) ∂(μs i)) l
      (𝓝 (1 / (1 + (k : ℝ)))))
    (hlapκ : ∀ k : ℕ, Tendsto (fun i => ∫ x, Real.exp (-((k : ℝ) * x)) ∂(κs i)) l
      (𝓝 (1 / (1 + (k : ℝ)))))
    (hmomμ : Tendsto (fun i => ∫ x, x ^ 2 ∂(μs i)) l (𝓝 2))
    (hmomκ : Tendsto (fun i => ∫ x, x ^ 2 ∂(κs i)) l (𝓝 2)) :
    Tendsto (fun i => ∫ z, |z.1 - z.2| ^ 2 ∂(monotoneCoupling (μs i) (κs i))) l (𝓝 0) := by
  haveI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  exact tendsto_integral_monotoneCoupling_pair_sq μs κs (expMeasure 1) hintμ hintκ
    integrable_sq_expMeasure_one
    (tendsto_integral_monotoneCoupling_sq_of_tendsto_laplace_value μs hsuppμ hintμ hlapμ hmomμ)
    (tendsto_integral_monotoneCoupling_sq_of_tendsto_laplace_value κs hsuppκ hintκ hlapκ hmomκ)

/-! ### The centered quadratic transport cost -/

/-- The uniform law on the unit interval is a probability law. -/
theorem isProbabilityMeasure_restrict_Ioo_zero_one :
    IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := by
  constructor
  rw [Measure.restrict_apply_univ, Real.volume_Ioo]
  norm_num

/-- The monotone coupling is a probability law on the plane. -/
instance isProbabilityMeasure_monotoneCoupling (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (monotoneCoupling μ ν) := by
  haveI := isProbabilityMeasure_restrict_Ioo_zero_one
  rw [monotoneCoupling]
  exact Measure.isProbabilityMeasure_map (measurable_quantilePair μ ν).aemeasurable

/-- The centered squared distance is dominated by the squared distance and the distance of the
centers. -/
theorem sq_abs_sub_centered_le (a b c₁ c₂ : ℝ) :
    |(a - c₁) - (b - c₂)| ^ 2 ≤ 2 * |a - b| ^ 2 + 2 * |c₁ - c₂| ^ 2 := by
  rw [sq_abs, sq_abs, sq_abs]
  nlinarith [sq_nonneg ((a - b) + (c₁ - c₂))]

/-- The quadratic cost of the monotone coupling of two laws with finite second moments is
integrable. -/
theorem integrable_sq_sub_monotoneCoupling (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : Integrable (fun x : ℝ => x ^ 2) μ)
    (hν : Integrable (fun x : ℝ => x ^ 2) ν) :
    Integrable (fun z : ℝ × ℝ => |z.1 - z.2| ^ 2) (monotoneCoupling μ ν) := by
  rw [monotoneCoupling]
  refine (integrable_map_measure
    ((measurable_fst.sub measurable_snd).abs.pow_const 2).aestronglyMeasurable
    (measurable_quantilePair μ ν).aemeasurable).mpr ?_
  exact integrableOn_quantile_sub_sq μ ν hμ hν

/-- **Vanishing centered quadratic transport cost.**  If the quadratic transport cost of the
monotone couplings vanishes and the two means come together, then the centered variables are
coupled in `L²`. -/
theorem tendsto_integral_monotoneCoupling_centered_sq {ι : Type*} {l : Filter ι}
    (μ κ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (κ i)]
    (hintμ : ∀ i, Integrable (fun x : ℝ => x ^ 2) (μ i))
    (hintκ : ∀ i, Integrable (fun x : ℝ => x ^ 2) (κ i))
    (hcost : Tendsto (fun i => ∫ z, |z.1 - z.2| ^ 2 ∂(monotoneCoupling (μ i) (κ i))) l (𝓝 0))
    (hmean : Tendsto (fun i => |(∫ x, x ∂(μ i)) - ∫ x, x ∂(κ i)|) l (𝓝 0)) :
    Tendsto (fun i => ∫ z, |(z.1 - ∫ x, x ∂(μ i)) - (z.2 - ∫ x, x ∂(κ i))| ^ 2
      ∂(monotoneCoupling (μ i) (κ i))) l (𝓝 0) := by
  have hlim : Tendsto (fun i => 2 * (∫ z, |z.1 - z.2| ^ 2 ∂(monotoneCoupling (μ i) (κ i)))
      + 2 * |(∫ x, x ∂(μ i)) - ∫ x, x ∂(κ i)| ^ 2) l (𝓝 0) := by
    have h := (hcost.const_mul 2).add ((hmean.pow 2).const_mul 2)
    simpa using h
  refine squeeze_zero (fun i => integral_nonneg fun z => sq_nonneg _) (fun i => ?_) hlim
  have hbase := integrable_sq_sub_monotoneCoupling (μ i) (κ i) (hintμ i) (hintκ i)
  have hdom : Integrable (fun z : ℝ × ℝ => 2 * |z.1 - z.2| ^ 2
      + 2 * |(∫ x, x ∂(μ i)) - ∫ x, x ∂(κ i)| ^ 2) (monotoneCoupling (μ i) (κ i)) :=
    (hbase.const_mul 2).add (integrable_const _)
  have hbound : ∀ z : ℝ × ℝ,
      |(z.1 - ∫ x, x ∂(μ i)) - (z.2 - ∫ x, x ∂(κ i))| ^ 2
        ≤ 2 * |z.1 - z.2| ^ 2 + 2 * |(∫ x, x ∂(μ i)) - ∫ x, x ∂(κ i)| ^ 2 :=
    fun z => sq_abs_sub_centered_le _ _ _ _
  have hmeasC : AEStronglyMeasurable (fun z : ℝ × ℝ =>
      |(z.1 - ∫ x, x ∂(μ i)) - (z.2 - ∫ x, x ∂(κ i))| ^ 2) (monotoneCoupling (μ i) (κ i)) :=
    (((measurable_fst.sub_const _).sub (measurable_snd.sub_const _)).abs.pow_const
      2).aestronglyMeasurable
  have hintC : Integrable (fun z : ℝ × ℝ =>
      |(z.1 - ∫ x, x ∂(μ i)) - (z.2 - ∫ x, x ∂(κ i))| ^ 2) (monotoneCoupling (μ i) (κ i)) := by
    refine Integrable.mono hdom hmeasC (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * |z.1 - z.2| ^ 2
        + 2 * |(∫ x, x ∂(μ i)) - ∫ x, x ∂(κ i)| ^ 2)]
    exact hbound z
  calc (∫ z, |(z.1 - ∫ x, x ∂(μ i)) - (z.2 - ∫ x, x ∂(κ i))| ^ 2
          ∂(monotoneCoupling (μ i) (κ i)))
      ≤ ∫ z, (2 * |z.1 - z.2| ^ 2 + 2 * |(∫ x, x ∂(μ i)) - ∫ x, x ∂(κ i)| ^ 2)
          ∂(monotoneCoupling (μ i) (κ i)) :=
        integral_mono_ae hintC hdom (Filter.Eventually.of_forall hbound)
    _ = 2 * (∫ z, |z.1 - z.2| ^ 2 ∂(monotoneCoupling (μ i) (κ i)))
          + 2 * |(∫ x, x ∂(μ i)) - ∫ x, x ∂(κ i)| ^ 2 := by
        rw [integral_add (hbase.const_mul 2) (integrable_const _), integral_const_mul,
          integral_const]
        simp

/-! ### The gap law of a monotone coupling -/

/-- The distance of two integrable quantile functions is integrable. -/
theorem integrableOn_quantile_sub (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : Integrable (id : ℝ → ℝ) μ) (hν : Integrable (id : ℝ → ℝ) ν) :
    IntegrableOn (fun p => |quantile μ p - quantile ν p|) (Ioo (0 : ℝ) 1) :=
  ((integrableOn_quantile μ hμ).sub (integrableOn_quantile ν hν)).abs

/-- The transport cost of the monotone coupling of two laws with finite means is integrable. -/
theorem integrable_abs_sub_monotoneCoupling (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : Integrable (id : ℝ → ℝ) μ) (hν : Integrable (id : ℝ → ℝ) ν) :
    Integrable (fun z : ℝ × ℝ => |z.1 - z.2|) (monotoneCoupling μ ν) := by
  rw [monotoneCoupling]
  refine (integrable_map_measure ((measurable_fst.sub measurable_snd).abs).aestronglyMeasurable
    (measurable_quantilePair μ ν).aemeasurable).mpr ?_
  exact integrableOn_quantile_sub μ ν hμ hν

/-- The law of the gap of a monotone coupling. -/
def gapLaw (μ ν : Measure ℝ) : Measure ℝ :=
  Measure.map (fun z : ℝ × ℝ => z.1 - z.2) (monotoneCoupling μ ν)

instance isProbabilityMeasure_gapLaw (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (gapLaw μ ν) := by
  rw [gapLaw]
  exact Measure.isProbabilityMeasure_map (measurable_fst.sub measurable_snd).aemeasurable

/-- Integrals of a function of the gap are integrals against the gap law. -/
theorem integral_gapLaw (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : ℝ → ℝ} (hf : AEStronglyMeasurable f (gapLaw μ ν)) :
    (∫ x, f x ∂(gapLaw μ ν)) = ∫ z, f (z.1 - z.2) ∂(monotoneCoupling μ ν) := by
  rw [gapLaw] at hf ⊢
  exact integral_map (measurable_fst.sub measurable_snd).aemeasurable hf

/-- The gap law of two laws with finite means has a finite first absolute moment. -/
theorem integrable_abs_gapLaw (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (id : ℝ → ℝ) μ) (hν : Integrable (id : ℝ → ℝ) ν) :
    Integrable (fun x : ℝ => |x|) (gapLaw μ ν) := by
  rw [gapLaw]
  refine (integrable_map_measure (measurable_id.abs).aestronglyMeasurable
    (measurable_fst.sub measurable_snd).aemeasurable).mpr ?_
  exact integrable_abs_sub_monotoneCoupling μ ν hμ hν

/-- A function of the gap is integrable exactly when it is integrable against the gap law. -/
theorem integrable_comp_gap (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : ℝ → ℝ} (hf : AEStronglyMeasurable f (gapLaw μ ν))
    (hint : Integrable f (gapLaw μ ν)) :
    Integrable (fun z : ℝ × ℝ => f (z.1 - z.2)) (monotoneCoupling μ ν) := by
  rw [gapLaw] at hint hf
  exact (integrable_map_measure hf (measurable_fst.sub measurable_snd).aemeasurable).mp hint

/-- The first coordinate of a monotone coupling of half-line laws is nonnegative. -/
theorem ae_nonneg_fst_monotoneCoupling (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hsupp : μ (Iio 0) = 0) :
    ∀ᵐ z ∂(monotoneCoupling μ ν), 0 ≤ z.1 := by
  have hpre : (monotoneCoupling μ ν) ((fun z : ℝ × ℝ => z.1) ⁻¹' (Iio 0)) = 0 := by
    rw [← Measure.map_apply measurable_fst measurableSet_Iio, map_fst_monotoneCoupling, hsupp]
  refine MeasureTheory.ae_iff.mpr (measure_mono_null ?_ hpre)
  intro z hz
  exact not_le.mp hz

/-- The second coordinate of a monotone coupling of half-line laws is nonnegative. -/
theorem ae_nonneg_snd_monotoneCoupling (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hsupp : ν (Iio 0) = 0) :
    ∀ᵐ z ∂(monotoneCoupling μ ν), 0 ≤ z.2 := by
  have hpre : (monotoneCoupling μ ν) ((fun z : ℝ × ℝ => z.2) ⁻¹' (Iio 0)) = 0 := by
    rw [← Measure.map_apply measurable_snd measurableSet_Iio, map_snd_monotoneCoupling, hsupp]
  refine MeasureTheory.ae_iff.mpr (measure_mono_null ?_ hpre)
  intro z hz
  exact not_le.mp hz

/-- **The quadratic transport cost scales with the square of the scale.** -/
theorem integral_monotoneCoupling_sq_sub_scaleLaw {c : ℝ} (hc : 0 < c) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (∫ z, |z.1 - z.2| ^ 2 ∂(monotoneCoupling (scaleLaw c μ) (scaleLaw c ν)))
      = c ^ 2 * ∫ z, |z.1 - z.2| ^ 2 ∂(monotoneCoupling μ ν) := by
  haveI : IsProbabilityMeasure (scaleLaw c μ) := instIsProbabilityMeasureScaleLaw c μ
  haveI : IsProbabilityMeasure (scaleLaw c ν) := instIsProbabilityMeasureScaleLaw c ν
  rw [integral_monotoneCoupling_sq_sub, integral_monotoneCoupling_sq_sub, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun p hp => ?_
  rw [quantile_scaleLaw hc μ hp.1 hp.2, quantile_scaleLaw hc ν hp.1 hp.2, ← mul_sub, abs_mul,
    abs_of_pos hc, mul_pow]

/-- The centered quadratic cost of the monotone coupling, as a quantile integral. -/
theorem integral_monotoneCoupling_centered_sq_eq (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (a b : ℝ) :
    (∫ z, |(z.1 - a) - (z.2 - b)| ^ 2 ∂(monotoneCoupling μ ν))
      = ∫ p in Ioo (0 : ℝ) 1, |(quantile μ p - a) - (quantile ν p - b)| ^ 2 := by
  have h : ∫ (z : ℝ × ℝ), |(z.1 - a) - (z.2 - b)| ^ 2
        ∂(Measure.map (fun p => (quantile μ p, quantile ν p))
          (volume.restrict (Ioo (0 : ℝ) 1)))
      = ∫ p, |(quantile μ p - a) - (quantile ν p - b)| ^ 2
        ∂(volume.restrict (Ioo (0 : ℝ) 1)) :=
    integral_map (measurable_quantilePair μ ν).aemeasurable
      ((((measurable_fst.sub_const a).sub (measurable_snd.sub_const b)).abs).pow_const
        2).aestronglyMeasurable
  rw [monotoneCoupling]
  exact h

/-- **The centered quadratic cost scales with the square of the scale.** -/
theorem integral_monotoneCoupling_centered_sq_scaleLaw {c : ℝ} (hc : 0 < c) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (∫ z, |(z.1 - ∫ x, x ∂(scaleLaw c μ)) - (z.2 - ∫ x, x ∂(scaleLaw c ν))| ^ 2
        ∂(monotoneCoupling (scaleLaw c μ) (scaleLaw c ν)))
      = c ^ 2 * ∫ z, |(z.1 - ∫ x, x ∂μ) - (z.2 - ∫ x, x ∂ν)| ^ 2 ∂(monotoneCoupling μ ν) := by
  haveI : IsProbabilityMeasure (scaleLaw c μ) := instIsProbabilityMeasureScaleLaw c μ
  haveI : IsProbabilityMeasure (scaleLaw c ν) := instIsProbabilityMeasureScaleLaw c ν
  rw [integral_monotoneCoupling_centered_sq_eq, integral_monotoneCoupling_centered_sq_eq,
    ← integral_const_mul, integral_id_scaleLaw, integral_id_scaleLaw]
  refine setIntegral_congr_fun measurableSet_Ioo fun p hp => ?_
  rw [quantile_scaleLaw hc μ hp.1 hp.2, quantile_scaleLaw hc ν hp.1 hp.2]
  have hfac : (c * quantile μ p - c * ∫ x, x ∂μ) - (c * quantile ν p - c * ∫ x, x ∂ν)
      = c * ((quantile μ p - ∫ x, x ∂μ) - (quantile ν p - ∫ x, x ∂ν)) := by ring
  rw [hfac, abs_mul, abs_of_pos hc, mul_pow]

end

end GaloisForLFunctions.HTGeometry
