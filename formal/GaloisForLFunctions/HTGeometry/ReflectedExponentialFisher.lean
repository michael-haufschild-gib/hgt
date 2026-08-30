import GaloisForLFunctions.HTGeometry.LikelihoodJeffreysBound
import Mathlib.Probability.Moments.Tilted
import Mathlib.Probability.Moments.MGFAnalytic

/-!
# The reflected exponential family and its Fisher response

A reflection-invariant base law together with a reflection-odd statistic generates a reflected
exponential family.  Its cumulant generating function is even, the reflection exchanges the two
tilts, and the posterior contrast of the reflected pair is `tanh(t·T)`.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-- `(LPC.38)`  A reflection-invariant base law with a reflection-odd statistic. -/
structure ReflectedExponentialFamily (X : Type*) [MeasurableSpace X] where
  /-- The reflection-invariant base law `P₀`. -/
  base : Measure X
  isProb : IsProbabilityMeasure base
  /-- The reflection `R`. -/
  reflection : X → X
  measurable_reflection : Measurable reflection
  reflection_involutive : ∀ x, reflection (reflection x) = x
  map_base : base.map reflection = base
  /-- The reflection-odd statistic `T`. -/
  stat : X → ℝ
  measurable_stat : Measurable stat
  stat_odd : ∀ x, stat (reflection x) = -stat x

namespace ReflectedExponentialFamily

variable (F : ReflectedExponentialFamily X)

instance : IsProbabilityMeasure F.base := F.isProb

theorem measurePreserving_reflection : MeasurePreserving F.reflection F.base F.base :=
  ⟨F.measurable_reflection, F.map_base⟩

/-- `(LPC.38)`  The tilted member `P_t`. -/
def tilt (t : ℝ) : Measure X := F.base.tilted fun x => t * F.stat x

/-- `(LPC.38)`  The cumulant generating function `A`. -/
def cumulant (t : ℝ) : ℝ := cgf F.stat F.base t

/-- The moment generating function is reflection even. -/
theorem mgf_neg (t : ℝ) : mgf F.stat F.base (-t) = mgf F.stat F.base t := by
  have h : ∫ x, Real.exp (t * F.stat x) ∂F.base
      = ∫ x, Real.exp (t * F.stat (F.reflection x)) ∂F.base := by
    have hmap := integral_map (μ := F.base) (φ := F.reflection)
      (f := fun x => Real.exp (t * F.stat x)) F.measurable_reflection.aemeasurable
      (by
        rw [F.map_base]
        exact (Real.continuous_exp.measurable.comp
          (measurable_const.mul F.measurable_stat)).aestronglyMeasurable)
    rw [F.map_base] at hmap
    exact hmap
  rw [mgf, mgf]
  conv_rhs => rw [h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show Real.exp (-t * F.stat x) = Real.exp (t * F.stat (F.reflection x))
  rw [F.stat_odd]
  congr 1
  ring

/-- `(LPC.38)`  The cumulant generating function is even. -/
theorem cumulant_neg (t : ℝ) : F.cumulant (-t) = F.cumulant t := by
  rw [cumulant, cumulant, cgf, cgf, F.mgf_neg]

theorem mgf_pos (t : ℝ) (hint : Integrable (fun x => Real.exp (t * F.stat x)) F.base) :
    0 < mgf F.stat F.base t := integral_exp_pos hint

theorem aestronglyMeasurable_expStat (t : ℝ) :
    AEStronglyMeasurable (fun x => Real.exp (t * F.stat x)) F.base :=
  (Real.continuous_exp.measurable.comp
    (measurable_const.mul F.measurable_stat)).aestronglyMeasurable

theorem integrable_exp_neg (t : ℝ)
    (hint : Integrable (fun x => Real.exp (t * F.stat x)) F.base) :
    Integrable (fun x => Real.exp (-t * F.stat x)) F.base := by
  have h := (F.measurePreserving_reflection.integrable_comp
    (F.aestronglyMeasurable_expStat t)).mpr hint
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  show Real.exp (t * F.stat (F.reflection x)) = Real.exp (-t * F.stat x)
  rw [F.stat_odd]
  congr 1
  ring

theorem tilt_eq_withDensity (t : ℝ) :
    F.tilt t = F.base.withDensity
      (fun x => ENNReal.ofReal (Real.exp (t * F.stat x) / mgf F.stat F.base t)) := rfl

theorem measurable_tiltDensity (t : ℝ) :
    Measurable fun x => ENNReal.ofReal (Real.exp (t * F.stat x) / mgf F.stat F.base t) :=
  ENNReal.measurable_ofReal.comp
    ((Real.continuous_exp.measurable.comp (measurable_const.mul F.measurable_stat)).div_const _)

theorem isProbabilityMeasure_tilt (t : ℝ)
    (hint : Integrable (fun x => Real.exp (t * F.stat x)) F.base) :
    IsProbabilityMeasure (F.tilt t) := by
  haveI : NeZero F.base := ⟨IsProbabilityMeasure.ne_zero F.base⟩
  exact isProbabilityMeasure_tilted hint

/-- The balanced law of a reflected tilt pair has hyperbolic-cosine density. -/
theorem balancedLaw_tilt (t : ℝ) (hint : Integrable (fun x => Real.exp (t * F.stat x)) F.base) :
    balancedLaw (F.tilt t) (F.tilt (-t))
      = F.base.withDensity
        (fun x => ENNReal.ofReal (Real.cosh (t * F.stat x) / mgf F.stat F.base t)) := by
  have hmgf := F.mgf_pos t hint
  rw [balancedLaw, F.tilt_eq_withDensity, F.tilt_eq_withDensity,
    ← withDensity_add_left (F.measurable_tiltDensity t), ← withDensity_smul _
      (by exact (F.measurable_tiltDensity t).add (F.measurable_tiltDensity (-t)))]
  refine withDensity_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hneg : mgf F.stat F.base (-t) = mgf F.stat F.base t := F.mgf_neg t
  show (2 : ℝ≥0∞)⁻¹ * (ENNReal.ofReal (Real.exp (t * F.stat x) / mgf F.stat F.base t)
      + ENNReal.ofReal (Real.exp (-t * F.stat x) / mgf F.stat F.base (-t))) = _
  rw [hneg, ← ENNReal.ofReal_add (by positivity) (by positivity),
    show ((2 : ℝ≥0∞))⁻¹ = ENNReal.ofReal (2⁻¹ : ℝ) by
      rw [ENNReal.ofReal_inv_of_pos (by norm_num)]; norm_num,
    ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  rw [Real.cosh_eq]
  field_simp

/-- `(LPC.39)`  The posterior contrast of a reflected tilt pair is `tanh(t·T)`. -/
theorem posteriorContrast_tilt (t : ℝ)
    (hint : Integrable (fun x => Real.exp (t * F.stat x)) F.base) :
    posteriorContrast (F.tilt t) (F.tilt (-t))
      =ᵐ[balancedLaw (F.tilt t) (F.tilt (-t))] fun x => Real.tanh (t * F.stat x) := by
  have hmgf := F.mgf_pos t hint
  haveI := F.isProbabilityMeasure_tilt t hint
  haveI := F.isProbabilityMeasure_tilt (-t) (F.integrable_exp_neg t hint)
  set η := balancedLaw (F.tilt t) (F.tilt (-t)) with hη
  have hηw : η = F.base.withDensity
      (fun x => ENNReal.ofReal (Real.cosh (t * F.stat x) / mgf F.stat F.base t)) :=
    F.balancedLaw_tilt t hint
  have hmeasC : Measurable fun x => ENNReal.ofReal
      (Real.cosh (t * F.stat x) / mgf F.stat F.base t) :=
    ENNReal.measurable_ofReal.comp
      ((Real.continuous_cosh.measurable.comp (measurable_const.mul F.measurable_stat)).div_const _)
  have hacη : η ≪ F.base := by rw [hηw]; exact withDensity_absolutelyContinuous _ _
  have hac : F.tilt t ≪ η := absolutelyContinuous_balancedLaw_left _ _
  have hdη : η.rnDeriv F.base =ᵐ[F.base]
      fun x => ENNReal.ofReal (Real.cosh (t * F.stat x) / mgf F.stat F.base t) := by
    rw [hηw]; exact Measure.rnDeriv_withDensity _ hmeasC
  have hdt : (F.tilt t).rnDeriv F.base =ᵐ[F.base]
      fun x => ENNReal.ofReal (Real.exp (t * F.stat x) / mgf F.stat F.base t) := by
    rw [F.tilt_eq_withDensity]; exact Measure.rnDeriv_withDensity _ (F.measurable_tiltDensity t)
  have hchain := Measure.rnDeriv_mul_rnDeriv (κ := F.base) hac
  have key : ∀ᵐ x ∂η, ((F.tilt t).rnDeriv η x).toReal
      = Real.exp (t * F.stat x) / Real.cosh (t * F.stat x) := by
    filter_upwards [hchain.filter_mono hacη.ae_le, hdη.filter_mono hacη.ae_le,
      hdt.filter_mono hacη.ae_le, Measure.rnDeriv_lt_top (F.tilt t) η] with x hc hη' hd hf
    have hcosh : 0 < Real.cosh (t * F.stat x) := Real.cosh_pos _
    have hc' : (F.tilt t).rnDeriv η x
        * ENNReal.ofReal (Real.cosh (t * F.stat x) / mgf F.stat F.base t)
        = (F.tilt t).rnDeriv F.base x := by
      rw [← hη']; exact hc
    have hR := congrArg ENNReal.toReal hc'
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), hd,
      ENNReal.toReal_ofReal (by positivity)] at hR
    field_simp at hR ⊢
    linarith [hR]
  filter_upwards [key] with x hx
  show ((F.tilt t).rnDeriv η x).toReal - 1 = _
  rw [hx, Real.tanh_eq_sinh_div_cosh, Real.cosh_eq, Real.sinh_eq]
  have hcosh : (0:ℝ) < (Real.exp (t * F.stat x) + Real.exp (-(t * F.stat x))) / 2 := by
    have := Real.cosh_pos (t * F.stat x)
    rwa [Real.cosh_eq] at this
  field_simp
  ring

/-- Integration against the balanced law of a reflected tilt pair. -/
theorem integral_balancedLaw_tilt (t : ℝ)
    (hint : Integrable (fun x => Real.exp (t * F.stat x)) F.base) (g : X → ℝ) :
    ∫ x, g x ∂(balancedLaw (F.tilt t) (F.tilt (-t)))
      = ∫ x, (Real.cosh (t * F.stat x) / mgf F.stat F.base t) * g x ∂F.base := by
  have hmgf := F.mgf_pos t hint
  rw [F.balancedLaw_tilt t hint,
    integral_withDensity_eq_integral_toReal_smul
      (f := fun x => ENNReal.ofReal (Real.cosh (t * F.stat x) / mgf F.stat F.base t))
      (ENNReal.measurable_ofReal.comp
        ((Real.continuous_cosh.measurable.comp
          (measurable_const.mul F.measurable_stat)).div_const _))
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top) g]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show (ENNReal.ofReal (Real.cosh (t * F.stat x) / mgf F.stat F.base t)).toReal • g x = _
  rw [smul_eq_mul, ENNReal.toReal_ofReal (by positivity)]

/-- `(LPC.40)`  The coherence energy of a reflected tilt pair. -/
theorem coherenceWork_tilt (t : ℝ)
    (hint : Integrable (fun x => Real.exp (t * F.stat x)) F.base) :
    coherenceWork (F.tilt t) (F.tilt (-t))
      = 4 / mgf F.stat F.base t
        * ∫ x, Real.sinh (t * F.stat x) ^ 2 / Real.cosh (t * F.stat x) ∂F.base := by
  have hmgf := F.mgf_pos t hint
  haveI := F.isProbabilityMeasure_tilt t hint
  haveI := F.isProbabilityMeasure_tilt (-t) (F.integrable_exp_neg t hint)
  rw [coherenceWork]
  have hcongr : ∫ x, (posteriorContrast (F.tilt t) (F.tilt (-t)) x) ^ 2
        ∂(balancedLaw (F.tilt t) (F.tilt (-t)))
      = ∫ x, (Real.tanh (t * F.stat x)) ^ 2 ∂(balancedLaw (F.tilt t) (F.tilt (-t))) := by
    refine integral_congr_ae ?_
    filter_upwards [F.posteriorContrast_tilt t hint] with x hx
    rw [hx]
  rw [hcongr, F.integral_balancedLaw_tilt t hint, ← integral_const_mul,
    show (4 : ℝ) / mgf F.stat F.base t
        * ∫ x, Real.sinh (t * F.stat x) ^ 2 / Real.cosh (t * F.stat x) ∂F.base
      = ∫ x, 4 / mgf F.stat F.base t
        * (Real.sinh (t * F.stat x) ^ 2 / Real.cosh (t * F.stat x)) ∂F.base
      from (integral_const_mul _ _).symm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hc : 0 < Real.cosh (t * F.stat x) := Real.cosh_pos _
  show 4 * (Real.cosh (t * F.stat x) / mgf F.stat F.base t * Real.tanh (t * F.stat x) ^ 2)
      = 4 / mgf F.stat F.base t * (Real.sinh (t * F.stat x) ^ 2 / Real.cosh (t * F.stat x))
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp

/-! ## Mutual absolute continuity of the reflected tilts -/

theorem absolutelyContinuous_withDensity_of_pos {μ : Measure X} {f : X → ℝ≥0∞}
    (hf : Measurable f) (hpos : ∀ x, f x ≠ 0) : μ ≪ μ.withDensity f := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hz => ?_
  rw [withDensity_apply _ hs] at hz
  have hzero := (lintegral_eq_zero_iff hf).mp hz
  have : (μ.restrict s) {x | f x = 0} = μ.restrict s Set.univ := by
    refine measure_congr ?_
    filter_upwards [hzero] with x hx
    show (f x = 0) = (x ∈ Set.univ)
    simp [show f x = 0 from hx]
  have huniv : μ.restrict s Set.univ = 0 := by
    rw [← this]
    refine measure_mono_null (fun x hx => ?_) (measure_empty (μ := μ.restrict s))
    exact absurd hx (by simpa using hpos x)
  rwa [Measure.restrict_apply_univ] at huniv

theorem tiltDensity_ne_zero (t : ℝ)
    (hint : Integrable (fun x => Real.exp (t * F.stat x)) F.base) (x : X) :
    ENNReal.ofReal (Real.exp (t * F.stat x) / mgf F.stat F.base t) ≠ 0 := by
  have hmgf := F.mgf_pos t hint
  simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
  positivity

theorem base_absolutelyContinuous_tilt (t : ℝ)
    (hint : Integrable (fun x => Real.exp (t * F.stat x)) F.base) : F.base ≪ F.tilt t := by
  rw [F.tilt_eq_withDensity]
  exact absolutelyContinuous_withDensity_of_pos (F.measurable_tiltDensity t)
    (F.tiltDensity_ne_zero t hint)

theorem tilt_absolutelyContinuous_base (t : ℝ) : F.tilt t ≪ F.base := by
  rw [F.tilt_eq_withDensity]
  exact withDensity_absolutelyContinuous _ _

/-- The two reflected tilts are mutually absolutely continuous. -/
theorem tilt_absolutelyContinuous (t : ℝ)
    (hint : Integrable (fun x => Real.exp (t * F.stat x)) F.base) :
    F.tilt t ≪ F.tilt (-t) :=
  (F.tilt_absolutelyContinuous_base t).trans
    (F.base_absolutelyContinuous_tilt (-t) (F.integrable_exp_neg t hint))

/-- The reflected statistic integral is the moment derivative. -/
theorem integral_stat_mul_sinh (t : ℝ)
    (hint : Integrable (fun x => (F.stat x) * Real.exp (t * F.stat x)) F.base)
    (hint' : Integrable (fun x => (F.stat x) * Real.exp (-t * F.stat x)) F.base) :
    ∫ x, F.stat x * Real.sinh (t * F.stat x) ∂F.base
      = ∫ x, F.stat x * Real.exp (t * F.stat x) ∂F.base := by
  have hrefl : ∫ x, F.stat x * Real.exp (-t * F.stat x) ∂F.base
      = -∫ x, F.stat x * Real.exp (t * F.stat x) ∂F.base := by
    have hmap := integral_map (μ := F.base) (φ := F.reflection)
      (f := fun x => F.stat x * Real.exp (-t * F.stat x))
      F.measurable_reflection.aemeasurable
      (by
        rw [F.map_base]
        exact (F.measurable_stat.mul (Real.continuous_exp.measurable.comp
          (measurable_const.mul F.measurable_stat))).aestronglyMeasurable)
    rw [F.map_base] at hmap
    rw [hmap, ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show F.stat (F.reflection x) * Real.exp (-t * F.stat (F.reflection x))
        = -(F.stat x * Real.exp (t * F.stat x))
    rw [F.stat_odd, show -t * -F.stat x = t * F.stat x by ring]
    ring
  rw [show (fun x => F.stat x * Real.sinh (t * F.stat x))
      = fun x => (F.stat x * Real.exp (t * F.stat x)
        - F.stat x * Real.exp (-t * F.stat x)) / 2 by
    funext x
    rw [Real.sinh_eq]
    have : -(t * F.stat x) = -t * F.stat x := by ring
    rw [this]
    ring]
  rw [integral_div, integral_sub hint hint', hrefl]
  ring

theorem integrable_stat_mul_exp_neg (t : ℝ)
    (hint : Integrable (fun x => F.stat x * Real.exp (t * F.stat x)) F.base) :
    Integrable (fun x => F.stat x * Real.exp (-t * F.stat x)) F.base := by
  have hmeas : AEStronglyMeasurable (fun x => F.stat x * Real.exp (t * F.stat x)) F.base :=
    (F.measurable_stat.mul (Real.continuous_exp.measurable.comp
      (measurable_const.mul F.measurable_stat))).aestronglyMeasurable
  have h := (F.measurePreserving_reflection.integrable_comp hmeas).mpr hint
  have hneg : Integrable (fun x => -(F.stat x * Real.exp (-t * F.stat x))) F.base := by
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    show F.stat (F.reflection x) * Real.exp (t * F.stat (F.reflection x))
        = -(F.stat x * Real.exp (-t * F.stat x))
    rw [F.stat_odd, show t * -F.stat x = -t * F.stat x by ring]
    ring
  simpa using hneg.neg

theorem integrable_stat_mul_exp (t : ℝ)
    (ht : t ∈ interior (integrableExpSet F.stat F.base)) :
    Integrable (fun x => F.stat x * Real.exp (t * F.stat x)) F.base := by
  have h := integrable_pow_mul_exp_of_mem_interior_integrableExpSet ht 1
  simpa using h

/-- `(LPC.41)`  Jeffreys information of a reflected tilt pair is `4t·A'(t)`. -/
theorem formationJeffreys_tilt (t : ℝ)
    (ht : t ∈ interior (integrableExpSet F.stat F.base)) :
    formationJeffreys (F.tilt t) (F.tilt (-t))
      = ENNReal.ofReal (4 * t * deriv (cgf F.stat F.base) t) := by
  have hint : Integrable (fun x => Real.exp (t * F.stat x)) F.base :=
    interior_subset (s := integrableExpSet F.stat F.base) ht
  have hmgf := F.mgf_pos t hint
  have hint1 := F.integrable_stat_mul_exp t ht
  have hint1' := F.integrable_stat_mul_exp_neg t hint1
  haveI := F.isProbabilityMeasure_tilt t hint
  haveI := F.isProbabilityMeasure_tilt (-t) (F.integrable_exp_neg t hint)
  have hac : F.tilt t ≪ F.tilt (-t) := F.tilt_absolutelyContinuous t hint
  have hac' : F.tilt (-t) ≪ F.tilt t := by
    have := F.tilt_absolutelyContinuous (-t) (F.integrable_exp_neg t hint)
    rwa [neg_neg] at this
  rw [formationJeffreys_eq_lintegral _ _ hac hac']
  have hg : ∀ᵐ x ∂(balancedLaw (F.tilt t) (F.tilt (-t))),
      4 * posteriorContrast (F.tilt t) (F.tilt (-t)) x
          * Real.artanh (posteriorContrast (F.tilt t) (F.tilt (-t)) x)
        = 4 * (t * F.stat x) * Real.tanh (t * F.stat x) := by
    filter_upwards [F.posteriorContrast_tilt t hint] with x hx
    rw [hx, Real.artanh_tanh]
    ring
  rw [lintegral_congr_ae (by
    filter_upwards [hg] with x hx
    rw [hx])]
  have hnn : ∀ x : X, 0 ≤ 4 * (t * F.stat x) * Real.tanh (t * F.stat x) := by
    intro x
    rcases le_total 0 (t * F.stat x) with h | h
    · have : 0 ≤ Real.tanh (t * F.stat x) := by
        rw [Real.tanh_eq_sinh_div_cosh]
        exact div_nonneg (Real.sinh_nonneg_iff.mpr h) (Real.cosh_pos _).le
      nlinarith
    · have : Real.tanh (t * F.stat x) ≤ 0 := by
        rw [Real.tanh_eq_sinh_div_cosh]
        exact div_nonpos_of_nonpos_of_nonneg (Real.sinh_nonpos_iff.mpr h) (Real.cosh_pos _).le
      nlinarith
  have hintg : Integrable (fun x => 4 * (t * F.stat x) * Real.tanh (t * F.stat x))
      (balancedLaw (F.tilt t) (F.tilt (-t))) := by
    rw [F.balancedLaw_tilt t hint, integrable_withDensity_iff
      (f := fun x => ENNReal.ofReal (Real.cosh (t * F.stat x) / mgf F.stat F.base t))
      (ENNReal.measurable_ofReal.comp ((Real.continuous_cosh.measurable.comp
        (measurable_const.mul F.measurable_stat)).div_const _))
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
    have hEq : (fun x => 4 * (t * F.stat x) * Real.tanh (t * F.stat x)
        * (ENNReal.ofReal (Real.cosh (t * F.stat x) / mgf F.stat F.base t)).toReal)
        = fun x => (4 * t / mgf F.stat F.base t)
          * (F.stat x * Real.sinh (t * F.stat x)) := by
      funext x
      have hc : 0 < Real.cosh (t * F.stat x) := Real.cosh_pos _
      rw [ENNReal.toReal_ofReal (by positivity), Real.tanh_eq_sinh_div_cosh]
      field_simp
    rw [hEq]
    refine Integrable.const_mul ?_ _
    rw [show (fun x => F.stat x * Real.sinh (t * F.stat x))
        = fun x => (F.stat x * Real.exp (t * F.stat x)
          - F.stat x * Real.exp (-t * F.stat x)) / 2 by
      funext x
      rw [Real.sinh_eq, show -(t * F.stat x) = -t * F.stat x by ring]
      ring]
    exact ((hint1.sub hint1').div_const 2)
  rw [← ofReal_integral_eq_lintegral_ofReal hintg (Filter.Eventually.of_forall hnn)]
  congr 1
  rw [F.integral_balancedLaw_tilt t hint]
  have hEq2 : (fun x => Real.cosh (t * F.stat x) / mgf F.stat F.base t
        * (4 * (t * F.stat x) * Real.tanh (t * F.stat x)))
      = fun x => (4 * t / mgf F.stat F.base t) * (F.stat x * Real.sinh (t * F.stat x)) := by
    funext x
    have hc : 0 < Real.cosh (t * F.stat x) := Real.cosh_pos _
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
  rw [hEq2, integral_const_mul, F.integral_stat_mul_sinh t hint1 hint1', deriv_cgf ht]
  field_simp

end ReflectedExponentialFamily

end

end GaloisForLFunctions.HTGeometry
