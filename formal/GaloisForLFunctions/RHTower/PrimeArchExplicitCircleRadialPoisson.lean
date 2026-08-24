import GaloisForLFunctions.HTGeometry.RadialPoissonMixture
import GaloisForLFunctions.RHTower.PrimeArchXiCompactThorinRH
import GaloisForLFunctions.RHTower.PrimeArchExplicitCircleStateReflection

/-!
# Exact radial Poisson chamber of the explicit prime--archimedean circle state

The canonical compact Xi moment measure is normalized and projected onto the sharp interval
`[0, 2/41]`. Under RH its Poisson barycenter is exactly the already constructed explicit circle
density. Conversely, uniform-norm membership of that density in the closed convex hull of the same
radial kernels forces every finite Hankel form to be nonnegative, hence forces RH.

Thus both pointwise radial disintegration and closed-convex-hull membership are proved exactly
equivalent to RH, with no additional hypothesis.
-/

namespace RHTower

open MeasureTheory Set
open scoped ENNReal

noncomputable section

private theorem primeArchRadialRadius_nonneg : (0 : ℝ) ≤ 2 / 41 := by norm_num
private theorem primeArchRadialRadius_lt_one : (2 / 41 : ℝ) < 1 := by norm_num

/-- Canonical Xi compact moment law normalized to mass one. -/
def normalizedPrimeArchXiCompactMomentMeasure : Measure ℝ :=
  ENNReal.ofReal (normalizedPrimeArchMoment 0)⁻¹ •
    primeArchXiCompactMomentMeasure

theorem isProbabilityMeasure_normalizedPrimeArchXiCompactMomentMeasure_of_rh
    (hRH : RiemannHypothesis) :
    IsProbabilityMeasure normalizedPrimeArchXiCompactMomentMeasure := by
  letI : IsFiniteMeasure primeArchXiCompactMomentMeasure :=
    primeArchXiCompactMomentMeasure_finite
  rw [isProbabilityMeasure_iff, normalizedPrimeArchXiCompactMomentMeasure,
    Measure.smul_apply, smul_eq_mul]
  have hm0 := integral_primeArchXiCompactMomentMeasure_eq_of_riemannHypothesis hRH 0
  simp only [pow_zero, integral_const] at hm0
  have hfinite : primeArchXiCompactMomentMeasure Set.univ ≠ ∞ := measure_ne_top _ _
  have hmass : primeArchXiCompactMomentMeasure Set.univ =
      ENNReal.ofReal (normalizedPrimeArchMoment 0) := by
    calc
      primeArchXiCompactMomentMeasure Set.univ =
          ENNReal.ofReal (primeArchXiCompactMomentMeasure Set.univ).toReal :=
        (ENNReal.ofReal_toReal hfinite).symm
      _ = ENNReal.ofReal (normalizedPrimeArchMoment 0) := by
        rw [← measureReal_def]
        congr 1
        simpa using hm0
  rw [hmass, ENNReal.ofReal_inv_of_pos normalizedPrimeArchMoment_zero_pos]
  exact ENNReal.inv_mul_cancel
    (ENNReal.ofReal_pos.mpr normalizedPrimeArchMoment_zero_pos).ne'
    ENNReal.ofReal_ne_top

theorem integral_normalizedPrimeArchXiCompactMomentMeasure_pow_of_rh
    (hRH : RiemannHypothesis) (n : ℕ) :
    ∫ x : ℝ, x ^ n ∂normalizedPrimeArchXiCompactMomentMeasure =
      normalizedPrimeArchMoment n / normalizedPrimeArchMoment 0 := by
  rw [normalizedPrimeArchXiCompactMomentMeasure, integral_smul_measure]
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr normalizedPrimeArchMoment_zero_pos.le)]
  rw [integral_primeArchXiCompactMomentMeasure_eq_of_riemannHypothesis hRH]
  simp only [smul_eq_mul]
  field_simp [normalizedPrimeArchMoment_zero_pos.ne']

/-- Canonical normalized Xi radial law, projected onto the sharp endpoint aperture. -/
def primeArchRadialPoissonMeasure :
    Measure (GaloisForLFunctions.HTGeometry.RadialPoissonParameter (2 / 41)) :=
  Measure.map
    (GaloisForLFunctions.HTGeometry.clampRadialPoissonParameter
      primeArchRadialRadius_nonneg)
    normalizedPrimeArchXiCompactMomentMeasure

theorem isProbabilityMeasure_primeArchRadialPoissonMeasure_of_rh
    (hRH : RiemannHypothesis) :
    IsProbabilityMeasure primeArchRadialPoissonMeasure := by
  letI : IsProbabilityMeasure normalizedPrimeArchXiCompactMomentMeasure :=
    isProbabilityMeasure_normalizedPrimeArchXiCompactMomentMeasure_of_rh hRH
  rw [isProbabilityMeasure_iff, primeArchRadialPoissonMeasure,
    Measure.map_apply_of_aemeasurable
      (GaloisForLFunctions.HTGeometry.continuous_clampRadialPoissonParameter
        primeArchRadialRadius_nonneg).aemeasurable MeasurableSet.univ]
  simp

theorem integral_primeArchRadialPoissonMeasure_pow_of_rh
    (hRH : RiemannHypothesis) (n : ℕ) :
    ∫ r, (r : ℝ) ^ n ∂primeArchRadialPoissonMeasure =
      normalizedPrimeArchMoment n / normalizedPrimeArchMoment 0 := by
  letI : IsProbabilityMeasure normalizedPrimeArchXiCompactMomentMeasure :=
    isProbabilityMeasure_normalizedPrimeArchXiCompactMomentMeasure_of_rh hRH
  rw [primeArchRadialPoissonMeasure, integral_map
    (GaloisForLFunctions.HTGeometry.continuous_clampRadialPoissonParameter
      primeArchRadialRadius_nonneg).aemeasurable
    (show Continuous
      (fun r : GaloisForLFunctions.HTGeometry.RadialPoissonParameter (2 / 41) =>
        (r : ℝ) ^ n) by fun_prop).aestronglyMeasurable]
  have hsupp : ∀ᵐ x : ℝ ∂normalizedPrimeArchXiCompactMomentMeasure,
      x ∈ Set.Icc (0 : ℝ) (2 / 41) := by
    rw [normalizedPrimeArchXiCompactMomentMeasure]
    apply Measure.ae_smul_measure
    exact ae_primeArchXiCompactMomentMeasure_mem_zero_two_over_fortyOne.mono
      fun x hx => ⟨hx.1, by simpa [abs_of_nonneg hx.1] using hx.2⟩
  calc
    ∫ x : ℝ,
        (GaloisForLFunctions.HTGeometry.clampRadialPoissonParameter
          primeArchRadialRadius_nonneg x : ℝ) ^ n
        ∂normalizedPrimeArchXiCompactMomentMeasure =
      ∫ x : ℝ, x ^ n ∂normalizedPrimeArchXiCompactMomentMeasure := by
        apply integral_congr_ae
        filter_upwards [hsupp] with x hx
        rw [GaloisForLFunctions.HTGeometry.clampRadialPoissonParameter_eq_of_mem
          primeArchRadialRadius_nonneg hx]
    _ = _ := integral_normalizedPrimeArchXiCompactMomentMeasure_pow_of_rh hRH n

private theorem primeArchCircleDensity_eq_symmetricCircleFourierDensity :
    primeArchCircleDensity =
      GaloisForLFunctions.HTGeometry.symmetricCircleFourierDensity
        normalizedPrimeArchMoment := by
  funext z
  change GaloisForLFunctions.HTGeometry.symmetricCircleFourierDensity
      (primeArchShiftMoment 0) z = _
  rw [show primeArchShiftMoment 0 = normalizedPrimeArchMoment by
    funext n
    simp [primeArchShiftMoment]]

/-- Explicit normalized central density as an element of `C(T)`. -/
def primeArchNormalizedCircleDensityContinuousMap : C(Circle, ℝ) :=
  ⟨fun z => primeArchCircleDensity z / normalizedPrimeArchMoment 0, by
    rw [continuous_iff_continuousAt]
    intro z
    have hc : ContinuousAt
        (fun y : Circle => primeArchCircleLaurentExtension (y : ℂ)) z :=
      (analyticAt_primeArchCircleLaurentExtension_on_unitCircle z).continuousAt.comp
        continuousAt_subtype_val
    have hr : ContinuousAt
        (fun y : Circle =>
          (primeArchCircleLaurentExtension (y : ℂ)).re) z :=
      Complex.continuous_re.continuousAt.comp hc
    simpa only [primeArchCircleLaurentExtension_coe, Complex.ofReal_re] using
      hr.div_const (normalizedPrimeArchMoment 0)⟩

@[simp] theorem primeArchNormalizedCircleDensityContinuousMap_apply (z : Circle) :
    primeArchNormalizedCircleDensityContinuousMap z =
      primeArchCircleDensity z / normalizedPrimeArchMoment 0 := rfl

/-- Under RH, the explicit source density is the canonical radial Poisson barycenter pointwise. -/
theorem primeArchNormalizedCircleDensity_eq_radialPoissonBarycenter_of_rh
    (hRH : RiemannHypothesis) :
    primeArchNormalizedCircleDensityContinuousMap =
      GaloisForLFunctions.HTGeometry.radialPoissonBarycenter
        primeArchRadialRadius_lt_one primeArchRadialPoissonMeasure := by
  letI : IsProbabilityMeasure primeArchRadialPoissonMeasure :=
    isProbabilityMeasure_primeArchRadialPoissonMeasure_of_rh hRH
  ext z
  rw [GaloisForLFunctions.HTGeometry.radialPoissonBarycenter_eq_symmetricCircleFourierDensity_moments
    primeArchRadialRadius_nonneg primeArchRadialRadius_lt_one]
  have hmom : (fun n : ℕ => ∫ r, (r : ℝ) ^ n ∂primeArchRadialPoissonMeasure) =
      fun n => normalizedPrimeArchMoment n / normalizedPrimeArchMoment 0 := by
    funext n
    exact integral_primeArchRadialPoissonMeasure_pow_of_rh hRH n
  rw [hmom]
  rw [GaloisForLFunctions.HTGeometry.symmetricCircleFourierDensity_div
    (by simpa [primeArchShiftMoment] using summable_abs_primeArchShiftMoment_tail 0)
    normalizedPrimeArchMoment_zero_pos.ne']
  change primeArchCircleDensity z / normalizedPrimeArchMoment 0 = _
  rw [primeArchCircleDensity_eq_symmetricCircleFourierDensity]

/-- The exact uniform-norm radial Poisson hull generated by the sharp source aperture. -/
def PrimeArchCircleRadialPoissonHull : Prop :=
  primeArchNormalizedCircleDensityContinuousMap ∈
    closedConvexHull ℝ (Set.range
      (GaloisForLFunctions.HTGeometry.radialPoissonKernel
        primeArchRadialRadius_lt_one))

theorem primeArchNormalizedCircleDensity_mem_radialPoissonHull_of_rh
    (hRH : RiemannHypothesis) :
    PrimeArchCircleRadialPoissonHull := by
  letI : IsProbabilityMeasure primeArchRadialPoissonMeasure :=
    isProbabilityMeasure_primeArchRadialPoissonMeasure_of_rh hRH
  rw [PrimeArchCircleRadialPoissonHull,
    primeArchNormalizedCircleDensity_eq_radialPoissonBarycenter_of_rh hRH]
  exact GaloisForLFunctions.HTGeometry.radialPoissonBarycenter_mem_closedConvexHull
    primeArchRadialRadius_lt_one primeArchRadialPoissonMeasure

theorem circleDensityHankelFormCLM_primeArchNormalizedCircleDensity
    {n : ℕ} (v : Fin n → ℝ) :
    GaloisForLFunctions.HTGeometry.circleDensityHankelFormCLM v
        primeArchNormalizedCircleDensityContinuousMap =
      (∑ i : Fin n, ∑ j : Fin n,
        v i * v j * normalizedPrimeArchMoment ((i : ℕ) + (j : ℕ))) /
          normalizedPrimeArchMoment 0 := by
  rw [GaloisForLFunctions.HTGeometry.circleDensityHankelFormCLM_apply]
  have hmoment (k : ℕ) :
      (∫ z : Circle,
        (primeArchNormalizedCircleDensityContinuousMap z : ℂ) * (z : ℂ) ^ k
          ∂GaloisForLFunctions.HTGeometry.circleLebesgue) =
        (normalizedPrimeArchMoment k : ℂ) /
          (normalizedPrimeArchMoment 0 : ℂ) := by
    simp_rw [primeArchNormalizedCircleDensityContinuousMap_apply]
    have hcast : (fun z : Circle =>
        ((primeArchCircleDensity z / normalizedPrimeArchMoment 0 : ℝ) : ℂ) *
          (z : ℂ) ^ k) =
      fun z => (primeArchCircleDensity z : ℂ) /
          (normalizedPrimeArchMoment 0 : ℂ) * (z : ℂ) ^ k := by
      funext z
      push_cast
      rfl
    rw [hcast]
    have hpoint : (fun z : Circle =>
        (primeArchCircleDensity z / normalizedPrimeArchMoment 0 : ℂ) * (z : ℂ) ^ k) =
      fun z => ((normalizedPrimeArchMoment 0 : ℂ)⁻¹) *
        ((primeArchCircleDensity z : ℂ) * (z : ℂ) ^ k) := by
      funext z
      rw [div_eq_inv_mul]
      ring
    rw [hpoint, integral_const_mul]
    rw [primeArchCircleDensity_eq_symmetricCircleFourierDensity]
    rw [GaloisForLFunctions.HTGeometry.integral_symmetricCircleFourierDensity_mul_coe_pow
      (by simpa [primeArchShiftMoment] using summable_abs_primeArchShiftMoment_tail 0)]
    rw [div_eq_mul_inv]
    ring
  have hM := normalizedPrimeArchMoment_zero_pos
  have hmomentRe (k : ℕ) :
      (∫ z : Circle,
        (primeArchNormalizedCircleDensityContinuousMap z : ℂ) * (z : ℂ) ^ k
          ∂GaloisForLFunctions.HTGeometry.circleLebesgue).re =
        normalizedPrimeArchMoment k / normalizedPrimeArchMoment 0 := by
    rw [hmoment]
    simp only [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, Complex.normSq_ofReal]
    field_simp [hM.ne']
    ring
  simp_rw [hmomentRe]
  rw [Finset.sum_div]
  simp_rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  field_simp [hM.ne']

theorem riemannHypothesis_of_primeArchCircleRadialPoissonHull
    (hhull : PrimeArchCircleRadialPoissonHull) : RiemannHypothesis := by
  apply (completeHankelCone_normalizedPrimeArchMoment_iff_riemannHypothesis).mp
  intro n v
  have hv :=
    GaloisForLFunctions.HTGeometry.circleDensityHankelFormCLM_nonneg_of_mem_closedConvexHull
      primeArchRadialRadius_lt_one v hhull
  rw [circleDensityHankelFormCLM_primeArchNormalizedCircleDensity] at hv
  rw [div_eq_mul_inv] at hv
  exact nonneg_of_mul_nonneg_left hv (inv_pos.mpr normalizedPrimeArchMoment_zero_pos)

/-- RH is exactly uniform-norm membership of the explicit density in the closed convex hull of
radial Poisson kernels with `0 ≤ r ≤ 2/41`. -/
theorem primeArchCircleRadialPoissonHull_iff_riemannHypothesis :
    PrimeArchCircleRadialPoissonHull ↔ RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_primeArchCircleRadialPoissonHull
  · exact primeArchNormalizedCircleDensity_mem_radialPoissonHull_of_rh

/-- Pointwise radial Poisson disintegration of the explicit source density. -/
def PrimeArchCircleRadialPoissonMixture : Prop :=
  ∃ ν : Measure
      (GaloisForLFunctions.HTGeometry.RadialPoissonParameter (2 / 41)),
    IsProbabilityMeasure ν ∧
      primeArchNormalizedCircleDensityContinuousMap =
        GaloisForLFunctions.HTGeometry.radialPoissonBarycenter
          primeArchRadialRadius_lt_one ν

theorem primeArchCircleRadialPoissonMixture_iff_riemannHypothesis :
    PrimeArchCircleRadialPoissonMixture ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨ν, hν, hdens⟩
    letI : IsProbabilityMeasure ν := hν
    apply riemannHypothesis_of_primeArchCircleRadialPoissonHull
    rw [PrimeArchCircleRadialPoissonHull, hdens]
    exact GaloisForLFunctions.HTGeometry.radialPoissonBarycenter_mem_closedConvexHull
      primeArchRadialRadius_lt_one ν
  · intro hRH
    exact ⟨primeArchRadialPoissonMeasure,
      isProbabilityMeasure_primeArchRadialPoissonMeasure_of_rh hRH,
      primeArchNormalizedCircleDensity_eq_radialPoissonBarycenter_of_rh hRH⟩

/-- Exact paper form: RH iff `w_Xi/M` is a probability mixture of the radial Poisson kernels on
the sharp interval `[0, 2/41]`. -/
theorem riemannHypothesis_iff_primeArchCircleDensity_radialPoissonIntegral :
    RiemannHypothesis ↔
      ∃ ν : Measure
          (GaloisForLFunctions.HTGeometry.RadialPoissonParameter (2 / 41)),
        IsProbabilityMeasure ν ∧
          ∀ z : Circle,
            primeArchCircleDensity z / normalizedPrimeArchMoment 0 =
              ∫ r,
                poissonKernel 0 (((r : ℝ) : ℂ)) (z : ℂ) ∂ν := by
  rw [← primeArchCircleRadialPoissonMixture_iff_riemannHypothesis]
  constructor
  · rintro ⟨ν, hν, hdens⟩
    refine ⟨ν, hν, fun z => ?_⟩
    letI : IsProbabilityMeasure ν := hν
    have hz := congrArg (fun f : C(Circle, ℝ) => f z) hdens
    rw [GaloisForLFunctions.HTGeometry.radialPoissonBarycenter_apply] at hz
    exact hz
  · rintro ⟨ν, hν, hdens⟩
    refine ⟨ν, hν, ?_⟩
    letI : IsProbabilityMeasure ν := hν
    ext z
    rw [GaloisForLFunctions.HTGeometry.radialPoissonBarycenter_apply]
    exact hdens z

end

end RHTower

