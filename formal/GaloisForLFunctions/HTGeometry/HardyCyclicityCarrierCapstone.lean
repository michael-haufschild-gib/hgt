import GaloisForLFunctions.HTGeometry.HardyCyclicityGaugeBlindness
import GaloisForLFunctions.HTGeometry.HardyCyclicityOrbitFreeness
import GaloisForLFunctions.HTGeometry.HardyCyclicityPowerFieldInvariance

/-!
# One carrier with a maximally free parabolic orbit and every finite cyclicity defect

The bounded outer carrier `O = exp ∘ c ∘ m ∘ φ` of a nonzero finite positive measure is an
invertible bounded analytic function on the disc, so it is a cyclic vector of the shift on `H²(D)`;
multiplying it by a finite Blaschke product of degree `k` leaves the whole differential power tower
over `ℂ(w)` unchanged while cutting the cyclic subspace down to codimension `k`.

For a residual set of exponential parameters the parabolic orbit of the carrier is moreover
differentially algebraically independent, so a single unpointed maximal-hypertranscendental power
pro-field is compatible with every finite Hardy cyclicity defect.
-/

open Complex Filter MeasureTheory Metric Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Bottcher

/-! ## The carrier is a bounded invertible multiplier -/

/-- The exponent of the bounded outer carrier: `σ = c ∘ m ∘ φ`. -/
def carrierExponent (ν : Measure ℝ) (w : ℂ) : ℂ :=
  cayleyToDisc (cauchyTransform ν (cayleyToUpper w))

theorem outerCarrier_eq_exp (ν : Measure ℝ) (w : ℂ) :
    outerCarrier ν w = Complex.exp (carrierExponent ν w) := rfl

theorem differentiableOn_carrierExponent (ν : Measure ℝ) [IsFiniteMeasure ν] :
    DifferentiableOn ℂ (carrierExponent ν) (Metric.ball 0 1) := by
  intro w hw
  have hw1 : ‖w‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hw
  have him : 0 < (cayleyToUpper w).im := im_cayleyToUpper_pos hw1
  have hC : AnalyticAt ℂ (cauchyTransform ν) (cayleyToUpper w) :=
    analyticOnNhd_cauchyTransform ν isOpen_upperHalf (fun z hz => ne_of_gt hz) _ him
  have hcomp : AnalyticAt ℂ (fun z : ℂ => cauchyTransform ν (cayleyToUpper z)) w :=
    AnalyticAt.comp (g := cauchyTransform ν) (f := cayleyToUpper) (x := w) hC
      (analyticAt_cayleyToUpper hw1)
  have hne : cauchyTransform ν (cayleyToUpper w) + Complex.I ≠ 0 :=
    add_I_ne_zero_of_im_nonneg (im_cauchyTransform_nonneg ν him)
  exact (((hcomp.sub analyticAt_const).div (hcomp.add analyticAt_const)
    hne).differentiableAt).differentiableWithinAt

theorem norm_carrierExponent_lt_one (ν : Measure ℝ) [IsFiniteMeasure ν] (hν : ν ≠ 0) :
    ∀ w ∈ Metric.ball (0 : ℂ) 1, ‖carrierExponent ν w‖ < 1 := by
  intro w hw
  have hw1 : ‖w‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hw
  exact norm_cayleyToDisc_lt_one
    (im_cauchyTransform_pos_of_ne_zero ν hν (im_cayleyToUpper_pos hw1))

/-- The bounded outer carrier as a bounded analytic multiplier of `H²(D)`. -/
def carrierMultiplier (ν : Measure ℝ) [IsFiniteMeasure ν] (hν : ν ≠ 0) : DiskMultiplier :=
  expMultiplier (differentiableOn_carrierExponent ν) (norm_carrierExponent_lt_one ν hν)

theorem carrierMultiplier_fn (ν : Measure ℝ) [IsFiniteMeasure ν] (hν : ν ≠ 0) (w : ℂ) :
    (carrierMultiplier ν hν).fn w = outerCarrier ν w := rfl

/-! ## The residual parameter measure is nonzero -/

theorem expWeightedMeasure_ne_zero (μ : Measure ℝ) (hμ : μ.support.Infinite)
    (w : ℝ → ℝ) (hw : Integrable w μ) (hwpos : ∀ x, 0 < w x) (u : Lp ℝ ⊤ μ) :
    expWeightedMeasure μ w u ≠ 0 := by
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0] at hμ
    simp [MeasureTheory.Measure.support] at hμ
  intro hzero
  have hmeas : AEMeasurable
      (fun t => ((Real.toNNReal (Real.exp (u t) * w t) : NNReal) : ENNReal)) μ := by
    refine AEMeasurable.coe_nnreal_ennreal ?_
    refine AEMeasurable.real_toNNReal ?_
    exact (Real.measurable_exp.comp_aemeasurable
      (Lp.aestronglyMeasurable u).aemeasurable).mul hw.aestronglyMeasurable.aemeasurable
  have huniv : (expWeightedMeasure μ w u) Set.univ = 0 := by rw [hzero]; rfl
  rw [expWeightedMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at huniv
  have hae := (lintegral_eq_zero_iff' hmeas).mp huniv
  have hne : ∀ t : ℝ, ((Real.toNNReal (Real.exp (u t) * w t) : NNReal) : ENNReal) ≠ 0 := by
    intro t
    have hpos : 0 < Real.exp (u t) * w t := mul_pos (Real.exp_pos _) (hwpos t)
    simp [Real.toNNReal_eq_zero, not_le, hpos]
  have hfalse : ∀ᵐ t ∂μ, False := hae.mono fun t ht => hne t ht
  exact hμ0 (MeasureTheory.ae_eq_bot.mp (Filter.eventually_false_iff_eq_bot.mp hfalse))

/-! ## The capstone -/

/-- **Hardy gauge blindness for one concrete carrier.**  For a residual set of exponential
parameters the bounded outer carrier `O` of the reweighted measure satisfies simultaneously:

* `O` is a cyclic vector of the shift on `H²(D)`;
* every finite family of distinct real parabolic translates of `O` is differentially algebraically
  independent over the rational functions;
* for every finite Blaschke product `B` and every power `N`, the parabolic orbit of `B·O` generates
  exactly the same differential field over `ℂ(w)` as the parabolic orbit of `O`;
* `[B·O] = B·H²(D)` has cyclicity defect exactly `deg B`.

So one and the same unpointed maximal-hypertranscendental power pro-field is compatible with every
finite Hardy cyclicity defect. -/
theorem hardyCyclicityGaugeBlindness_carrier
    (μ : Measure ℝ) (hμ : μ.support.Infinite)
    (w : ℝ → ℝ) (hw : Integrable w μ) (hwpos : ∀ x, 0 < w x) :
    letI := isDomain_analyticSubring openDisc isOpen_openDisc isPreconnected_openDisc
      openDisc_nonempty
    letI : Algebra (RatFunc ℂ) (meroField openDisc) :=
      (ratfuncToMero openDisc isOpen_openDisc isPreconnected_openDisc openDisc_nonempty
        openDisc_infinite).toAlgebra
    letI : Differential (RatFunc ℂ) := GaloisForLFunctions.ratFuncCoordinateDifferential
    letI := meroFieldDifferential isOpen_openDisc isPreconnected_openDisc openDisc_nonempty
    letI : DifferentialAlgebra (RatFunc ℂ) (meroField openDisc) :=
      meroFieldRatFuncDifferentialAlgebra isOpen_openDisc isPreconnected_openDisc
        openDisc_nonempty openDisc_infinite
    ∃ Ufree : Set (Lp ℝ ⊤ μ), Dense Ufree ∧ Ufree ∈ residual (Lp ℝ ⊤ μ) ∧
      ∀ u ∈ Ufree, ∃ hν : expWeightedMeasure μ w u ≠ 0,
        letI : IsFiniteMeasure (expWeightedMeasure μ w u) :=
          isFiniteMeasure_expWeightedMeasure μ w hw (fun x => (hwpos x).le) u
        -- statement 1
        (cyclicSubspace (hardyOf (carrierMultiplier (expWeightedMeasure μ w u) hν)) = ⊤) ∧
        -- statement 2
        (∀ (m : ℕ) (t : Fin m → ℝ), Function.Injective t →
          ¬ FamilyDifferentiallyAlgebraicOn
            (fun i v => outerCarrier (expWeightedMeasure μ w u) (parabolicAut (t i) v))
            openDisc) ∧
        -- statement 3
        (∀ (B : FiniteBlaschke) (N : ℕ),
          differentialAdjoin (RatFunc ℂ)
              (Set.range fun t : ℝ => (gaugedOrbitMero (expWeightedMeasure μ w u) B t) ^ N) =
            differentialAdjoin (RatFunc ℂ)
              (Set.range fun t : ℝ => (carrierOrbitMero (expWeightedMeasure μ w u) t) ^ N)) ∧
        -- statement 4
        (∀ {k : ℕ} (a : Fin k → ℂ) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (hle : ∀ j, ‖a j‖ ≤ c),
          cyclicSubspace (hardyMul (blaschkeOf a hc0 hc1 hle).toMultiplier
              (hardyOf (carrierMultiplier (expWeightedMeasure μ w u) hν)))
              = LinearMap.range ((hardyMul (blaschkeOf a hc0 hc1 hle).toMultiplier :
                HardyDisk →L[ℂ] HardyDisk) : HardyDisk →ₗ[ℂ] HardyDisk) ∧
            Module.finrank ℂ
              ((LinearMap.range ((hardyMul (blaschkeOf a hc0 hc1 hle).toMultiplier :
                HardyDisk →L[ℂ] HardyDisk) : HardyDisk →ₗ[ℂ] HardyDisk))ᗮ :
                Submodule ℂ HardyDisk) = k) := by
  letI := isDomain_analyticSubring openDisc isOpen_openDisc isPreconnected_openDisc
    openDisc_nonempty
  letI : Algebra (RatFunc ℂ) (meroField openDisc) :=
    (ratfuncToMero openDisc isOpen_openDisc isPreconnected_openDisc openDisc_nonempty
      openDisc_infinite).toAlgebra
  letI : Differential (RatFunc ℂ) := GaloisForLFunctions.ratFuncCoordinateDifferential
  letI := meroFieldDifferential isOpen_openDisc isPreconnected_openDisc openDisc_nonempty
  letI : DifferentialAlgebra (RatFunc ℂ) (meroField openDisc) :=
    meroFieldRatFuncDifferentialAlgebra isOpen_openDisc isPreconnected_openDisc
      openDisc_nonempty openDisc_infinite
  obtain ⟨Ufree, hdense, hres, hfree⟩ :=
    outerCarrier_parabolicOrbitFreeness_denseResidual μ hμ w hw hwpos
  refine ⟨Ufree, hdense, hres, ?_⟩
  intro u hu
  refine ⟨expWeightedMeasure_ne_zero μ hμ w hw hwpos u, ?_⟩
  letI : IsFiniteMeasure (expWeightedMeasure μ w u) :=
    isFiniteMeasure_expWeightedMeasure μ w hw (fun x => (hwpos x).le) u
  refine ⟨cyclicSubspace_expCarrier _ _, fun m t ht => hfree u hu m t ht,
    fun B N => gaugedOrbit_differentialAdjoin_pow_eq _ B N, ?_⟩
  intro k a c hc0 hc1 hle
  have hcyc := cyclicSubspace_expCarrier
    (differentiableOn_carrierExponent (expWeightedMeasure μ w u))
    (norm_carrierExponent_lt_one (expWeightedMeasure μ w u)
      (expWeightedMeasure_ne_zero μ hμ w hw hwpos u))
  exact ⟨cyclicSubspace_blaschke_mul _ hcyc,
    (finrank_orthogonal_range_blaschkeOf k a hc0 hc1 hle).2⟩

end GaloisForLFunctions.HTGeometry
