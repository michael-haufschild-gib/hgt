import GaloisForLFunctions.RHTower.PrimeArchThetaCanonicalPlateauQuantizerOrientationWall

/-!
# Canonical monotone theta plateau and the orientation wall

The arbitrary measurable plateau construction leaves open whether the literal one-dimensional
theta order might encode the missing prime--Gamma orientation.  This file closes that possibility.

Normalize the compact Xi atomic measure on `[0,1]`, take its explicit generalized inverse, and
compose with the strictly increasing theta CDF.  The resulting reporter is nondecreasing and has
the exact Xi pushforward unconditionally.  It therefore has positive fibres over every thermal
atom and every positive thermal moment.  Nevertheless its barycenter defect is still exactly the
thermal orientation energy, so vanishing remains equivalent to RH.  Order and plateau geometry
alone are kinematic; any successful Route-Q quotient must retain source-specific arithmetic
incidence beyond the ordered pushforward law.
-/

open MeasureTheory ProbabilityTheory Set ENNReal unitInterval Filter Topology Function

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- The normalized Xi measure remains almost everywhere in the closed unit interval. -/
theorem ae_primeArchXiProbabilityMeasure_mem_unit :
    ∀ᵐ x ∂primeArchXiProbabilityMeasure, x ∈ Set.Icc (0 : ℝ) 1 := by
  have hc : (ENNReal.ofReal (normalizedPrimeArchMoment 0))⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
  rw [primeArchXiProbabilityMeasure,
    Measure.ae_ennreal_smul_measure_eq hc]
  filter_upwards [ae_primeArchXiCompactMomentMeasure_mem_zero_one] with x hx
  exact ⟨hx.1, (le_abs_self x).trans hx.2⟩

/-- Normalized compact Xi measure, restricted to its intrinsic unit-interval support. -/
def primeArchXiProbabilityMeasureUnit : Measure (Set.Icc (0 : ℝ) 1) :=
  Measure.comap Subtype.val primeArchXiProbabilityMeasure

instance primeArchXiProbabilityMeasureUnit_isProbability :
    IsProbabilityMeasure primeArchXiProbabilityMeasureUnit := by
  constructor
  rw [primeArchXiProbabilityMeasureUnit,
    comap_subtype_coe_apply measurableSet_Icc]
  have himage : Subtype.val '' (Set.univ : Set (Set.Icc (0 : ℝ) 1)) =
      Set.Icc (0 : ℝ) 1 := by
    ext x
    simp
  rw [himage]
  have hrestrict : primeArchXiProbabilityMeasure.restrict (Set.Icc (0 : ℝ) 1) =
      primeArchXiProbabilityMeasure :=
    Measure.restrict_eq_self_of_ae_mem ae_primeArchXiProbabilityMeasure_mem_unit
  have huniv := congrArg
    (fun μ : Measure ℝ => μ Set.univ) hrestrict
  simpa only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    IsProbabilityMeasure.measure_univ] using huniv

/-- Left-continuous generalized inverse of the normalized Xi compact measure. -/
def routeQXiMonotoneQuantile (t : Set.Icc (0 : ℝ) 1) :
    Set.Icc (0 : ℝ) 1 :=
  sSup {x | primeArchXiProbabilityMeasureUnit.real (Set.Icc 0 x) < t}

theorem routeQXiMonotoneQuantile_monotone :
    Monotone routeQXiMonotoneQuantile := by
  intro s t hst
  apply sSup_le_sSup
  intro x hx
  change primeArchXiProbabilityMeasureUnit.real (Set.Icc 0 x) < (s : ℝ) at hx
  change primeArchXiProbabilityMeasureUnit.real (Set.Icc 0 x) < (t : ℝ)
  exact hx.trans_le hst

theorem measurable_routeQXiMonotoneQuantile :
    Measurable routeQXiMonotoneQuantile :=
  routeQXiMonotoneQuantile_monotone.measurable

/-- The generalized inverse pushes unit Lebesgue probability exactly to the normalized compact
Xi measure, atoms included. -/
theorem map_routeQXiMonotoneQuantile_volume :
    Measure.map routeQXiMonotoneQuantile
        (volume : Measure (Set.Icc (0 : ℝ) 1)) =
      primeArchXiProbabilityMeasureUnit := by
  refine (volume.map routeQXiMonotoneQuantile).ext_of_Iic
    primeArchXiProbabilityMeasureUnit fun x => ?_
  have Iic_to_Icc : Set.Iic x = Set.Icc 0 x := by
    ext
    simp
  have hmu_in_I :
      primeArchXiProbabilityMeasureUnit.real (Set.Icc 0 x) ∈
        Set.Icc (0 : ℝ) 1 :=
    ⟨measureReal_nonneg, measureReal_le_one⟩
  simp_rw [Measure.map_apply measurable_routeQXiMonotoneQuantile measurableSet_Iic,
    preimage, mem_Iic, Iic_to_Icc,
    ← ofReal_measureReal (measure_ne_top primeArchXiProbabilityMeasureUnit _),
    ← volume_Iic ⟨_, hmu_in_I⟩]
  congr with ξ
  constructor
  · intro (hξ : routeQXiMonotoneQuantile ξ ≤ x)
    change ξ ≤ primeArchXiProbabilityMeasureUnit.real (Set.Icc 0 x)
    by_cases hx : x = 1
    · simp [hx, ← univ_eq_Icc, ξ.2.2]
    let g := fun y => primeArchXiProbabilityMeasureUnit.real (Set.Icc 0 y)
    let nebot : NeBot (𝓝[>] x) := by
      refine nhdsGT_neBot_of_exists_gt ?_
      use 1
      exact lt_of_le_of_ne x.2.2 hx
    refine le_of_tendsto_of_tendsto (b := 𝓝[>] x) (g := g)
      continuousWithinAt_const ?_ ?_
    · let h := cdf (primeArchXiProbabilityMeasureUnit.map Subtype.val)
      have h_continuousWithinAt :=
        continuousWithinAt_Ioi_iff_Ici.mpr (h.right_continuous x)
      simp_rw [g, ← unitInterval.cdf_eq_real primeArchXiProbabilityMeasureUnit]
      exact h_continuousWithinAt.comp
        (Continuous.continuousWithinAt (by fun_prop)) (fun y hy => hy)
    · refine eventually_nhdsWithin_of_forall fun y hy => ?_
      by_contra! h
      simp only [routeQXiMonotoneQuantile, sSup_le_iff] at hξ
      specialize hξ y h
      exact (not_le_of_gt hy) hξ
  · intro (hξ : ξ ≤ primeArchXiProbabilityMeasureUnit.real (Set.Icc 0 x))
    simp only [routeQXiMonotoneQuantile, sSup_le_iff]
    intro c hc
    by_contra! h
    have h_lt : ¬ primeArchXiProbabilityMeasureUnit.real (Set.Icc 0 x) ≤
        primeArchXiProbabilityMeasureUnit.real (Set.Icc 0 c) :=
      not_le.mpr (lt_of_le_of_lt' hξ hc)
    refine h_lt ?_
    gcongr
    simp

theorem map_subtypeVal_primeArchXiProbabilityMeasureUnit :
    Measure.map Subtype.val primeArchXiProbabilityMeasureUnit =
      primeArchXiProbabilityMeasure := by
  rw [primeArchXiProbabilityMeasureUnit,
    map_comap_subtype_coe measurableSet_Icc,
    Measure.restrict_eq_self_of_ae_mem
      ae_primeArchXiProbabilityMeasure_mem_unit]

/-- Explicit order-preserving reporter from the literal theta source to the canonical Xi atoms. -/
def routeQThetaMonotonePlateauReporter (x : ℝ) : ℝ :=
  ((routeQXiMonotoneQuantile (routeQThetaCdfUnit x) :
    Set.Icc (0 : ℝ) 1) : ℝ)

theorem routeQThetaMonotonePlateauReporter_monotone :
    Monotone routeQThetaMonotonePlateauReporter := by
  intro x y hxy
  change (routeQXiMonotoneQuantile (routeQThetaCdfUnit x) : ℝ) ≤
    (routeQXiMonotoneQuantile (routeQThetaCdfUnit y) : ℝ)
  apply Subtype.coe_le_coe.mpr
  apply routeQXiMonotoneQuantile_monotone
  change HedenmalmThetaSource.thetaSource.cdfFun x ≤
    HedenmalmThetaSource.thetaSource.cdfFun y
  exact HedenmalmThetaSource.thetaSource.strictMono_cdfFun.monotone hxy

theorem measurable_routeQThetaMonotonePlateauReporter :
    Measurable routeQThetaMonotonePlateauReporter := by
  exact measurable_subtype_coe.comp
    (measurable_routeQXiMonotoneQuantile.comp measurable_routeQThetaCdfUnit)

theorem map_routeQThetaMonotonePlateauReporter_law :
    Measure.map routeQThetaMonotonePlateauReporter
        HedenmalmThetaSource.thetaSource.law =
      primeArchXiProbabilityMeasure := by
  change Measure.map
      ((Subtype.val ∘ routeQXiMonotoneQuantile) ∘ routeQThetaCdfUnit)
        HedenmalmThetaSource.thetaSource.law = _
  rw [← Measure.map_map
      (measurable_subtype_coe.comp measurable_routeQXiMonotoneQuantile)
      measurable_routeQThetaCdfUnit,
    map_routeQThetaCdfUnit_law_eq_volume]
  change Measure.map (Subtype.val ∘ routeQXiMonotoneQuantile)
      (volume : Measure (Set.Icc (0 : ℝ) 1)) = _
  rw [← Measure.map_map measurable_subtype_coe
      measurable_routeQXiMonotoneQuantile,
    map_routeQXiMonotoneQuantile_volume,
    map_subtypeVal_primeArchXiProbabilityMeasureUnit]

/-- Native-mass pushforward of the explicit monotone reporter is the canonical compact Xi
measure. -/
theorem map_routeQThetaMonotonePlateauReporter_source :
    Measure.map routeQThetaMonotonePlateauReporter
        routeQThetaPlateauSourceMeasure =
      primeArchXiCompactMomentMeasure := by
  let c : ℝ≥0∞ := ENNReal.ofReal (normalizedPrimeArchMoment 0)
  have hc0 : c ≠ 0 :=
    (ENNReal.ofReal_pos.mpr normalizedPrimeArchMoment_zero_pos).ne'
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  calc
    Measure.map routeQThetaMonotonePlateauReporter
        routeQThetaPlateauSourceMeasure =
        c • Measure.map routeQThetaMonotonePlateauReporter
          HedenmalmThetaSource.thetaSource.law := by
      rw [routeQThetaPlateauSourceMeasure]
      exact Measure.map_smul c HedenmalmThetaSource.thetaSource.law
        routeQThetaMonotonePlateauReporter
    _ = c • primeArchXiProbabilityMeasure := by
      rw [map_routeQThetaMonotonePlateauReporter_law]
    _ = primeArchXiCompactMomentMeasure := by
      rw [primeArchXiProbabilityMeasure, smul_smul,
        ENNReal.mul_inv_cancel hc0 hctop, one_smul]

/-- **Route-Q monotone orientation wall.**  Even requiring the canonical one-dimensional order
does not supply source orientation: the explicit nondecreasing reporter has every positive Xi
atom as a positive fibre and the full positive thermal moment tower, while its barycenter defect
is nonnegative and vanishes exactly under RH. -/
theorem routeQThetaMonotonePlateauReporter_orientationWall :
    Monotone routeQThetaMonotonePlateauReporter ∧
      Measurable routeQThetaMonotonePlateauReporter ∧
      Measure.map routeQThetaMonotonePlateauReporter
          routeQThetaPlateauSourceMeasure =
        primeArchXiCompactMomentMeasure ∧
      (∀ j : ℕ, 0 < routeQThetaPlateauSourceMeasure
        (routeQThetaMonotonePlateauReporter ⁻¹'
          {xiThermalNode (xiThermalEnumeration j)})) ∧
      (∀ n : ℕ, ∫ x : ℝ, routeQThetaMonotonePlateauReporter x ^ n
          ∂routeQThetaPlateauSourceMeasure = xiThermalPositiveMoment n) ∧
      0 ≤ (∫ x : ℝ, routeQThetaMonotonePlateauReporter x
          ∂routeQThetaPlateauSourceMeasure) - normalizedPrimeArchMoment 1 ∧
      (((∫ x : ℝ, routeQThetaMonotonePlateauReporter x
          ∂routeQThetaPlateauSourceMeasure) - normalizedPrimeArchMoment 1 = 0) ↔
        RiemannHypothesis) ∧
      (IsPrimeArchObservableWitness routeQThetaPlateauSourceMeasure
          routeQThetaMonotonePlateauReporter ↔ RiemannHypothesis) := by
  let hQ := measurable_routeQThetaMonotonePlateauReporter
  let hmap := map_routeQThetaMonotonePlateauReporter_source
  refine ⟨routeQThetaMonotonePlateauReporter_monotone, hQ, hmap,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact fun j => routeQThetaPlateauReporter_levelSet_pos hQ hmap j
  · exact fun n => integral_routeQThetaPlateauReporter_pow hQ hmap n
  · exact routeQThetaPlateauReporter_firstMomentDefect_nonneg hQ hmap
  · exact routeQThetaPlateauReporter_firstMomentDefect_eq_zero_iff_rh hQ hmap
  · exact routeQThetaPlateauReporter_isWitness_iff_rh hQ hmap

end

end RHTower
