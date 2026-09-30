import GaloisForLFunctions.RHTower.SteinhausEulerSelectedBarrier

open Complex Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section
namespace RHTower
open SteinhausModel

private theorem measurable_critical_field_joint (N : ℕ) :
    Measurable (fun x : Omega × ℝ => steinhausFiniteEulerProduct (Nat.primesBelow N)
      ((1 / 2 : ℂ) + (x.2 : ℂ) * I) x.1) := by
  have hm := measurable_steinhausFiniteEulerProduct_joint (Nat.primesBelow N)
    (fun _ hp => (Nat.mem_primesBelow.mp hp).2)
  have ht : Measurable (fun x : Omega × ℝ => (x.2 : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp measurable_snd
  have hs : Measurable (fun x : Omega × ℝ => (1 / 2 : ℂ) + (x.2 : ℂ) * I) :=
    measurable_const.add (ht.mul_const I)
  have hmap : Measurable (fun x : Omega × ℝ => (x.1, ((1 / 2 : ℂ) + (x.2 : ℂ) * I))) :=
    measurable_fst.prodMk hs
  have hcomp := hm.comp hmap
  simpa only [Function.comp_def] using hcomp

theorem measurable_steinhausEulerSpatialDensity_joint (N : ℕ) :
    Measurable (fun x : Omega × ℝ => steinhausEulerSpatialDensity N x.2 x.1) :=
  ENNReal.measurable_ofReal.comp (((measurable_critical_field_joint N).norm.pow_const 2).div_const _)

theorem measurableSet_steinhausEulerSpatialFiniteBarrier_joint (u : ℕ → ℕ) (A : ℝ) (J : ℕ) :
    MeasurableSet {x : Omega × ℝ | x.1 ∈ steinhausEulerSpatialFiniteBarrier u A J x.2} := by
  change MeasurableSet {x : Omega × ℝ | ∀ j, ∀ _ : j < J,
    Real.log ‖steinhausFiniteEulerProduct (Nat.primesBelow (u j))
      ((1 / 2 : ℂ) + (x.2 : ℂ) * I) x.1‖ -
        Real.log (steinhausEulerPartition (Nat.primesBelow (u j)) (1 / 2)) ≤
      A + 2 * Real.log (1 + steinhausEulerTiltVariance (u j))}
  simp only [setOf_forall]
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _hj
  exact measurableSet_le ((Real.measurable_log.comp
    (measurable_critical_field_joint (u j)).norm).sub_const _) measurable_const

private theorem measurable_restricted_density_joint (u : ℕ → ℕ) (A : ℝ) (J N : ℕ) :
    Measurable (fun x : Omega × ℝ =>
      (steinhausEulerSpatialFiniteBarrier u A J x.2).indicator
        (steinhausEulerSpatialDensity N x.2) x.1) := by
  have h := (measurable_steinhausEulerSpatialDensity_joint N).indicator
    (measurableSet_steinhausEulerSpatialFiniteBarrier_joint u A J)
  convert h using 1
  funext x
  by_cases hx : x.1 ∈ steinhausEulerSpatialFiniteBarrier u A J x.2
  · simp [hx]
  · simp [hx]

/-- The normalized literal critical Euler energy integrated over a unit vertical segment. -/
def steinhausEulerCriticalMass (N : ℕ) (ω : Omega) : ℝ≥0∞ :=
  ∫⁻ t in Icc (0 : ℝ) 1, steinhausEulerSpatialDensity N t ω

/-- The same mass with the whole finite spatial barrier imposed at every integration point. -/
def steinhausEulerRestrictedCriticalMass (u : ℕ → ℕ) (A : ℝ) (J N : ℕ) (ω : Omega) : ℝ≥0∞ :=
  ∫⁻ t in Icc (0 : ℝ) 1, (steinhausEulerSpatialFiniteBarrier u A J t).indicator
    (steinhausEulerSpatialDensity N t) ω

theorem measurable_steinhausEulerCriticalMass (N : ℕ) : Measurable (steinhausEulerCriticalMass N) :=
  (measurable_steinhausEulerSpatialDensity_joint N).lintegral_prod_right'

theorem measurable_steinhausEulerRestrictedCriticalMass (u : ℕ → ℕ) (A : ℝ) (J N : ℕ) :
    Measurable (steinhausEulerRestrictedCriticalMass u A J N) :=
  (measurable_restricted_density_joint u A J N).lintegral_prod_right'

/-- Tonelli preserves the exact tilted survival identity through spatial integration. -/
theorem lintegral_steinhausEulerRestrictedCriticalMass (u : ℕ → ℕ) (A : ℝ) (J N : ℕ)
    (hN : ∀ j < J, u j ≤ N) :
    (∫⁻ ω, steinhausEulerRestrictedCriticalMass u A J N ω ∂steinhausMeasure) =
      steinhausEulerTiltProductMeasure (steinhausEulerTiltFiniteBarrier u A J) := by
  unfold steinhausEulerRestrictedCriticalMass
  rw [lintegral_lintegral_swap (measurable_restricted_density_joint u A J N).aemeasurable]
  have hs (t : ℝ) : (∫⁻ ω, (steinhausEulerSpatialFiniteBarrier u A J t).indicator
      (steinhausEulerSpatialDensity N t) ω ∂steinhausMeasure) =
      steinhausEulerTiltProductMeasure (steinhausEulerTiltFiniteBarrier u A J) := by
    rw [lintegral_indicator (measurableSet_steinhausEulerSpatialFiniteBarrier u A J t)]
    exact setLIntegral_steinhausEulerSpatialFiniteBarrier_density u A J N hN t
  simp_rw [hs]
  rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
  norm_num

/-- The literal normalized critical mass has expectation exactly one at every cutoff. -/
theorem lintegral_steinhausEulerCriticalMass (N : ℕ) :
    (∫⁻ ω, steinhausEulerCriticalMass N ω ∂steinhausMeasure) = 1 := by
  have h := lintegral_steinhausEulerRestrictedCriticalMass (fun _ => 0) 0 0 N (by intro j hj; omega)
  simpa [steinhausEulerRestrictedCriticalMass, steinhausEulerSpatialFiniteBarrier,
    steinhausEulerTiltFiniteBarrier, steinhausEulerCriticalMass] using h

/-- On one good event every finite barrier restriction is inactive, for every final cutoff. -/
theorem steinhausEulerCriticalMass_eq_restricted_of_globalEnvelope (A : ℝ) (J N : ℕ) (ω : Omega)
    (hω : steinhausEulerGlobalEnvelope steinhausEulerBarrierCutoff ω ≤ ENNReal.ofReal (Real.exp (2 * A))) :
    steinhausEulerCriticalMass N ω =
      steinhausEulerRestrictedCriticalMass steinhausEulerBarrierCutoff A J N ω := by
  apply setLIntegral_congr_fun measurableSet_Icc
  intro t ht
  have hm := mem_steinhausEulerSpatialFiniteBarrier_of_globalEnvelope A ω hω J ht
  simp only [Set.indicator_of_mem hm]

/-- A quantitative probability estimate uniform over all cutoffs beyond the tested heads. -/
theorem measure_steinhausEulerCriticalMass_ge_le (A : ℝ) (J N : ℕ)
    (hN : ∀ j < J, steinhausEulerBarrierCutoff j ≤ N) {ε : ℝ} (hε : 0 < ε) :
    steinhausMeasure {ω | ENNReal.ofReal ε ≤ steinhausEulerCriticalMass N ω} ≤
      ENNReal.ofReal (steinhausEulerGlobalEnvelopeConstant * Real.exp (-(2 * A))) +
        steinhausEulerTiltProductMeasure (steinhausEulerTiltFiniteBarrier steinhausEulerBarrierCutoff A J) /
          ENNReal.ofReal ε := by
  have hsub : {ω | ENNReal.ofReal ε ≤ steinhausEulerCriticalMass N ω} ⊆
      {ω | ENNReal.ofReal (Real.exp (2 * A)) ≤ steinhausEulerGlobalEnvelope steinhausEulerBarrierCutoff ω} ∪
        {ω | ENNReal.ofReal ε ≤ steinhausEulerRestrictedCriticalMass steinhausEulerBarrierCutoff A J N ω} := by
    intro ω hω
    by_cases hb : ENNReal.ofReal (Real.exp (2 * A)) ≤
        steinhausEulerGlobalEnvelope steinhausEulerBarrierCutoff ω
    · exact Or.inl hb
    · right
      change ENNReal.ofReal ε ≤ steinhausEulerRestrictedCriticalMass steinhausEulerBarrierCutoff A J N ω
      rw [← steinhausEulerCriticalMass_eq_restricted_of_globalEnvelope A J N ω (le_of_not_ge hb)]
      exact hω
  have hmarkov := meas_ge_le_lintegral_div (μ := steinhausMeasure)
    (measurable_steinhausEulerRestrictedCriticalMass steinhausEulerBarrierCutoff A J N).aemeasurable
    (ENNReal.ofReal_ne_zero_iff.mpr hε) ENNReal.ofReal_ne_top
  rw [lintegral_steinhausEulerRestrictedCriticalMass _ _ _ _ hN] at hmarkov
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans
    (add_le_add (measure_steinhausEulerBarrier_bad_le A) hmarkov))

/-- Every prescribed positive probability tolerance holds at all sufficiently large cutoffs. -/
theorem eventually_measure_steinhausEulerCriticalMass_ge_le {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      steinhausMeasure {ω | ENNReal.ofReal ε ≤ steinhausEulerCriticalMass N ω} ≤ ENNReal.ofReal η := by
  let C := steinhausEulerGlobalEnvelopeConstant
  have hC : 0 < C := steinhausEulerGlobalEnvelopeConstant_pos
  let R := 2 * C / η
  have hR : 0 < R := by dsimp [R]; positivity
  let A := Real.log R / 2
  have hA : steinhausEulerGlobalEnvelopeConstant * Real.exp (-(2 * A)) = η / 2 := by
    have ha : 2 * A = Real.log R := by dsimp [A]; ring
    rw [ha, Real.exp_neg, Real.exp_log hR]
    change C * R⁻¹ = η / 2
    dsimp [R]
    field_simp
  have hsurv := tendsto_measure_steinhausEulerTiltFiniteBarrier steinhausEulerBarrierCutoff
    tendsto_steinhausEulerBarrierCutoff A
  obtain ⟨J, hJ⟩ := ENNReal.tendsto_atTop_zero.mp hsurv (ENNReal.ofReal (ε * η / 2))
    (ENNReal.ofReal_pos.mpr (by positivity))
  refine ⟨(Finset.range J).sup steinhausEulerBarrierCutoff, ?_⟩
  intro N hN
  have hheads : ∀ j < J, steinhausEulerBarrierCutoff j ≤ N := by
    intro j hj
    exact (Finset.le_sup (Finset.mem_range.mpr hj)).trans hN
  calc
    _ ≤ ENNReal.ofReal (steinhausEulerGlobalEnvelopeConstant * Real.exp (-(2 * A))) +
        steinhausEulerTiltProductMeasure (steinhausEulerTiltFiniteBarrier steinhausEulerBarrierCutoff A J) /
          ENNReal.ofReal ε := measure_steinhausEulerCriticalMass_ge_le A J N hheads hε
    _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (ε * η / 2) / ENNReal.ofReal ε := by
      rw [hA]
      exact add_le_add le_rfl (ENNReal.div_le_div_right (hJ J le_rfl) _)
    _ = ENNReal.ofReal η := by
      rw [← ENNReal.ofReal_div_of_pos hε]
      have hcancel : ε * η / 2 / ε = η / 2 := by field_simp
      rw [hcancel, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-- The literal normalized critical spatial mass tends to zero in probability along all cutoffs. -/
theorem tendsto_measure_steinhausEulerCriticalMass_ge {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N => steinhausMeasure {ω | ENNReal.ofReal ε ≤ steinhausEulerCriticalMass N ω})
      atTop (𝓝 0) := by
  apply ENNReal.tendsto_atTop_zero.mpr
  intro δ hδ
  by_cases htop : δ = ∞
  · subst δ
    exact ⟨0, fun _ _ => le_top⟩
  obtain ⟨N₀, hN₀⟩ := eventually_measure_steinhausEulerCriticalMass_ge_le hε
    (ENNReal.toReal_pos hδ.ne' htop)
  refine ⟨N₀, fun N hN => ?_⟩
  simpa only [ENNReal.ofReal_toReal htop] using hN₀ N hN

end RHTower
