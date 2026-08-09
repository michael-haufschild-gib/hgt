import GaloisForLFunctions.HTGeometry.SeparableBuresIncidenceLaw
import GaloisForLFunctions.HTGeometry.RectangularNuclearNormBound
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Probability designs for separable Bures incidence

This module turns the occupied-event construction into a genuine probability
design.  A positive-mass measurable event is normalized as a probability law;
a measurable occupied-target selector is then pushed forward to the Hilbert
space.  For compact targets in the closed unit ball, the identity target field
is Bochner `L²`, so its synthesis covariance is an honest target probability
mixture rather than an abstract auxiliary covariance.
-/

noncomputable section

namespace RHTower

open MeasureTheory
open Filter
open scoped ENNReal NNReal

variable {X H : Type*} [MeasurableSpace X]

/-- A covariance is an occupied-target probability covariance when it is the
synthesis covariance of the identity vector field under a probability law
supported almost surely on `V`. -/
def IsTargetProbabilityCovariance
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [MeasurableSpace H]
    (V : Set H) (M : H →L[ℂ] H) : Prop :=
  ∃ design : ProbabilityMeasure H,
    ∃ t : Lp H 2 (design : Measure H),
      (t : H → H) =ᵐ[(design : Measure H)] (fun y ↦ y) ∧
      (∀ᵐ y ∂(design : Measure H), y ∈ V) ∧
      M = rangeCovariance (l2Synthesis (design : Measure H) t)

/-- Multiplying a vector by a unit complex phase leaves its rank-one
covariance action unchanged. -/
theorem inner_smul_smul_eq_of_norm_one
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (p : ℂ) (hp : ‖p‖ = 1) (z q : H) :
    inner ℂ (p • z) q • (p • z) = inner ℂ z q • z := by
  rw [inner_smul_left, smul_smul]
  have hpstar : (starRingEnd ℂ) p * p = 1 := by
    rw [Complex.conj_mul', hp]
    norm_num
  rw [show (starRingEnd ℂ) p * inner ℂ z q * p = inner ℂ z q by
    calc
      (starRingEnd ℂ) p * inner ℂ z q * p =
          ((starRingEnd ℂ) p * p) * inner ℂ z q := by ring
      _ = inner ℂ z q := by rw [hpstar, one_mul]]

/-- General scalar form of rank-one covariance scaling. -/
theorem inner_smul_smul_eq_norm_sq_smul
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (c : ℂ) (z q : H) :
    inner ℂ (c • z) q • (c • z) =
      ((‖c‖ ^ 2 : ℝ) : ℂ) • (inner ℂ z q • z) := by
  rw [inner_smul_left, smul_smul, smul_smul]
  have hcstar : (starRingEnd ℂ) c * c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.conj_mul']
    norm_cast
  congr 1
  calc
    (starRingEnd ℂ) c * inner ℂ z q * c =
        ((starRingEnd ℂ) c * c) * inner ℂ z q := by ring
    _ = ((‖c‖ ^ 2 : ℝ) : ℂ) * inner ℂ z q := by rw [hcstar]

/-- Finite measure obtained by restricting a finite ambient measure to an
arbitrary event. -/
def finiteRestriction (μ : Measure X) [IsFiniteMeasure μ] (E : Set X) :
    FiniteMeasure X :=
  ⟨μ.restrict E, by infer_instance⟩

/-- The real mass of a finite restriction is exactly the ambient real mass of
the event. -/
theorem coe_mass_finiteRestriction_eq_measureReal
    (μ : Measure X) [IsFiniteMeasure μ] (E : Set X) :
    ((finiteRestriction μ E).mass : ℝ) = μ.real E := by
  rw [measureReal_def]
  change ENNReal.toReal ((finiteRestriction μ E).mass : ℝ≥0∞) =
    ENNReal.toReal (μ E)
  rw [FiniteMeasure.ennreal_mass]
  simp [finiteRestriction]

/-- Positive real event mass makes the corresponding finite restriction
nonzero. -/
theorem finiteRestriction_ne_zero
    (μ : Measure X) [IsFiniteMeasure μ] (E : Set X)
    (hE : 0 < μ.real E) :
    finiteRestriction μ E ≠ 0 := by
  apply (FiniteMeasure.mass_nonzero_iff (finiteRestriction μ E)).mp
  have hmassReal : ((finiteRestriction μ E).mass : ℝ) ≠ 0 := by
    rw [coe_mass_finiteRestriction_eq_measureReal]
    exact ne_of_gt hE
  exact_mod_cast hmassReal

/-- Probability law obtained by normalizing the restriction to an event.
For zero mass Mathlib supplies its canonical fallback; every theorem below
uses positive event mass and hence the nonzero branch. -/
def normalizedRestrictionProbability
    (μ : Measure X) [IsFiniteMeasure μ] [Nonempty X] (E : Set X) :
    ProbabilityMeasure X :=
  (finiteRestriction μ E).normalize

/-- On a positive-mass event, normalization is literal inverse-mass scaling
of the restricted measure. -/
theorem normalizedRestrictionProbability_toMeasure_eq
    (μ : Measure X) [IsFiniteMeasure μ] [Nonempty X]
    (E : Set X) (hE : 0 < μ.real E) :
    (normalizedRestrictionProbability μ E : Measure X) =
      (finiteRestriction μ E).mass⁻¹ • (μ.restrict E) := by
  exact (finiteRestriction μ E).toMeasure_normalize_eq_of_nonzero
    (finiteRestriction_ne_zero μ E hE)

/-- Bochner integration against normalized occupied mass is inverse-mass
scaling of the ambient integral with an event indicator. -/
theorem integral_normalizedRestrictionProbability_eq
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (μ : Measure X) [IsFiniteMeasure μ] [Nonempty X]
    {E : Set X} (hEmeas : MeasurableSet E) (hE : 0 < μ.real E)
  (f : X → G) :
    (∫ x, f x ∂(normalizedRestrictionProbability μ E : Measure X)) =
      (finiteRestriction μ E).mass⁻¹ •
        ∫ x, E.indicator f x ∂μ := by
  rw [normalizedRestrictionProbability_toMeasure_eq μ E hE,
    integral_smul_nnreal_measure, integral_indicator hEmeas]

/-- Complex-scalar form of normalized occupied integration. -/
theorem integral_normalizedRestrictionProbability_eq_complex
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    (μ : Measure X) [IsFiniteMeasure μ] [Nonempty X]
    {E : Set X} (hEmeas : MeasurableSet E) (hE : 0 < μ.real E)
    (f : X → G) :
    (∫ x, f x ∂(normalizedRestrictionProbability μ E : Measure X)) =
      ((((finiteRestriction μ E).mass⁻¹ : ℝ≥0) : ℝ) : ℂ) •
        ∫ x, E.indicator f x ∂μ := by
  rw [integral_normalizedRestrictionProbability_eq μ hEmeas hE f,
    NNReal.smul_def]
  exact RCLike.real_smul_eq_coe_smul (K := ℂ)
    (((finiteRestriction μ E).mass⁻¹ : ℝ≥0) : ℝ)
    (∫ x, E.indicator f x ∂μ)

/-- The normalized restriction is supported on its defining measurable
event. -/
theorem ae_normalizedRestrictionProbability_mem
    (μ : Measure X) [IsFiniteMeasure μ] [Nonempty X]
    {E : Set X} (hEmeas : MeasurableSet E) (hE : 0 < μ.real E) :
    ∀ᵐ x ∂(normalizedRestrictionProbability μ E : Measure X), x ∈ E := by
  rw [normalizedRestrictionProbability_toMeasure_eq μ E hE]
  rw [← Measure.coe_nnreal_smul]
  apply (Measure.ae_ennreal_smul_measure_iff ?_).2
  · exact ae_restrict_mem hEmeas
  · exact_mod_cast inv_ne_zero
      ((FiniteMeasure.mass_nonzero_iff (finiteRestriction μ E)).mpr
        (finiteRestriction_ne_zero μ E hE))

/-- Every measurable field bounded on the occupied event is `L²` for the
normalized restriction. -/
theorem memLp_normalizedRestrictionProbability_of_bound
    [NormedAddCommGroup H] [MeasurableSpace H] [BorelSpace H]
    [TopologicalSpace.SeparableSpace H]
    (μ : Measure X) [IsFiniteMeasure μ] [Nonempty X]
    {E : Set X} (hEmeas : MeasurableSet E) (hE : 0 < μ.real E)
    {z : X → H} (hz : Measurable z)
    (hzNorm : ∀ x ∈ E, ‖z x‖ ≤ 1) :
    MemLp z 2 (normalizedRestrictionProbability μ E : Measure X) := by
  refine MemLp.of_bound hz.aestronglyMeasurable 1 ?_
  filter_upwards [ae_normalizedRestrictionProbability_mem μ hEmeas hE] with x hx
  exact hzNorm x hx

/-- Canonical common-carrier target field: restrict to the occupied event,
correct the overlap phase, then divide by the square root of occupied mass. -/
def phaseCorrectedL2Design
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    [TopologicalSpace.SeparableSpace H]
    (μ : Measure X) [IsFiniteMeasure μ]
    {E : Set X} (hEmeas : MeasurableSet E)
    {u z : X → H} (hu : Measurable u) (hz : Measurable z)
    (hzNorm : ∀ x ∈ E, ‖z x‖ ≤ 1) : Lp H 2 μ :=
  let wfun : X → H := E.indicator
    (fun x ↦ overlapPhase (inner ℂ (u x) (z x)) • z x)
  let hwMem : MemLp wfun 2 μ :=
    memLp_indicator_overlapPhase_smul μ hEmeas hu hz hzNorm
  (((Real.sqrt (μ.real E) : ℝ) : ℂ)⁻¹) • hwMem.toLp wfun

/-- **Phase-corrected covariance is an honest probability design.**  The
common-carrier field used by the diagonal incidence lower bound has exactly
the same covariance as the selected target field under normalized occupied
mass.  Unit phase correction and square-root mass normalization introduce no
hidden covariance or subprobability loss. -/
theorem exists_phaseCorrected_l2_covariance_eq_normalized_selected
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    [TopologicalSpace.SeparableSpace H]
    (μ : Measure X) [IsFiniteMeasure μ] [Nonempty X]
    {E : Set X} (hEmeas : MeasurableSet E) (hE : 0 < μ.real E)
    {u z : X → H} (hu : Measurable u) (hz : Measurable z)
    (hzNorm : ∀ x ∈ E, ‖z x‖ ≤ 1) :
    ∃ v : Lp H 2 μ,
      v = phaseCorrectedL2Design μ hEmeas hu hz hzNorm ∧
      ‖v‖ ≤ 1 ∧
      ∀ q : H,
        rangeCovariance (l2Synthesis μ v) q =
          ∫ x, inner ℂ (z x) q • z x
            ∂(normalizedRestrictionProbability μ E : Measure X) := by
  let wfun : X → H := E.indicator
    (fun x ↦ overlapPhase (inner ℂ (u x) (z x)) • z x)
  have hwMem : MemLp wfun 2 μ :=
    memLp_indicator_overlapPhase_smul μ hEmeas hu hz hzNorm
  let w : Lp H 2 μ := hwMem.toLp wfun
  let m : ℝ := μ.real E
  let r : ℝ := Real.sqrt m
  have hm : 0 < m := hE
  have hr : 0 < r := Real.sqrt_pos.2 hm
  have hmEq : r ^ 2 = m := Real.sq_sqrt hm.le
  have hwNormSq : ‖w‖ ^ 2 ≤ m := by
    rw [HTGeometry.norm_l2_sq_eq_integral_norm_sq]
    calc
      ∫ x, ‖w x‖ ^ 2 ∂μ ≤
          ∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x ∂μ := by
        apply integral_mono_ae
        · exact (memLp_two_iff_integrable_sq_norm
            (Lp.aestronglyMeasurable w)).mp (Lp.memLp w)
        · exact (integrable_const (1 : ℝ)).indicator hEmeas
        filter_upwards [hwMem.coeFn_toLp] with x hx
        rw [show w x = wfun x by exact hx]
        by_cases hxE : x ∈ E
        · simp only [wfun, Set.indicator_of_mem hxE, norm_smul,
            overlapPhase_norm, one_mul]
          nlinarith [hzNorm x hxE, norm_nonneg (z x)]
        · simp [wfun, Set.indicator_of_notMem hxE]
      _ = m := by simp [hEmeas, m, measureReal_def]
  have hwNormLe : ‖w‖ ≤ r := by
    nlinarith [norm_nonneg w, Real.sqrt_nonneg m]
  let c : ℂ := (r : ℂ)⁻¹
  let v : Lp H 2 μ := c • w
  have hvCanonical :
      v = phaseCorrectedL2Design μ hEmeas hu hz hzNorm := by
    rfl
  have hvNorm : ‖v‖ ≤ 1 := by
    rw [show v = c • w by rfl, norm_smul, show ‖c‖ = r⁻¹ by
      simp [c, norm_inv, Complex.norm_real, Real.norm_of_nonneg hr.le]]
    simpa [div_eq_inv_mul] using (div_le_one hr).2 hwNormLe
  have hcNormSqReal :
      ‖c‖ ^ 2 = (((finiteRestriction μ E).mass⁻¹ : ℝ≥0) : ℝ) := by
    calc
      ‖c‖ ^ 2 = (r⁻¹) ^ 2 := by
        rw [show ‖c‖ = r⁻¹ by
          simp [c, norm_inv, Complex.norm_real, Real.norm_of_nonneg hr.le]]
      _ = (r ^ 2)⁻¹ := by rw [inv_pow]
      _ = m⁻¹ := by rw [hmEq]
      _ = (((finiteRestriction μ E).mass⁻¹ : ℝ≥0) : ℝ) := by
        rw [NNReal.coe_inv, coe_mass_finiteRestriction_eq_measureReal]
  have hcNormSqComplex :
      ((‖c‖ ^ 2 : ℝ) : ℂ) =
        ((((finiteRestriction μ E).mass⁻¹ : ℝ≥0) : ℝ) : ℂ) :=
    congrArg (fun t : ℝ ↦ (t : ℂ)) hcNormSqReal
  refine ⟨v, hvCanonical, hvNorm, fun q ↦ ?_⟩
  rw [rangeCovariance_l2Synthesis_apply,
    integral_normalizedRestrictionProbability_eq_complex μ hEmeas hE]
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul c w, hwMem.coeFn_toLp] with x hvx hwx
  rw [show v x = c • w x by exact hvx,
    show w x = wfun x by exact hwx]
  by_cases hxE : x ∈ E
  · simp only [wfun, Set.indicator_of_mem hxE]
    rw [inner_smul_smul_eq_norm_sq_smul,
      inner_smul_smul_eq_of_norm_one
        (overlapPhase (inner ℂ (u x) (z x)))
        (overlapPhase_norm (inner ℂ (u x) (z x))) (z x) q,
      hcNormSqComplex]
  · simp [wfun, Set.indicator_of_notMem hxE]

/-- Pushforward of normalized occupied mass by a measurable target selector:
the canonical target probability design. -/
def occupiedTargetProbability
    [MeasurableSpace H]
    (μ : Measure X) [IsFiniteMeasure μ] [Nonempty X]
    (E : Set X) (z : X → H) (hz : Measurable z) :
    ProbabilityMeasure H :=
  ProbabilityMeasure.map (normalizedRestrictionProbability μ E)
    hz.aemeasurable

/-- The occupied target probability is supported on the selected target set. -/
theorem ae_occupiedTargetProbability_mem
    [TopologicalSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure X) [IsFiniteMeasure μ] [Nonempty X]
    {E : Set X} (hEmeas : MeasurableSet E) (hE : 0 < μ.real E)
    {V : Set H} (hVcompact : IsCompact V)
    {z : X → H} (hz : Measurable z) (hzV : ∀ x ∈ E, z x ∈ V) :
    ∀ᵐ y ∂(occupiedTargetProbability μ E z hz : Measure H), y ∈ V := by
  rw [occupiedTargetProbability, ProbabilityMeasure.toMeasure_map]
  apply (ae_map_iff (p := fun y : H ↦ y ∈ V) hz.aemeasurable
    hVcompact.isClosed.measurableSet).2
  filter_upwards [ae_normalizedRestrictionProbability_mem μ hEmeas hE] with x hx
  exact hzV x hx

/-- On a compact occupied family in the closed unit ball, the identity vector
field is `L²` for the pushed-forward target probability. -/
theorem memLp_id_occupiedTargetProbability
    [NormedAddCommGroup H]
    [MeasurableSpace H] [BorelSpace H]
    [TopologicalSpace.SeparableSpace H]
    (μ : Measure X) [IsFiniteMeasure μ] [Nonempty X]
    {E : Set X} (hEmeas : MeasurableSet E) (hE : 0 < μ.real E)
    {V : Set H} (hVcompact : IsCompact V)
    (hVnorm : ∀ y ∈ V, ‖y‖ ≤ 1)
    {z : X → H} (hz : Measurable z) (hzV : ∀ x ∈ E, z x ∈ V) :
    MemLp (fun y : H ↦ y) 2
      (occupiedTargetProbability μ E z hz : Measure H) := by
  refine MemLp.of_bound
    (measurable_id : Measurable (fun y : H ↦ y)).aestronglyMeasurable 1 ?_
  filter_upwards [ae_occupiedTargetProbability_mem μ hEmeas hE hVcompact hz hzV]
    with y hy
  exact hVnorm y hy

/-- **Exact occupied-probability covariance.**  The synthesis covariance of
the identity field under the pushed-forward target probability is exactly the
normalized occupied-event integral of the selected rank-one rays.  This is
the infinite-dimensional probability-design realization used by the Bures
incidence law. -/
theorem exists_l2_occupiedTargetProbability_covariance_apply
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    [TopologicalSpace.SeparableSpace H]
    (μ : Measure X) [IsFiniteMeasure μ] [Nonempty X]
    {E : Set X} (hEmeas : MeasurableSet E) (hE : 0 < μ.real E)
    {V : Set H} (hVcompact : IsCompact V)
    (hVnorm : ∀ y ∈ V, ‖y‖ ≤ 1)
    {z : X → H} (hz : Measurable z) (hzV : ∀ x ∈ E, z x ∈ V) :
    ∃ t : Lp H 2 (occupiedTargetProbability μ E z hz : Measure H),
      (t : H → H) =ᵐ[(occupiedTargetProbability μ E z hz : Measure H)]
        (fun y ↦ y) ∧
      ∀ q : H,
        rangeCovariance
            (l2Synthesis (occupiedTargetProbability μ E z hz : Measure H) t) q =
          ∫ x, inner ℂ (z x) q • z x
            ∂(normalizedRestrictionProbability μ E : Measure X) := by
  let htMem : MemLp (fun y : H ↦ y) 2
      (occupiedTargetProbability μ E z hz : Measure H) :=
    memLp_id_occupiedTargetProbability μ hEmeas hE hVcompact hVnorm hz hzV
  let t : Lp H 2 (occupiedTargetProbability μ E z hz : Measure H) :=
    htMem.toLp (fun y : H ↦ y)
  have htCoe :
      (t : H → H) =ᵐ[(occupiedTargetProbability μ E z hz : Measure H)]
        (fun y ↦ y) := htMem.coeFn_toLp
  refine ⟨t, htCoe, fun q ↦ ?_⟩
  rw [rangeCovariance_l2Synthesis_apply]
  calc
    (∫ y, inner ℂ (t y) q • t y
        ∂(occupiedTargetProbability μ E z hz : Measure H)) =
        ∫ y, inner ℂ y q • y
          ∂(occupiedTargetProbability μ E z hz : Measure H) := by
      apply integral_congr_ae
      filter_upwards [htCoe] with y hy
      rw [hy]
    _ = ∫ x, inner ℂ (z x) q • z x
          ∂(normalizedRestrictionProbability μ E : Measure X) := by
      rw [occupiedTargetProbability, ProbabilityMeasure.toMeasure_map]
      have hfContinuous : Continuous (fun y : H ↦ inner ℂ y q • y) :=
        (continuous_inner.comp (continuous_id.prodMk continuous_const)).smul
          continuous_id
      exact integral_map hz.aemeasurable hfContinuous.aestronglyMeasurable

/-- **Probability-design realization of the phase-corrected witness.**  One
common-carrier phase-corrected field and one genuine pushed-forward target
probability field have exactly the same covariance operator.  The latter is
supported on the compact occupied family and is represented by the identity
target vector in `L²`. -/
theorem exists_phaseCorrected_probabilityDesign_covariance_eq
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    [TopologicalSpace.SeparableSpace H]
    (μ : Measure X) [IsFiniteMeasure μ] [Nonempty X]
    {E : Set X} (hEmeas : MeasurableSet E) (hE : 0 < μ.real E)
    {V : Set H} (hVcompact : IsCompact V)
    (hVnorm : ∀ y ∈ V, ‖y‖ ≤ 1)
    {u z : X → H} (hu : Measurable u) (hz : Measurable z)
    (hzV : ∀ x ∈ E, z x ∈ V) :
    ∃ v : Lp H 2 μ,
      ∃ t : Lp H 2 (occupiedTargetProbability μ E z hz : Measure H),
        v = phaseCorrectedL2Design μ hEmeas hu hz
          (fun x hx ↦ hVnorm (z x) (hzV x hx)) ∧
        ‖v‖ ≤ 1 ∧
        (t : H → H) =ᵐ[(occupiedTargetProbability μ E z hz : Measure H)]
          (fun y ↦ y) ∧
        rangeCovariance (l2Synthesis μ v) =
          rangeCovariance
            (l2Synthesis (occupiedTargetProbability μ E z hz : Measure H) t) := by
  have hzNorm : ∀ x ∈ E, ‖z x‖ ≤ 1 := fun x hx ↦ hVnorm (z x) (hzV x hx)
  obtain ⟨v, hvCanonical, hvNorm, hvCov⟩ :=
    exists_phaseCorrected_l2_covariance_eq_normalized_selected
      μ hEmeas hE hu hz hzNorm
  obtain ⟨t, htCoe, htCov⟩ :=
    exists_l2_occupiedTargetProbability_covariance_apply
      μ hEmeas hE hVcompact hVnorm hz hzV
  refine ⟨v, t, hvCanonical, hvNorm, htCoe, ?_⟩
  ext q
  exact (hvCov q).trans (htCov q).symm

/-- **Separable probability-design Bures incidence law.**  A measurable
occupied target selector on a positive-mass event produces a genuine target
probability design, supported on the compact occupied family, whose exact
Bures fidelity captures threshold squared times occupied source mass.  No
dimension, rank, target-cardinality, or fibre-sheet factor occurs. -/
theorem exists_probabilityTargetDesign_operatorBuresRootFidelity_sq_lower
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    [TopologicalSpace.SeparableSpace H]
    (μ : Measure X) [IsFiniteMeasure μ] [Nonempty X]
    {E : Set X} (hEmeas : MeasurableSet E) (hE : 0 < μ.real E)
    {V : Set H} (hVcompact : IsCompact V)
    (hVnorm : ∀ y ∈ V, ‖y‖ ≤ 1)
    {u z : X → H} (hu : Measurable u) (hz : Measurable z)
    (huLp : MemLp u 2 μ) (hzV : ∀ x ∈ E, z x ∈ V)
    (a : ℝ) (ha : 0 ≤ a)
    (hcapture : ∀ x ∈ E, a ≤ ‖inner ℂ (u x) (z x)‖) :
    ∃ t : Lp H 2 (occupiedTargetProbability μ E z hz : Measure H),
      (t : H → H) =ᵐ[(occupiedTargetProbability μ E z hz : Measure H)]
        (fun y ↦ y) ∧
      a ^ 2 * μ.real E ≤
        operatorBuresRootFidelity
          (rangeCovariance (l2Synthesis μ (huLp.toLp u)))
          (rangeCovariance
            (l2Synthesis (occupiedTargetProbability μ E z hz : Measure H) t)) ^ 2 := by
  have hzNorm : ∀ x ∈ E, ‖z x‖ ≤ 1 := fun x hx ↦ hVnorm (z x) (hzV x hx)
  obtain ⟨v, t, hvCanonical, _hvNorm, htCoe, hCovEq⟩ :=
    exists_phaseCorrected_probabilityDesign_covariance_eq
      μ hEmeas hE hVcompact hVnorm hu hz hzV
  let wfun : X → H := E.indicator
    (fun x ↦ overlapPhase (inner ℂ (u x) (z x)) • z x)
  have hwMem : MemLp wfun 2 μ :=
    memLp_indicator_overlapPhase_smul μ hEmeas hu hz hzNorm
  let w : Lp H 2 μ := hwMem.toLp wfun
  let u2 : Lp H 2 μ := huLp.toLp u
  let m : ℝ := μ.real E
  let r : ℝ := Real.sqrt m
  have hm : 0 < m := hE
  have hr : 0 < r := Real.sqrt_pos.2 hm
  have hmEq : r ^ 2 = m := Real.sq_sqrt hm.le
  have hvExplicit : v = ((r : ℂ)⁻¹) • w := by
    rw [hvCanonical]
    rfl
  let g : X → ℝ := E.indicator
    (fun x ↦ ‖inner ℂ (u x) (z x)‖)
  have hinnerW : inner ℂ u2 w = (∫ x, g x ∂μ : ℝ) := by
    rw [MeasureTheory.L2.inner_def]
    calc
      ∫ x, inner ℂ (u2 x) (w x) ∂μ =
          ∫ x, (g x : ℂ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [huLp.coeFn_toLp, hwMem.coeFn_toLp] with x hux hwx
        rw [show u2 x = u x by exact hux, show w x = wfun x by exact hwx]
        by_cases hxE : x ∈ E
        · rw [show wfun x =
              overlapPhase (inner ℂ (u x) (z x)) • z x by
                simp [wfun, Set.indicator_of_mem hxE],
            inner_overlapPhase_smul]
          simp [g, Set.indicator_of_mem hxE]
        · simp [wfun, g, Set.indicator_of_notMem hxE]
      _ = (∫ x, g x ∂μ : ℝ) := integral_ofReal
  have hgIntegrable : Integrable g μ := by
    have hint : Integrable (fun x ↦ ‖inner ℂ (u2 x) (w x)‖) μ :=
      (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) u2 w).norm
    refine hint.congr ?_
    filter_upwards [huLp.coeFn_toLp, hwMem.coeFn_toLp] with x hux hwx
    rw [show u2 x = u x by exact hux, show w x = wfun x by exact hwx]
    by_cases hxE : x ∈ E
    · rw [show wfun x =
          overlapPhase (inner ℂ (u x) (z x)) • z x by
            simp [wfun, Set.indicator_of_mem hxE],
        inner_overlapPhase_smul]
      simp [g, Set.indicator_of_mem hxE]
    · simp [wfun, g, Set.indicator_of_notMem hxE]
  have hconstIntegrable : Integrable
      (E.indicator (fun _ : X ↦ a)) μ :=
    (integrable_const a).indicator hEmeas
  have hgLower : a * m ≤ ∫ x, g x ∂μ := by
    calc
      a * m = ∫ x, E.indicator (fun _ : X ↦ a) x ∂μ := by
        simp [hEmeas, m, measureReal_def, mul_comm]
      _ ≤ ∫ x, g x ∂μ := by
        apply integral_mono_ae hconstIntegrable hgIntegrable
        filter_upwards with x
        by_cases hxE : x ∈ E
        · simpa [g, Set.indicator_of_mem hxE] using hcapture x hxE
        · simp [g, Set.indicator_of_notMem hxE]
  have hgNonneg : 0 ≤ ∫ x, g x ∂μ :=
    (mul_nonneg ha hm.le).trans hgLower
  have hoverlapNorm :
      ‖inner ℂ u2 v‖ = (∫ x, g x ∂μ) / r := by
    rw [hvExplicit, inner_smul_right,
      norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hr.le,
      hinnerW, Complex.norm_real, Real.norm_of_nonneg hgNonneg,
      div_eq_inv_mul]
  have hoverlapLower : a * r ≤ ‖inner ℂ u2 v‖ := by
    rw [hoverlapNorm, le_div_iff₀ hr]
    nlinarith [hmEq]
  have hoverlapSq :
      a ^ 2 * m ≤ ‖inner ℂ u2 v‖ ^ 2 := by
    have hsq := pow_le_pow_left₀ (mul_nonneg ha hr.le) hoverlapLower 2
    rw [mul_pow, hmEq] at hsq
    exact hsq
  refine ⟨t, htCoe, hoverlapSq.trans ?_⟩
  have hcouple := norm_inner_le_operatorBuresRootFidelity μ u2 v
  have hcoupleTarget :
      ‖inner ℂ u2 v‖ ≤
        operatorBuresRootFidelity
          (rangeCovariance (l2Synthesis μ u2))
          (rangeCovariance
            (l2Synthesis (occupiedTargetProbability μ E z hz : Measure H) t)) := by
    rw [← hCovEq]
    exact hcouple
  exact pow_le_pow_left₀ (norm_nonneg (inner ℂ u2 v)) hcoupleTarget 2

/-- Coordinate-free form of the separable probability-design incidence law:
the witnessing target label space and `L²` field are hidden behind the exact
probability-covariance predicate. -/
theorem exists_targetProbabilityCovariance_operatorBuresRootFidelity_sq_lower
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    [TopologicalSpace.SeparableSpace H]
    (μ : Measure X) [IsFiniteMeasure μ] [Nonempty X]
    {E : Set X} (hEmeas : MeasurableSet E) (hE : 0 < μ.real E)
    {V : Set H} (hVcompact : IsCompact V)
    (hVnorm : ∀ y ∈ V, ‖y‖ ≤ 1)
    {u z : X → H} (hu : Measurable u) (hz : Measurable z)
    (huLp : MemLp u 2 μ) (hzV : ∀ x ∈ E, z x ∈ V)
    (a : ℝ) (ha : 0 ≤ a)
    (hcapture : ∀ x ∈ E, a ≤ ‖inner ℂ (u x) (z x)‖) :
    ∃ M : H →L[ℂ] H,
      IsTargetProbabilityCovariance V M ∧
      a ^ 2 * μ.real E ≤
        operatorBuresRootFidelity
          (rangeCovariance (l2Synthesis μ (huLp.toLp u))) M ^ 2 := by
  obtain ⟨t, htCoe, htLower⟩ :=
    exists_probabilityTargetDesign_operatorBuresRootFidelity_sq_lower
      μ hEmeas hE hVcompact hVnorm hu hz huLp hzV a ha hcapture
  let design : ProbabilityMeasure H := occupiedTargetProbability μ E z hz
  let M : H →L[ℂ] H := rangeCovariance (l2Synthesis (design : Measure H) t)
  have hDesignV : ∀ᵐ y ∂(design : Measure H), y ∈ V :=
    ae_occupiedTargetProbability_mem μ hEmeas hE hVcompact hz hzV
  refine ⟨M, ?_, htLower⟩
  exact ⟨design, t, htCoe, hDesignV, rfl⟩

/-- **Compact complete-union probability-design law.**  For every nonempty
norm-compact target family in the closed unit ball and every positive slack,
the full continuum capture event is controlled by one genuine probability
covariance supported on that same family.  A dense sequence and first-hit
selector are internal proof devices; target count never appears in the bound.
-/
theorem exists_compact_targetProbabilityCovariance_lower
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    [TopologicalSpace.SeparableSpace H]
    (μ : Measure X) [IsFiniteMeasure μ]
    {u : X → H} (hu : Measurable u) (huLp : MemLp u 2 μ)
    (V : Set H) (hVcompact : IsCompact V) (hVnonempty : V.Nonempty)
    (hVnorm : ∀ y ∈ V, ‖y‖ ≤ 1)
    (a δ : ℝ) (hδ : 0 < δ) (hδa : δ ≤ a)
    (hEmass : 0 < μ.real (setOverlapCaptureEvent V u a)) :
    ∃ M : H →L[ℂ] H,
      IsTargetProbabilityCovariance V M ∧
      (a - δ) ^ 2 * μ.real (setOverlapCaptureEvent V u a) ≤
        operatorBuresRootFidelity
          (rangeCovariance (l2Synthesis μ (huLp.toLp u))) M ^ 2 := by
  classical
  letI : Nonempty V := hVnonempty.to_subtype
  letI : TopologicalSpace.SeparableSpace V :=
    hVcompact.isSeparable.separableSpace
  let targetV : ℕ → V := TopologicalSpace.denseSeq V
  let target : ℕ → H := fun n ↦ (targetV n : H)
  let Ecount : Set X :=
    countableOverlapCaptureEvent target u (a - δ)
  have hEcountMeas : MeasurableSet Ecount :=
    measurableSet_countableOverlapCaptureEvent target hu (a - δ)
  have hsubset : setOverlapCaptureEvent V u a ⊆ Ecount := by
    intro x hx
    obtain ⟨z, hzV, hz⟩ := hx
    let zV : V := ⟨z, hzV⟩
    let O : Set V := {w | a - δ < ‖inner ℂ (u x) (w : H)‖}
    have hcontinuous : Continuous
        (fun w : V ↦ ‖inner ℂ (u x) (w : H)‖) :=
      continuous_norm.comp
        (continuous_inner.comp (continuous_const.prodMk continuous_subtype_val))
    have hOopen : IsOpen O := isOpen_lt continuous_const hcontinuous
    have hzO : zV ∈ O := by
      change a - δ < ‖inner ℂ (u x) z‖
      linarith
    obtain ⟨n, hn⟩ :=
      (TopologicalSpace.denseRange_denseSeq V).exists_mem_open hOopen ⟨zV, hzO⟩
    exact ⟨n, le_of_lt hn⟩
  have hmeasure :
      μ.real (setOverlapCaptureEvent V u a) ≤ μ.real Ecount :=
    measureReal_mono hsubset
  have hEcountMass : 0 < μ.real Ecount := hEmass.trans_le hmeasure
  have hEcountNonempty : Ecount.Nonempty := by
    by_contra hne
    have hEmpty : Ecount = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [hEmpty] at hEcountMass
    simpa using hEcountMass
  letI : Nonempty X := ⟨hEcountNonempty.some⟩
  let p : X → ℕ → Prop := fun x n ↦
    (x ∈ Ecount ∧ a - δ ≤ ‖inner ℂ (u x) (target n)‖) ∨
      (x ∉ Ecount ∧ n = 0)
  have hp : ∀ x, ∃ n, p x n := by
    intro x
    by_cases hx : x ∈ Ecount
    · have hxCapture : ∃ n, a - δ ≤ ‖inner ℂ (u x) (target n)‖ := by
        simpa [Ecount, countableOverlapCaptureEvent] using hx
      obtain ⟨n, hn⟩ := hxCapture
      exact ⟨n, Or.inl ⟨hx, hn⟩⟩
    · exact ⟨0, Or.inr ⟨hx, rfl⟩⟩
  have hpMeasurable : ∀ n, MeasurableSet {x | p x n} := by
    intro n
    apply MeasurableSet.union
    · exact hEcountMeas.inter (measurableSet_le measurable_const
        (measurable_norm.comp
          (continuous_inner.measurable.comp (hu.prodMk measurable_const))))
    · exact hEcountMeas.compl.inter (MeasurableSet.const (n = 0))
  let select : X → ℕ := fun x ↦ Nat.find (hp x)
  have hselect : Measurable select := measurable_find hp hpMeasurable
  let z : X → H := fun x ↦ target (select x)
  have hz : Measurable z := (measurable_of_countable target).comp hselect
  have hzV : ∀ x ∈ Ecount, z x ∈ V := by
    intro x _hx
    exact (targetV (select x)).property
  have hcapture : ∀ x ∈ Ecount,
      a - δ ≤ ‖inner ℂ (u x) (z x)‖ := by
    intro x hx
    have hfound : p x (select x) := Nat.find_spec (hp x)
    rcases hfound with hgood | hbad
    · exact hgood.2
    · exact False.elim (hbad.1 hx)
  obtain ⟨M, hMdesign, hMlower⟩ :=
    exists_targetProbabilityCovariance_operatorBuresRootFidelity_sq_lower
      μ hEcountMeas hEcountMass hVcompact hVnorm hu hz huLp hzV
        (a - δ) (sub_nonneg.mpr hδa) hcapture
  refine ⟨M, hMdesign, ?_⟩
  exact (mul_le_mul_of_nonneg_left hmeasure (sq_nonneg (a - δ))).trans hMlower

/-- **Exact compact capture law in universal-upper-bound form.**  A real
number bounding the Bures fidelity squared of every target probability
covariance supported on `V` also bounds the full continuum capture mass.

This removes the positive slack from
`exists_compact_targetProbabilityCovariance_lower` without postulating a
measurable argmax or an infinite-dimensional compactness theorem: apply the
slack law at `δₙ = a / (n + 1)` and pass to the limit.  Equivalently, the
capture mass is below the least upper bound of all admissible probability
designs whenever that least upper bound is represented order-theoretically.
-/
theorem compact_capture_le_targetProbabilityCovariance_upperBound
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    [TopologicalSpace.SeparableSpace H]
    (μ : Measure X) [IsFiniteMeasure μ]
    {u : X → H} (hu : Measurable u) (huLp : MemLp u 2 μ)
    (V : Set H) (hVcompact : IsCompact V) (hVnonempty : V.Nonempty)
    (hVnorm : ∀ y ∈ V, ‖y‖ ≤ 1)
    (a : ℝ) (ha : 0 < a)
    (hEmass : 0 < μ.real (setOverlapCaptureEvent V u a))
    (K : ℝ)
    (hUpper : ∀ M : H →L[ℂ] H,
      IsTargetProbabilityCovariance V M →
        operatorBuresRootFidelity
            (rangeCovariance (l2Synthesis μ (huLp.toLp u))) M ^ 2 ≤ K) :
    a ^ 2 * μ.real (setOverlapCaptureEvent V u a) ≤ K := by
  let m : ℝ := μ.real (setOverlapCaptureEvent V u a)
  have hδLimit :
      Tendsto (fun n : ℕ ↦ a / ((n : ℝ) + 1)) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul a
  have hApprox : ∀ n : ℕ,
      (a - a / ((n : ℝ) + 1)) ^ 2 * m ≤ K := by
    intro n
    have hdenom : 0 < (n : ℝ) + 1 := by positivity
    have hδpos : 0 < a / ((n : ℝ) + 1) := div_pos ha hdenom
    have hδle : a / ((n : ℝ) + 1) ≤ a := by
      exact div_le_self ha.le (by norm_num)
    obtain ⟨M, hM, hLower⟩ :=
      exists_compact_targetProbabilityCovariance_lower
        μ hu huLp V hVcompact hVnonempty hVnorm
          a (a / ((n : ℝ) + 1)) hδpos hδle hEmass
    exact hLower.trans (hUpper M hM)
  have hLimit :
      Tendsto
        (fun n : ℕ ↦ (a - a / ((n : ℝ) + 1)) ^ 2 * m)
        atTop (nhds (a ^ 2 * m)) := by
    simpa using ((tendsto_const_nhds.sub hδLimit).pow 2).mul_const m
  simpa [m] using le_of_tendsto' hLimit hApprox

/-! ## Exact order capacity and its finite upper bound -/

/-- Bochner synthesis preserves the `L²` norm as Hilbert--Schmidt norm. -/
theorem hsNorm_l2Synthesis_eq_norm
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (μ : Measure X) (u : Lp H 2 μ) :
    ContinuousLinearMap.hsNorm (l2Synthesis μ u) = ‖u‖ := by
  rw [ContinuousLinearMap.hsNorm,
    hsNormSq_l2Synthesis_eq_norm_sq,
    Real.sqrt_sq (norm_nonneg u)]

/-- Operator Bures fidelity of two Bochner covariances obeys the sharp
Schatten Hölder bound. -/
theorem operatorBuresRootFidelity_l2_covariance_le_norm_mul_norm
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {Y : Type*} [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (u : Lp H 2 μ) (v : Lp H 2 ν) :
    operatorBuresRootFidelity
        (rangeCovariance (l2Synthesis μ u))
        (rangeCovariance (l2Synthesis ν v)) ≤ ‖u‖ * ‖v‖ := by
  rw [← rectTraceNorm_l2SheetTargetIncidence_eq_operatorBuresRootFidelity]
  have hU : (l2Synthesis μ u).IsHilbertSchmidt :=
    l2Synthesis_isHilbertSchmidt μ u
  have hV : (l2Synthesis ν v).IsHilbertSchmidt :=
    l2Synthesis_isHilbertSchmidt ν v
  have h := rectTraceNorm_comp_le_hsNorm_mul_hsNorm hV hU.adjoint
  change rectTraceNorm (Lp ℂ 2 ν) (Lp ℂ 2 μ)
      (ContinuousLinearMap.adjoint (l2Synthesis μ u) ∘L
        l2Synthesis ν v) ≤ _ at h
  have hAdjNorm : ContinuousLinearMap.hsNorm
      (ContinuousLinearMap.adjoint (l2Synthesis μ u)) =
      ContinuousLinearMap.hsNorm (l2Synthesis μ u) := by
    unfold ContinuousLinearMap.hsNorm
    rw [hU.hsNormSq_adjoint]
  rw [hAdjNorm, hsNorm_l2Synthesis_eq_norm,
    hsNorm_l2Synthesis_eq_norm] at h
  simpa [l2SheetTargetIncidence, sheetTargetIncidence, mul_comm] using h

/-- The operator Bures root fidelity is nonnegative. -/
theorem operatorBuresRootFidelity_nonneg
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (C M : H →L[ℂ] H) :
    0 ≤ operatorBuresRootFidelity C M :=
  traceNorm_nonneg _

/-- Every target probability covariance supported in the closed unit ball
has Bures fidelity squared at most the source `L²` energy. -/
theorem operatorBuresRootFidelity_sq_le_source_norm_sq_of_targetProbabilityCovariance
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    [TopologicalSpace.SeparableSpace H]
    (μ : Measure X) (u : Lp H 2 μ)
    {V : Set H} (hVnorm : ∀ y ∈ V, ‖y‖ ≤ 1)
    {M : H →L[ℂ] H} (hM : IsTargetProbabilityCovariance V M) :
    operatorBuresRootFidelity
        (rangeCovariance (l2Synthesis μ u)) M ^ 2 ≤ ‖u‖ ^ 2 := by
  obtain ⟨design, t, htCoe, htV, rfl⟩ := hM
  have htBound : ∀ᵐ y ∂(design : Measure H), ‖t y‖ ≤ 1 := by
    filter_upwards [htCoe, htV] with y hty hyV
    rw [hty]
    exact hVnorm y hyV
  have htNorm : ‖t‖ ≤ 1 := by
    have h := Lp.norm_le_of_ae_bound (p := (2 : ENNReal))
      (μ := (design : Measure H)) zero_le_one htBound
    have hmass : measureUnivNNReal (design : Measure H) = 1 := by
      simp [measureUnivNNReal]
    rw [hmass] at h
    simpa using h
  have hF := operatorBuresRootFidelity_l2_covariance_le_norm_mul_norm
    μ (design : Measure H) u t
  have hFnonneg : 0 ≤ operatorBuresRootFidelity
      (rangeCovariance (l2Synthesis μ u))
      (rangeCovariance (l2Synthesis (design : Measure H) t)) :=
    operatorBuresRootFidelity_nonneg _ _
  have hprodnonneg : 0 ≤ ‖u‖ * ‖t‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hsquare : operatorBuresRootFidelity
      (rangeCovariance (l2Synthesis μ u))
      (rangeCovariance (l2Synthesis (design : Measure H) t)) ^ 2 ≤
      (‖u‖ * ‖t‖) ^ 2 := by
    nlinarith
  calc
    operatorBuresRootFidelity
        (rangeCovariance (l2Synthesis μ u))
        (rangeCovariance (l2Synthesis (design : Measure H) t)) ^ 2 ≤
        (‖u‖ * ‖t‖) ^ 2 := hsquare
    _ ≤ ‖u‖ ^ 2 := by
      rw [mul_pow]
      calc
        ‖u‖ ^ 2 * ‖t‖ ^ 2 ≤ ‖u‖ ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left
            (by simpa using
              ((sq_le_sq₀ (norm_nonneg t) zero_le_one).2 htNorm))
            (sq_nonneg ‖u‖)
        _ = ‖u‖ ^ 2 := mul_one _

/-- Fidelity-squared values of every genuine target probability covariance. -/
def targetProbabilityBuresValueSet
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [MeasurableSpace H]
    (μ : Measure X) (u : Lp H 2 μ) (V : Set H) : Set ℝ :=
  {q | ∃ M : H →L[ℂ] H,
    IsTargetProbabilityCovariance V M ∧
    q = operatorBuresRootFidelity
      (rangeCovariance (l2Synthesis μ u)) M ^ 2}

/-- Exact order capacity of the compact target probability body.  This
definition does not assume existence of a maximizing design. -/
noncomputable def targetProbabilityBuresCapacity
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [MeasurableSpace H]
    (μ : Measure X) (u : Lp H 2 μ) (V : Set H) : ℝ :=
  sSup (targetProbabilityBuresValueSet μ u V)

theorem targetProbabilityBuresValueSet_bddAbove
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    [TopologicalSpace.SeparableSpace H]
    (μ : Measure X) (u : Lp H 2 μ)
    {V : Set H} (hVnorm : ∀ y ∈ V, ‖y‖ ≤ 1) :
    BddAbove (targetProbabilityBuresValueSet μ u V) := by
  refine ⟨‖u‖ ^ 2, ?_⟩
  rintro q ⟨M, hM, rfl⟩
  exact operatorBuresRootFidelity_sq_le_source_norm_sq_of_targetProbabilityCovariance
    μ u hVnorm hM

/-- Every admissible target probability design lies below the exact order
capacity. -/
theorem operatorBuresRootFidelity_sq_le_targetProbabilityBuresCapacity
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    [TopologicalSpace.SeparableSpace H]
    (μ : Measure X) (u : Lp H 2 μ)
    {V : Set H} (hVnorm : ∀ y ∈ V, ‖y‖ ≤ 1)
    {M : H →L[ℂ] H} (hM : IsTargetProbabilityCovariance V M) :
    operatorBuresRootFidelity
        (rangeCovariance (l2Synthesis μ u)) M ^ 2 ≤
      targetProbabilityBuresCapacity μ u V := by
  exact le_csSup (targetProbabilityBuresValueSet_bddAbove μ u hVnorm)
    ⟨M, hM, rfl⟩

/-- **Exact separable compact complete-union law.**  For every positive
threshold, full continuum capture mass is bounded by the order capacity of
all genuine target probability covariances supported on the compact target
family.  There is no slack, target count, rank, dimension, or fibre-sheet
factor. -/
theorem compact_capture_le_targetProbabilityBuresCapacity
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    [TopologicalSpace.SeparableSpace H]
    (μ : Measure X) [IsFiniteMeasure μ]
    {u : X → H} (hu : Measurable u) (huLp : MemLp u 2 μ)
    (V : Set H) (hVcompact : IsCompact V) (hVnonempty : V.Nonempty)
    (hVnorm : ∀ y ∈ V, ‖y‖ ≤ 1)
    (a : ℝ) (ha : 0 < a)
    (hEmass : 0 < μ.real (setOverlapCaptureEvent V u a)) :
    a ^ 2 * μ.real (setOverlapCaptureEvent V u a) ≤
      targetProbabilityBuresCapacity μ (huLp.toLp u) V := by
  apply compact_capture_le_targetProbabilityCovariance_upperBound
    μ hu huLp V hVcompact hVnonempty hVnorm a ha hEmass
  intro M hM
  exact operatorBuresRootFidelity_sq_le_targetProbabilityBuresCapacity
    μ (huLp.toLp u) hVnorm hM

end RHTower
