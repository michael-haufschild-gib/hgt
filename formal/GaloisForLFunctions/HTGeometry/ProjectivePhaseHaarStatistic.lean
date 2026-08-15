import GaloisForLFunctions.HTGeometry.FiniteEntropyPlateauFutureLaw

/-!
# The independent-phase law of a maximally projective spectrum

The survival amplitude of a finite weighted spectrum is a character sum on the product torus, and
its modulus is invariant under the diagonal phase.  It therefore factors through the torus of
relative phases anchored at any chosen level.

The relative phase flow of a maximally projective spectrum equidistributes, and the anchoring map
pushes product Haar measure to product Haar measure.  Consequently the symmetric long-time average
of every continuous statistic of the survival fidelity is its Haar average over the full phase
torus, with independent phases.
-/

open Filter MeasureTheory Set Topology UnitAddTorus

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section PhaseTransfer

variable {I : Type*} [Fintype I] [DecidableEq I]

set_option linter.unusedSectionVars false

theorem norm_fourier_eq_one (k : ℤ) (x : UnitAddCircle) : ‖fourier k x‖ = 1 :=
  Circle.norm_coe _

theorem fourier_add_point (k : ℤ) (x y : UnitAddCircle) :
    fourier k (x + y) = fourier k x * fourier k y := by
  simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

theorem fourier_mul_conj (k : ℤ) (x : UnitAddCircle) :
    fourier k x * (starRingEnd ℂ) (fourier k x) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast
  rw [norm_fourier_eq_one]
  norm_num

theorem fourier_sub_arg (k : ℤ) (a b : UnitAddCircle) :
    fourier k (a - b) = fourier k a * (starRingEnd ℂ) (fourier k b) := by
  have hadd : fourier k (a - b) * fourier k b = fourier k a := by
    rw [← fourier_add_point]
    congr 1
    abel
  calc fourier k (a - b)
      = fourier k (a - b) * (fourier k b * (starRingEnd ℂ) (fourier k b)) := by
        rw [fourier_mul_conj, mul_one]
    _ = fourier k a * (starRingEnd ℂ) (fourier k b) := by
        rw [← mul_assoc, hadd]

theorem prod_fourier_const {ι : Type*} (s : Finset ι) (k : ι → ℤ) (x : UnitAddCircle) :
    ∏ i ∈ s, fourier (k i) x = fourier (∑ i ∈ s, k i) x := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, ← fourier_add]

/-- The deterministic phase point of a frequency family at one time. -/
def timePhasePoint (omega : I → ℝ) (t : ℝ) : UnitAddTorus I :=
  fun i => ((t * omega i / (2 * Real.pi) : ℝ) : UnitAddCircle)

theorem finiteTorusPhasePoint_eq_timePhasePoint (omega : I → ℝ) (A u : ℝ) :
    finiteTorusPhasePoint omega A u = timePhasePoint omega (A * (2 * u - 1)) := by
  funext i
  rw [finiteTorusPhasePoint, timePhasePoint]

/-- The torus form of the survival amplitude. -/
def torusSurvivalAmplitude (weight : I → ℝ) (z : UnitAddTorus I) : ℂ :=
  ∑ i, (weight i : ℂ) * fourier 1 (z i)

theorem continuous_torusSurvivalAmplitude (weight : I → ℝ) :
    Continuous (torusSurvivalAmplitude weight) := by
  refine continuous_finsetSum _ fun i _ => ?_
  exact continuous_const.mul ((fourier (1 : ℤ)).continuous.comp (continuous_apply i))

theorem torusSurvivalAmplitude_timePhasePoint (weight energy : I → ℝ) (t : ℝ) :
    torusSurvivalAmplitude weight (timePhasePoint energy t) =
      finiteSpectralSurvivalAmplitude weight energy t := by
  rw [torusSurvivalAmplitude, finiteSpectralSurvivalAmplitude]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [timePhasePoint, fourier_coe_apply]
  congr 1
  push_cast
  field_simp

/-- Anchoring the phases at one level. -/
def projectiveTorusMap (ref : I) (z : UnitAddTorus I) : UnitAddTorus {i : I // i ≠ ref} :=
  fun i => z i.1 - z ref

theorem continuous_projectiveTorusMap (ref : I) : Continuous (projectiveTorusMap ref) := by
  refine continuous_pi fun i => ?_
  exact (continuous_apply i.1).sub (continuous_apply ref)

theorem projectiveTorusMap_timePhasePoint (energy : I → ℝ) (ref : I) (t : ℝ) :
    projectiveTorusMap ref (timePhasePoint energy t) =
      timePhasePoint (projectiveFrequency energy ref) t := by
  funext i
  rw [projectiveTorusMap, timePhasePoint, timePhasePoint]
  show ((t * energy i.1 / (2 * Real.pi) : ℝ) : UnitAddCircle) -
      ((t * energy ref / (2 * Real.pi) : ℝ) : UnitAddCircle) = _
  rw [← QuotientAddGroup.mk_sub]
  congr 1
  show _ = t * (energy i.1 - energy ref) / (2 * Real.pi)
  ring

/-- The relative-phase form of the survival amplitude. -/
def projectiveSurvivalAmplitude (weight : I → ℝ) (ref : I)
    (y : UnitAddTorus {i : I // i ≠ ref}) : ℂ :=
  (weight ref : ℂ) + ∑ i : {i : I // i ≠ ref}, (weight i.1 : ℂ) * fourier 1 (y i)

theorem continuous_projectiveSurvivalAmplitude (weight : I → ℝ) (ref : I) :
    Continuous (projectiveSurvivalAmplitude weight ref) := by
  refine continuous_const.add (continuous_finsetSum _ fun i _ => ?_)
  exact continuous_const.mul ((fourier (1 : ℤ)).continuous.comp (continuous_apply i))

theorem torusSurvivalAmplitude_eq (weight : I → ℝ) (ref : I) (z : UnitAddTorus I) :
    torusSurvivalAmplitude weight z =
      fourier 1 (z ref) * projectiveSurvivalAmplitude weight ref (projectiveTorusMap ref z) := by
  rw [torusSurvivalAmplitude, projectiveSurvivalAmplitude,
    Fintype.sum_eq_add_sum_subtype_ne (fun i => (weight i : ℂ) * fourier 1 (z i)) ref,
    mul_add, Finset.mul_sum]
  have hone : fourier (1 : ℤ) (z ref) * (starRingEnd ℂ) (fourier (1 : ℤ) (z ref)) = 1 :=
    fourier_mul_conj 1 (z ref)
  refine congrArg₂ (· + ·) (by ring) ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  show (weight i.1 : ℂ) * fourier 1 (z i.1) =
    fourier 1 (z ref) * ((weight i.1 : ℂ) * fourier 1 (z i.1 - z ref))
  rw [fourier_sub_arg]
  calc (weight i.1 : ℂ) * fourier 1 (z i.1)
      = (weight i.1 : ℂ) * fourier 1 (z i.1) *
        (fourier (1 : ℤ) (z ref) * (starRingEnd ℂ) (fourier (1 : ℤ) (z ref))) := by
        rw [hone, mul_one]
    _ = _ := by ring

theorem normSq_torusSurvivalAmplitude (weight : I → ℝ) (ref : I) (z : UnitAddTorus I) :
    Complex.normSq (torusSurvivalAmplitude weight z) =
      Complex.normSq (projectiveSurvivalAmplitude weight ref (projectiveTorusMap ref z)) := by
  rw [torusSurvivalAmplitude_eq weight ref z, map_mul]
  have hone : Complex.normSq (fourier (1 : ℤ) (z ref)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, norm_fourier_eq_one]
    norm_num
  rw [hone, one_mul]

end PhaseTransfer

section HaarPushforward

variable {I : Type*} [Fintype I] [DecidableEq I]

set_option linter.unusedSectionVars false

/-- The index vector obtained by anchoring a relative-phase character. -/
def anchoredIndex (ref : I) (n : {i : I // i ≠ ref} → ℤ) : I → ℤ :=
  fun j => if h : j = ref then -∑ i : {i : I // i ≠ ref}, n i else n ⟨j, h⟩

theorem mFourier_projectiveTorusMap (ref : I) (n : {i : I // i ≠ ref} → ℤ)
    (z : UnitAddTorus I) :
    mFourier n (projectiveTorusMap ref z) = mFourier (anchoredIndex ref n) z := by
  classical
  have hL : mFourier n (projectiveTorusMap ref z) =
      (∏ i : {i : I // i ≠ ref}, fourier (n i) (z i.1)) *
        fourier (-∑ i : {i : I // i ≠ ref}, n i) (z ref) := by
    show (∏ i : {i : I // i ≠ ref}, fourier (n i) (projectiveTorusMap ref z i)) = _
    have hterm : ∀ i : {i : I // i ≠ ref},
        fourier (n i) (projectiveTorusMap ref z i) =
          fourier (n i) (z i.1) * fourier (-(n i)) (z ref) := by
      intro i
      show fourier (n i) (z i.1 - z ref) = _
      rw [fourier_sub_arg, fourier_neg]
    rw [Finset.prod_congr rfl fun i _ => hterm i, Finset.prod_mul_distrib, prod_fourier_const]
    congr 2
    simp
  have hR : mFourier (anchoredIndex ref n) z =
      fourier (-∑ i : {i : I // i ≠ ref}, n i) (z ref) *
        ∏ i : {i : I // i ≠ ref}, fourier (n i) (z i.1) := by
    show (∏ j : I, fourier (anchoredIndex ref n j) (z j)) = _
    rw [Fintype.prod_eq_mul_prod_subtype_ne
      (fun j : I => fourier (anchoredIndex ref n j) (z j)) ref]
    congr 1
    · rw [anchoredIndex, dif_pos rfl]
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [anchoredIndex, dif_neg i.2]
  rw [hL, hR, mul_comm]

theorem anchoredIndex_eq_zero_iff (ref : I) (n : {i : I // i ≠ ref} → ℤ) :
    anchoredIndex ref n = 0 ↔ n = 0 := by
  classical
  constructor
  · intro h
    funext i
    have hi := congrFun h i.1
    rw [anchoredIndex, dif_neg i.2] at hi
    exact hi
  · intro h
    subst h
    funext j
    rw [anchoredIndex]
    by_cases hj : j = ref
    · rw [dif_pos hj]
      simp
    · rw [dif_neg hj]
      rfl

/-- **Anchoring pushes Haar measure to Haar measure.** -/
theorem map_projectiveTorusMap_haar (ref : I) :
    ProbabilityMeasure.map (finiteTorusHaarProbabilityMeasure I)
      (f := projectiveTorusMap ref) (continuous_projectiveTorusMap ref).aemeasurable =
      finiteTorusHaarProbabilityMeasure {i : I // i ≠ ref} := by
  refine probabilityMeasure_ext_of_mFourier_integral_eq _ _ fun n => ?_
  rw [ProbabilityMeasure.toMeasure_map,
    integral_map (continuous_projectiveTorusMap ref).aemeasurable
      ((mFourier n).continuous.aestronglyMeasurable)]
  simp_rw [mFourier_projectiveTorusMap]
  rw [finiteTorusHaarProbabilityMeasure_mFourier_integral,
    finiteTorusHaarProbabilityMeasure_mFourier_integral]
  by_cases hn : n = 0
  · rw [if_pos hn, if_pos ((anchoredIndex_eq_zero_iff ref n).mpr hn)]
  · rw [if_neg hn, if_neg (fun h => hn ((anchoredIndex_eq_zero_iff ref n).mp h))]

theorem projectiveTorusMap_finiteTorusPhasePoint (energy : I → ℝ) (ref : I) (A u : ℝ) :
    projectiveTorusMap ref (finiteTorusPhasePoint energy A u) =
      finiteTorusPhasePoint (projectiveFrequency energy ref) A u := by
  rw [finiteTorusPhasePoint_eq_timePhasePoint, finiteTorusPhasePoint_eq_timePhasePoint,
    projectiveTorusMap_timePhasePoint]

/-- **Anchoring pushes the sampled phase law to the relative phase law.** -/
theorem map_projectiveTorusMap_phaseMeasure (energy : I → ℝ) (ref : I) (A : ℝ) :
    ProbabilityMeasure.map (finiteTorusPhaseProbabilityMeasure energy A)
      (f := projectiveTorusMap ref) (continuous_projectiveTorusMap ref).aemeasurable =
      finiteTorusPhaseProbabilityMeasure (projectiveFrequency energy ref) A := by
  refine ProbabilityMeasure.toMeasure_injective ?_
  rw [ProbabilityMeasure.toMeasure_map, finiteTorusPhaseProbabilityMeasure,
    finiteTorusPhaseProbabilityMeasure, ProbabilityMeasure.toMeasure_map,
    ProbabilityMeasure.toMeasure_map,
    Measure.map_map (continuous_projectiveTorusMap ref).measurable
      (finiteTorusPhasePoint_continuous energy A).measurable]
  congr 1
  funext u
  exact projectiveTorusMap_finiteTorusPhasePoint energy ref A u

end HaarPushforward

section IndependentPhaseLaw

variable {I : Type*} [Fintype I] [DecidableEq I]

set_option linter.unusedSectionVars false

/-- The continuous statistic of the survival fidelity on the full phase torus. -/
def torusFidelityStatistic (weight : I → ℝ) (h : C(ℝ, ℂ)) : C(UnitAddTorus I, ℂ) :=
  ⟨fun z => h (Complex.normSq (torusSurvivalAmplitude weight z)), by
    exact h.continuous.comp (Complex.continuous_normSq.comp
      (continuous_torusSurvivalAmplitude weight))⟩

/-- The same statistic read on the torus of relative phases. -/
def projectiveFidelityStatistic (weight : I → ℝ) (ref : I) (h : C(ℝ, ℂ)) :
    C(UnitAddTorus {i : I // i ≠ ref}, ℂ) :=
  ⟨fun y => h (Complex.normSq (projectiveSurvivalAmplitude weight ref y)), by
    exact h.continuous.comp (Complex.continuous_normSq.comp
      (continuous_projectiveSurvivalAmplitude weight ref))⟩

theorem torusFidelityStatistic_eq (weight : I → ℝ) (ref : I) (h : C(ℝ, ℂ))
    (z : UnitAddTorus I) :
    torusFidelityStatistic weight h z =
      projectiveFidelityStatistic weight ref h (projectiveTorusMap ref z) := by
  show h (Complex.normSq (torusSurvivalAmplitude weight z)) = _
  rw [normSq_torusSurvivalAmplitude weight ref z]
  rfl

theorem integral_torusFidelityStatistic_map (weight : I → ℝ) (ref : I) (h : C(ℝ, ℂ))
    (μ : ProbabilityMeasure (UnitAddTorus I)) :
    ∫ z, torusFidelityStatistic weight h z ∂(μ : Measure (UnitAddTorus I)) =
      ∫ y, projectiveFidelityStatistic weight ref h y
        ∂((ProbabilityMeasure.map μ (f := projectiveTorusMap ref)
          (continuous_projectiveTorusMap ref).aemeasurable :
            ProbabilityMeasure (UnitAddTorus {i : I // i ≠ ref})) :
          Measure (UnitAddTorus {i : I // i ≠ ref})) := by
  rw [ProbabilityMeasure.toMeasure_map,
    integral_map (continuous_projectiveTorusMap ref).aemeasurable
      ((projectiveFidelityStatistic weight ref h).continuous.aestronglyMeasurable)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun z =>
    torusFidelityStatistic_eq weight ref h z)

/-- **The completed-time law of every continuous fidelity statistic is its Haar law.** -/
theorem integral_torusFidelityStatistic_tendsto (weight energy : I → ℝ)
    (hmax : MaximallyProjectiveEnergy energy) (ref : I) (h : C(ℝ, ℂ)) :
    Tendsto
      (fun A : ℝ => ∫ z, torusFidelityStatistic weight h z
        ∂(finiteTorusPhaseProbabilityMeasure energy A : Measure (UnitAddTorus I)))
      atTop
      (𝓝 (∫ z, torusFidelityStatistic weight h z
        ∂(finiteTorusHaarProbabilityMeasure I : Measure (UnitAddTorus I)))) := by
  have hlim := integral_projectivePhaseProbabilityMeasure_tendsto_haar energy hmax ref
    (projectiveFidelityStatistic weight ref h)
  have hleft : ∀ A : ℝ, ∫ z, torusFidelityStatistic weight h z
      ∂(finiteTorusPhaseProbabilityMeasure energy A : Measure (UnitAddTorus I)) =
      ∫ y, projectiveFidelityStatistic weight ref h y
        ∂(finiteTorusPhaseProbabilityMeasure (projectiveFrequency energy ref) A :
          Measure (UnitAddTorus {i : I // i ≠ ref})) := by
    intro A
    rw [integral_torusFidelityStatistic_map weight ref h,
      map_projectiveTorusMap_phaseMeasure energy ref A]
  have hright : ∫ z, torusFidelityStatistic weight h z
      ∂(finiteTorusHaarProbabilityMeasure I : Measure (UnitAddTorus I)) =
      ∫ y, projectiveFidelityStatistic weight ref h y
        ∂(finiteTorusHaarProbabilityMeasure {i : I // i ≠ ref} :
          Measure (UnitAddTorus {i : I // i ≠ ref})) := by
    rw [integral_torusFidelityStatistic_map weight ref h, map_projectiveTorusMap_haar ref]
  rw [hright]
  exact hlim.congr fun A => (hleft A).symm

end IndependentPhaseLaw

section TimeAverage

variable {I : Type*} [Fintype I] [DecidableEq I]

set_option linter.unusedSectionVars false

/-- The symmetric long-time average of a continuous torus statistic along the phase flow equals its
average against the sampled phase law. -/
theorem integral_phaseMeasure_eq_timeAverage (omega : I → ℝ) (g : C(UnitAddTorus I, ℂ))
    {A : ℝ} (hA : A ≠ 0) :
    ∫ z, g z ∂(finiteTorusPhaseProbabilityMeasure omega A : Measure (UnitAddTorus I)) =
      ((2 * A : ℝ) : ℂ)⁻¹ * ∫ t in (-A)..A, g (timePhasePoint omega t) := by
  rw [finiteTorusPhaseProbabilityMeasure, ProbabilityMeasure.toMeasure_map,
    integral_map (finiteTorusPhasePoint_continuous omega A).aemeasurable
      (g.continuous.aestronglyMeasurable)]
  rw [show (unitIntervalProbabilityMeasure : Measure ℝ) = volume.restrict (Ioc 0 1) from rfl,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hfun : ∀ u : ℝ, g (finiteTorusPhasePoint omega A u) =
      (fun t : ℝ => g (timePhasePoint omega t)) (2 * A * u + (-A)) := by
    intro u
    rw [finiteTorusPhasePoint_eq_timePhasePoint]
    congr 2
    ring
  rw [intervalIntegral.integral_congr (g := fun u : ℝ =>
    (fun t : ℝ => g (timePhasePoint omega t)) (2 * A * u + (-A)))
    (fun u _ => hfun u)]
  rw [intervalIntegral.integral_comp_mul_add (fun t : ℝ => g (timePhasePoint omega t))
    (by simpa using hA) (-A)]
  rw [show 2 * A * 0 + -A = -A by ring, show 2 * A * 1 + -A = A by ring]
  rw [Complex.real_smul]
  push_cast
  ring

/-- **Exact independent-phase time law.**  For a maximally projective spectrum the symmetric
long-time average of every continuous statistic of the survival fidelity is the Haar average of the
same statistic over the full phase torus, with independent phases. -/
theorem tendsto_timeAverage_fidelityStatistic (weight energy : I → ℝ)
    (hmax : MaximallyProjectiveEnergy energy) (ref : I) (h : C(ℝ, ℂ)) :
    Tendsto
      (fun A : ℝ => ((2 * A : ℝ) : ℂ)⁻¹ *
        ∫ t in (-A)..A, h (Complex.normSq (finiteSpectralSurvivalAmplitude weight energy t)))
      atTop
      (𝓝 (∫ z, h (Complex.normSq (torusSurvivalAmplitude weight z))
        ∂(finiteTorusHaarProbabilityMeasure I : Measure (UnitAddTorus I)))) := by
  have hlim := integral_torusFidelityStatistic_tendsto weight energy hmax ref h
  refine hlim.congr' ?_
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with A hA
  rw [integral_phaseMeasure_eq_timeAverage energy (torusFidelityStatistic weight h) hA]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  show h (Complex.normSq (torusSurvivalAmplitude weight (timePhasePoint energy t))) = _
  rw [torusSurvivalAmplitude_timePhasePoint]

end TimeAverage

end

end GaloisForLFunctions.HTGeometry
