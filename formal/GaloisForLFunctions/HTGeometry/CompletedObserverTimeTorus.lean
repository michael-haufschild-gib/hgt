import GaloisForLFunctions.HTGeometry.PhaseOrbitClosureSubtorus

/-!
# Completed observer time

The completed time of a finite frequency packet is the closure of its phase orbit.  It is a
compact connected subgroup of the phase torus, isomorphic as a topological group to a torus whose
dimension is the rational rank of the packet, and the characters which are identically one on it
are exactly the resonant ones.

Uniformly sampled clock time equidistributes in completed time: the phase laws converge weakly to
the image of Haar measure under the presenting homomorphism, which is Haar measure of the completed
time itself.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d k : Type*} [Fintype d] [Fintype k]

/-- Detuning computed through an integer presentation of the frequencies. -/
theorem finiteTorusCharacterDetuning_of_integer_presentation
    (omega : d → ℝ) (gamma : k → ℝ) (M : d → k → ℤ)
    (hM : ∀ i, omega i = ∑ j, (M i j : ℝ) * gamma j) (n : d → ℤ) :
    finiteTorusCharacterDetuning n omega
      = finiteTorusCharacterDetuning (fun j => ∑ i, n i * M i j) gamma := by
  unfold finiteTorusCharacterDetuning
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => by rw [hM i, Finset.mul_sum],
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Haar probability measure of the completed time, presented as the image of Haar measure of the
presenting torus. -/
def orbitClosureHaar (M : d → k → ℤ) : ProbabilityMeasure (UnitAddTorus d) :=
  ProbabilityMeasure.map (finiteTorusHaarProbabilityMeasure k)
    (continuous_torusIntegerHom M).aemeasurable

theorem orbitClosureHaar_mFourier_integral (M : d → k → ℤ) (n : d → ℤ) :
    (∫ x, UnitAddTorus.mFourier n x ∂(orbitClosureHaar M : Measure (UnitAddTorus d)))
      = if (fun j => ∑ i, n i * M i j) = 0 then 1 else 0 := by
  rw [orbitClosureHaar, ProbabilityMeasure.toMeasure_map,
    integral_map (continuous_torusIntegerHom M).aemeasurable
      (UnitAddTorus.mFourier n).continuous.aestronglyMeasurable]
  simp_rw [mFourier_torusIntegerHom]
  rw [finiteTorusHaarProbabilityMeasure_mFourier_integral]

/-- **Equidistribution in completed time.**  Uniformly sampled clock time converges weakly to Haar
measure of the completed time. -/
theorem finiteTorusPhaseProbabilityMeasure_tendsto_orbitClosureHaar
    (omega : d → ℝ) (gamma : k → ℝ) (M : d → k → ℤ)
    (hgamma : RationallyIndependentFrequency gamma)
    (hM : ∀ i, omega i = ∑ j, (M i j : ℝ) * gamma j) :
    Tendsto (finiteTorusPhaseProbabilityMeasure omega) atTop (𝓝 (orbitClosureHaar M)) := by
  apply probabilityMeasure_tendsto_of_mFourier_integral_tendsto
  intro n
  rw [orbitClosureHaar_mFourier_integral]
  have hdet := finiteTorusCharacterDetuning_of_integer_presentation omega gamma M hM n
  have hiff : finiteTorusCharacterDetuning n omega = 0
      ↔ (fun j => ∑ i, n i * M i j) = 0 := by
    rw [hdet]
    constructor
    · intro h
      exact hgamma _ h
    · intro h
      rw [h]
      unfold finiteTorusCharacterDetuning
      simp
  by_cases hn : (fun j => ∑ i, n i * M i j) = 0
  · rw [if_pos hn]
    have hd0 : finiteTorusCharacterDetuning n omega = 0 := hiff.mpr hn
    apply tendsto_const_nhds.congr'
    filter_upwards [] with A
    rw [finiteTorusPhaseProbabilityMeasure_mFourier_integral, hd0]
    simp
  · rw [if_neg hn]
    have hd : finiteTorusCharacterDetuning n omega ≠ 0 := fun h => hn (hiff.mp h)
    have ht := symmetricPhaseAverage_tendsto_resonanceIndicator
      (finiteTorusCharacterDetuning n omega)
    simp only [if_neg hd] at ht
    apply ht.congr'
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with A hA
    rw [finiteTorusPhaseProbabilityMeasure_mFourier_integral,
      symmetricPhaseAverage_eq_sinc A (finiteTorusCharacterDetuning n omega) hA]

/-- **Resonant characters.**  A torus character is identically one on the completed time exactly
when its detuning vanishes. -/
theorem mFourier_eq_one_on_orbitClosure_iff (omega : d → ℝ) (n : d → ℤ) :
    (∀ x ∈ closure (Set.range (finiteClockPhasePoint omega)), UnitAddTorus.mFourier n x = 1)
      ↔ finiteTorusCharacterDetuning n omega = 0 := by
  constructor
  · intro h
    by_contra hdet
    have ht := h (finiteClockPhasePoint omega
      (Real.pi / finiteTorusCharacterDetuning n omega)) (subset_closure ⟨_, rfl⟩)
    rw [mFourier_finiteClockPhasePoint, div_mul_cancel₀ _ hdet] at ht
    rw [show ((Real.pi : ℝ) : ℂ) * Complex.I = (Real.pi : ℂ) * Complex.I from rfl,
      Complex.exp_pi_mul_I] at ht
    norm_num at ht
  · intro hdet x hx
    refine closure_minimal ?_
      (isClosed_eq (UnitAddTorus.mFourier n).continuous continuous_const) hx
    rintro _ ⟨t, rfl⟩
    show UnitAddTorus.mFourier n (finiteClockPhasePoint omega t) = 1
    rw [mFourier_finiteClockPhasePoint, hdet]
    simp

/-- The completed time, as a subgroup of the phase torus. -/
theorem closure_range_eq_addSubgroup_range (omega : d → ℝ) (gamma : k → ℝ) (M : d → k → ℤ)
    (hgamma : RationallyIndependentFrequency gamma)
    (hM : ∀ i, omega i = ∑ j, (M i j : ℝ) * gamma j) :
    closure (Set.range (finiteClockPhasePoint omega))
      = ((torusIntegerAddHom M).range : Set (UnitAddTorus d)) := by
  rw [closure_range_finiteClockPhasePoint_eq omega gamma M hgamma hM]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, rfl⟩

omit [Fintype d] in
/-- The completed time is connected. -/
theorem isConnected_range_torusIntegerHom (M : d → k → ℤ) :
    IsConnected (Set.range (torusIntegerHom M)) := by
  rw [← Set.image_univ]
  exact (isConnected_univ (α := UnitAddTorus k)).image _
    (continuous_torusIntegerHom M).continuousOn

omit [Fintype d] in
/-- The completed time is compact. -/
theorem isCompact_range_torusIntegerHom (M : d → k → ℤ) :
    IsCompact (Set.range (torusIntegerHom M)) := by
  rw [← Set.image_univ]
  exact isCompact_univ.image (continuous_torusIntegerHom M)

/-- **Completed time is a torus.**  An injective presentation identifies the presenting torus with
the completed time, as topological groups. -/
def orbitClosureAddEquiv {M : d → k → ℤ} (hM : Function.Injective (torusIntegerHom M)) :
    UnitAddTorus k ≃+ (torusIntegerAddHom M).range :=
  AddMonoidHom.ofInjective (f := torusIntegerAddHom M) hM

/-- The identification of the presenting torus with the completed time is a homeomorphism. -/
def orbitClosureHomeomorph {M : d → k → ℤ} (hM : Function.Injective (torusIntegerHom M)) :
    UnitAddTorus k ≃ₜ (torusIntegerAddHom M).range :=
  Continuous.homeoOfEquivCompactToT2 (f := (orbitClosureAddEquiv hM).toEquiv)
    ((continuous_torusIntegerHom M).subtype_mk _)

/-- **Observer time representation.**  The completed time of a finite frequency packet is a
compact connected subgroup of the phase torus, isomorphic as a topological group to a torus of
dimension the rational rank of the packet, whose resonant characters are exactly those with
vanishing detuning. -/
theorem exists_completedTime_representation (omega : d → ℝ) :
    ∃ (k : ℕ) (M : d → Fin k → ℤ),
      closure (Set.range (finiteClockPhasePoint omega))
          = ((torusIntegerAddHom M).range : Set (UnitAddTorus d)) ∧
        IsCompact (closure (Set.range (finiteClockPhasePoint omega))) ∧
        IsConnected (closure (Set.range (finiteClockPhasePoint omega))) ∧
        Function.Injective (torusIntegerHom M) ∧
        k = Module.finrank ℚ (Submodule.span ℚ (Set.range omega)) := by
  obtain ⟨k, gamma, M, A, hindep, -, -, hM, hA, hrank⟩ := exists_frequency_integer_basis omega
  have hclosure := closure_range_finiteClockPhasePoint_eq omega gamma M hindep hM
  refine ⟨k, M, closure_range_eq_addSubgroup_range omega gamma M hindep hM, ?_, ?_,
    torusIntegerHom_injective M A hA, hrank⟩
  · rw [hclosure]
    exact isCompact_range_torusIntegerHom M
  · rw [hclosure]
    exact isConnected_range_torusIntegerHom M

/-- **Equidistribution in completed time, without a chosen presentation.** -/
theorem exists_finiteTorusPhaseProbabilityMeasure_tendsto_orbitHaar (omega : d → ℝ) :
    ∃ (k : ℕ) (M : d → Fin k → ℤ),
      closure (Set.range (finiteClockPhasePoint omega)) = Set.range (torusIntegerHom M) ∧
        Tendsto (finiteTorusPhaseProbabilityMeasure omega) atTop (𝓝 (orbitClosureHaar M)) := by
  obtain ⟨k, gamma, M, A, hindep, -, -, hM, -, -⟩ := exists_frequency_integer_basis omega
  exact ⟨k, M, closure_range_finiteClockPhasePoint_eq omega gamma M hindep hM,
    finiteTorusPhaseProbabilityMeasure_tendsto_orbitClosureHaar omega gamma M hindep hM⟩

/-- **Full-channel law.**  The completed projective time of a finite spectrum is a torus of
dimension the rational rank of its gap packet. -/
theorem exists_projectiveCompletedTime_representation
    {I : Type*} [Fintype I] [DecidableEq I] (energy : I → ℝ) (reference : I) :
    ∃ (k : ℕ) (M : {i : I // i ≠ reference} → Fin k → ℤ),
      closure (Set.range (finiteClockPhasePoint (projectiveFrequency energy reference)))
          = ((torusIntegerAddHom M).range : Set (UnitAddTorus {i : I // i ≠ reference})) ∧
        Function.Injective (torusIntegerHom M) ∧
        k = Module.finrank ℚ
          (Submodule.span ℚ (Set.range (projectiveFrequency energy reference))) := by
  obtain ⟨k, M, hclosure, -, -, hinj, hrank⟩ :=
    exists_completedTime_representation (projectiveFrequency energy reference)
  exact ⟨k, M, hclosure, hinj, hrank⟩

end

end GaloisForLFunctions.HTGeometry
