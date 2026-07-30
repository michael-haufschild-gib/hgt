import GaloisForLFunctions.HTGeometry.ObserverActionRecurrenceProjectionLaw
import GaloisForLFunctions.HTGeometry.RationalIndependentWeights

/-!
# Universal clock-sampling phase law

An observation protocol is a probability law of readout times.  Its
characteristic function, evaluated on each spectral detuning, is exactly the
Fourier transform of the induced phase-history law.  This replaces the
uniform-window sinc kernel by an arbitrary clock transfer function.

For finite and countable spectra, convergence of all these coefficients is
necessary and sufficient for convergence of the entire phase law.  At fixed
scale, characters at which the clock characteristic function equals one are
exactly the hidden aliases; observable temporal rank plus their rank is
conserved.
-/

open Filter MeasureTheory Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Phase point generated at an arbitrary real sampled time. -/
def finiteClockPhasePoint
    {d : Type*} [Fintype d]
    (omega : d → ℝ) (t : ℝ) : UnitAddTorus d :=
  fun i =>
    ((t * omega i / (2 * Real.pi) : ℝ) : UnitAddCircle)

/-- The finite phase point depends continuously on sampled time. -/
theorem finiteClockPhasePoint_continuous
    {d : Type*} [Fintype d] (omega : d → ℝ) :
    Continuous (finiteClockPhasePoint omega) := by
  unfold finiteClockPhasePoint
  apply continuous_pi
  intro i
  exact
    (AddCircle.continuous_mk' (1 : ℝ)).comp
      (by fun_prop)

/-- Phase law produced by an arbitrary probability distribution of readout
times. -/
def finiteClockSampledPhaseProbabilityMeasure
    {d : Type*} [Fintype d]
    (clockLaw : ProbabilityMeasure ℝ) (omega : d → ℝ) :
    ProbabilityMeasure (UnitAddTorus d) :=
  ProbabilityMeasure.map clockLaw
    (f := finiteClockPhasePoint omega)
    (finiteClockPhasePoint_continuous omega).aemeasurable

/-- Evaluation of a torus character at one arbitrary sampled time. -/
theorem mFourier_finiteClockPhasePoint
    {d : Type*} [Fintype d]
    (n : d → ℤ) (omega : d → ℝ) (t : ℝ) :
    UnitAddTorus.mFourier n
        (finiteClockPhasePoint omega t) =
      Complex.exp
        (((t * finiteTorusCharacterDetuning n omega : ℝ) : ℂ) *
          Complex.I) := by
  rw [UnitAddTorus.mFourier]
  simp only [ContinuousMap.coe_mk, finiteClockPhasePoint,
    fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  simp only [finiteTorusCharacterDetuning]
  push_cast
  field_simp [Real.pi_ne_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- **Clock transfer law.** Every phase coefficient is the clock
characteristic function at the corresponding spectral detuning. -/
theorem finiteClockSampledPhaseProbabilityMeasure_mFourier_integral
    {d : Type*} [Fintype d]
    (clockLaw : ProbabilityMeasure ℝ)
    (n : d → ℤ) (omega : d → ℝ) :
    (∫ x, UnitAddTorus.mFourier n x
        ∂(finiteClockSampledPhaseProbabilityMeasure clockLaw omega :
          Measure (UnitAddTorus d))) =
      charFun (clockLaw : Measure ℝ)
        (finiteTorusCharacterDetuning n omega) := by
  rw [finiteClockSampledPhaseProbabilityMeasure,
    ProbabilityMeasure.toMeasure_map]
  rw [integral_map
    (finiteClockPhasePoint_continuous omega).aemeasurable
    (by fun_prop)]
  simp_rw [mFourier_finiteClockPhasePoint]
  rw [charFun_apply_real]
  apply integral_congr_ae
  filter_upwards with t
  congr 1
  push_cast
  ring

/-- **Arbitrary-clock recurrence projection.** Expected survival fidelity
is the gap-weighted clock transfer function. -/
theorem integral_finiteWeightedReturnPolynomial_clockSampled
    {d : Type*} [Fintype d]
    (clockLaw : ProbabilityMeasure ℝ)
    (weight omega : d → ℝ) :
    (∫ x, finiteWeightedReturnPolynomial weight x
        ∂(finiteClockSampledPhaseProbabilityMeasure
          clockLaw omega : Measure (UnitAddTorus d))) =
      ∑ p : d × d,
        ((weight p.1 * weight p.2 : ℝ) : ℂ) *
          charFun (clockLaw : Measure ℝ)
            (omega p.1 - omega p.2) := by
  rw [finiteWeightedReturnPolynomial,
    integral_projectiveCharacterPolynomial]
  apply Finset.sum_congr rfl
  intro p hp
  rw [projectivePhaseLawFourierCoefficient,
    finiteClockSampledPhaseProbabilityMeasure_mFourier_integral,
    finiteTorusCharacterDetuning_finiteCharacterOfProjective,
    finiteProjectiveCharacterDetuning_pair]

/-- Characteristic-function convergence for every spectral character. -/
def HasCompleteFiniteClockSamplingLimits
    {α d : Type*} [Fintype d]
    (l : Filter α)
    (clockLaw : α → ProbabilityMeasure ℝ)
    (omega : α → d → ℝ) : Prop :=
  ∀ n : d → ℤ, ∃ c : ℂ,
    Tendsto
      (fun x =>
        charFun (clockLaw x : Measure ℝ)
          (finiteTorusCharacterDetuning n (omega x)))
      l (𝓝 c)

/-- **Arbitrary-sampling finite phase law.** For every family of
probability laws of observation times, finite phase histories have a unique
weak limit exactly when the clock characteristic function converges on
every integer spectral detuning. -/
theorem existsUnique_finiteClockSampledPhaseLimit_iff_complete
    {α d : Type*} [Fintype d]
    {l : Filter α} [l.NeBot]
    (clockLaw : α → ProbabilityMeasure ℝ)
    (omega : α → d → ℝ) :
    (∃! μ : ProbabilityMeasure (UnitAddTorus d),
      Tendsto
        (fun x =>
          finiteClockSampledPhaseProbabilityMeasure
            (clockLaw x) (omega x))
        l (𝓝 μ)) ↔
      HasCompleteFiniteClockSamplingLimits l clockLaw omega := by
  constructor
  · rintro ⟨μ, hμ, hμunique⟩
    intro n
    refine
      ⟨∫ y, UnitAddTorus.mFourier n y
          ∂(μ : Measure (UnitAddTorus d)), ?_⟩
    have hcoefficient :=
      (continuous_integral_complex_continuousMap
        (UnitAddTorus.mFourier n)).continuousAt.tendsto.comp hμ
    apply hcoefficient.congr'
    filter_upwards [] with x
    simp only [Function.comp_apply]
    exact
      finiteClockSampledPhaseProbabilityMeasure_mFourier_integral
        (clockLaw x) n (omega x)
  · intro hcomplete
    choose limit hlimit using hcomplete
    have hcoefficient : ∀ n : d → ℤ,
        Tendsto
          (fun x =>
            ∫ y, UnitAddTorus.mFourier n y
              ∂(finiteClockSampledPhaseProbabilityMeasure
                (clockLaw x) (omega x) :
                  Measure (UnitAddTorus d)))
          l (𝓝 (limit n)) := by
      intro n
      apply (hlimit n).congr'
      filter_upwards [] with x
      symm
      exact
        finiteClockSampledPhaseProbabilityMeasure_mFourier_integral
          (clockLaw x) n (omega x)
    obtain ⟨μ, hμ, hμunique⟩ :=
      existsUnique_probabilityMeasure_tendsto_of_mFourier_limit
        (fun x =>
          finiteClockSampledPhaseProbabilityMeasure
            (clockLaw x) (omega x))
        limit hcoefficient
    refine ⟨μ, hμ.1, ?_⟩
    intro ν hν
    exact tendsto_nhds_unique hν hμ.1

/-- Rational span of projective characters hidden by exact clock
aliases. -/
def clockSamplingConstraintRationalSpace
    {d : Type*} [Fintype d]
    (clockLaw : ProbabilityMeasure ℝ) (omega : d → ℝ) :
    Submodule ℚ (ProjectiveRationalCharacter d) :=
  Submodule.span ℚ
    (projectiveCharacterToRational ''
      {k : ProjectiveCharacter d |
        charFun (clockLaw : Measure ℝ)
          (finiteTorusCharacterDetuning
            (finiteCharacterOfProjective k) omega) = 1})

/-- A projective relation is hidden exactly when the clock transfer
function equals one at its detuning. -/
theorem phaseLawConstraint_iff_clockCharacteristic_eq_one
    {d : Type*} [Fintype d]
    (clockLaw : ProbabilityMeasure ℝ) (omega : d → ℝ)
    (k : ProjectiveCharacter d) :
    phaseLawConstraint
        (finiteClockSampledPhaseProbabilityMeasure
          clockLaw omega) k ↔
      charFun (clockLaw : Measure ℝ)
        (finiteTorusCharacterDetuning
          (finiteCharacterOfProjective k) omega) = 1 := by
  rw [phaseLawConstraint_iff_integral_eq_one,
    finiteClockSampledPhaseProbabilityMeasure_mFourier_integral]

/-- The complete phase-law constraint space is the clock-alias space. -/
theorem phaseLawConstraintRationalSpace_clockSampled_eq
    {d : Type*} [Fintype d]
    (clockLaw : ProbabilityMeasure ℝ) (omega : d → ℝ) :
    phaseLawConstraintRationalSpace
        (finiteClockSampledPhaseProbabilityMeasure clockLaw omega) =
      clockSamplingConstraintRationalSpace clockLaw omega := by
  rw [phaseLawConstraintRationalSpace,
    clockSamplingConstraintRationalSpace]
  congr 1
  ext q
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact
      ⟨k,
        (phaseLawConstraint_iff_clockCharacteristic_eq_one
          clockLaw omega k).mp hk,
        rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact
      ⟨k,
        (phaseLawConstraint_iff_clockCharacteristic_eq_one
          clockLaw omega k).mpr hk,
        rfl⟩

/-- **Clock-dependent temporal dimension.** For every time-sampling law,
observable temporal dimension is complete projective rank minus the rank of
clock-aliased spectral relations. -/
theorem finiteClockSampled_temporalDimension_eq_quotientRank
    {d : Type*} [Fintype d]
    (clockLaw : ProbabilityMeasure ℝ) (omega : d → ℝ) :
    phaseLawTemporalDimension
        (finiteClockSampledPhaseProbabilityMeasure clockLaw omega) =
      Module.finrank ℚ (ProjectiveRationalCharacter d) -
        Module.finrank ℚ
          (clockSamplingConstraintRationalSpace
            clockLaw omega) := by
  unfold phaseLawTemporalDimension
  rw [phaseLawConstraintRationalSpace_clockSampled_eq]

/-- **Clock-sampling rank conservation.** Resolved temporal rank plus the
rank hidden by sampling aliases is constant for every probability clock. -/
theorem finiteClockSampled_temporalDimension_add_aliasRank
    {d : Type*} [Fintype d]
    (clockLaw : ProbabilityMeasure ℝ) (omega : d → ℝ) :
    phaseLawTemporalDimension
        (finiteClockSampledPhaseProbabilityMeasure clockLaw omega) +
      Module.finrank ℚ
        (clockSamplingConstraintRationalSpace clockLaw omega) =
      Module.finrank ℚ (ProjectiveRationalCharacter d) := by
  rw [finiteClockSampled_temporalDimension_eq_quotientRank]
  have hle :
      Module.finrank ℚ
          (clockSamplingConstraintRationalSpace clockLaw omega) ≤
        Module.finrank ℚ (ProjectiveRationalCharacter d) :=
    Submodule.finrank_le _
  omega

/-- Clock that reads the system only at time zero. -/
def zeroClockProbabilityMeasure : ProbabilityMeasure ℝ :=
  ⟨Measure.dirac 0, Measure.dirac.isProbabilityMeasure⟩

/-- Integral projective characters rationally span the full projective
character space. -/
theorem span_projectiveCharacterToRational_range_eq_top
    {d : Type*} [Fintype d] :
    Submodule.span ℚ
        (Set.range
          (projectiveCharacterToRational :
            ProjectiveCharacter d → ProjectiveRationalCharacter d)) =
      ⊤ := by
  apply top_unique
  intro q hq
  obtain ⟨b, hb, k, hk⟩ :=
    exists_integer_projective_multiple q
  have hgenerator :
      projectiveCharacterToRational k ∈
        Set.range
          (projectiveCharacterToRational :
            ProjectiveCharacter d →
              ProjectiveRationalCharacter d) :=
    ⟨k, rfl⟩
  have hspan :
      projectiveCharacterToRational k ∈
        Submodule.span ℚ
          (Set.range
            (projectiveCharacterToRational :
              ProjectiveCharacter d →
                ProjectiveRationalCharacter d)) :=
    Submodule.subset_span hgenerator
  rw [hk] at hspan
  have hbinv : (b : ℚ)⁻¹ • ((b : ℚ) • q) = q := by
    rw [← mul_smul]
    simp [hb]
  rw [← hbinv]
  exact Submodule.smul_mem _ _ hspan

/-- Clock that samples at one deterministic, not necessarily zero, time. -/
def deterministicClockProbabilityMeasure (t : ℝ) :
    ProbabilityMeasure ℝ :=
  ⟨Measure.dirac t, Measure.dirac.isProbabilityMeasure⟩

/-- Transfer function of a deterministic clock. -/
theorem charFun_deterministicClockProbabilityMeasure
    (t ξ : ℝ) :
    charFun
        (deterministicClockProbabilityMeasure t : Measure ℝ) ξ =
      Complex.exp (((t * ξ : ℝ) : ℂ) * Complex.I) := by
  change charFun (Measure.dirac t) ξ =
    Complex.exp (((t * ξ : ℝ) : ℂ) * Complex.I)
  rw [charFun_dirac]
  congr 1
  simp [mul_comm]

/-- The two-level spectrum with unit energy gap. -/
def unitGapTwoLevelSpectrum : Fin 2 → ℝ := ![0, 1]

/-- Every projective detuning of the unit-gap two-level spectrum is the
integer coefficient at its excited level. -/
theorem unitGapTwoLevelSpectrum_detuning
    (k : ProjectiveCharacter (Fin 2)) :
    finiteTorusCharacterDetuning
        (finiteCharacterOfProjective k)
        unitGapTwoLevelSpectrum =
      k.1 1 := by
  simp [finiteTorusCharacterDetuning, finiteCharacterOfProjective,
    unitGapTwoLevelSpectrum, Fin.sum_univ_two]

/-- The unit-gap two-level spectrum has no nonzero exact projective
resonance. -/
theorem unitGapTwoLevelSpectrum_projectiveFaithful :
    ∀ k : ProjectiveCharacter (Fin 2),
      finiteTorusCharacterDetuning
        (finiteCharacterOfProjective k)
        unitGapTwoLevelSpectrum = 0 →
          k = 0 := by
  intro k hdetuning
  have hk1 : k.1 1 = 0 := by
    rw [unitGapTwoLevelSpectrum_detuning] at hdetuning
    exact_mod_cast hdetuning
  have hcharge : k.1 0 + k.1 1 = 0 := by
    have hk := k.property
    change k.1.sum (fun _ m => m) = 0 at hk
    rw [Finsupp.sum_fintype] at hk
    · simpa [Fin.sum_univ_two] using hk
    · intro i
      simp
  have hk0 : k.1 0 = 0 := by omega
  apply Subtype.ext
  ext i
  fin_cases i
  · exact hk0
  · exact hk1

/-- A deterministic clock reading at one nonzero full-revival time aliases
every projective character of the unit-gap two-level spectrum. -/
theorem deterministicFullRevivalClock_constraintSpace_eq_top :
    clockSamplingConstraintRationalSpace
        (deterministicClockProbabilityMeasure (2 * Real.pi))
        unitGapTwoLevelSpectrum = ⊤ := by
  rw [clockSamplingConstraintRationalSpace]
  have hall :
      {k : ProjectiveCharacter (Fin 2) |
        charFun
            (deterministicClockProbabilityMeasure
              (2 * Real.pi) : Measure ℝ)
            (finiteTorusCharacterDetuning
              (finiteCharacterOfProjective k)
              unitGapTwoLevelSpectrum) = 1} =
        Set.univ := by
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    rw [charFun_deterministicClockProbabilityMeasure,
      unitGapTwoLevelSpectrum_detuning]
    convert
      Complex.exp_int_mul_two_pi_mul_I (k.1 1) using 1 <;>
        push_cast <;> ring
  rw [hall, Set.image_univ]
  exact span_projectiveCharacterToRational_range_eq_top

/-- A time-zero clock aliases every projective character. -/
theorem zeroClock_constraintSpace_eq_top
    {d : Type*} [Fintype d] (omega : d → ℝ) :
    clockSamplingConstraintRationalSpace
        zeroClockProbabilityMeasure omega = ⊤ := by
  rw [clockSamplingConstraintRationalSpace]
  have hall :
      {k : ProjectiveCharacter d |
        charFun (zeroClockProbabilityMeasure : Measure ℝ)
          (finiteTorusCharacterDetuning
            (finiteCharacterOfProjective k) omega) = 1} =
        Set.univ := by
    ext k
    simp [zeroClockProbabilityMeasure, charFun_dirac]
  rw [hall, Set.image_univ]
  exact span_projectiveCharacterToRational_range_eq_top

/-- A clock that samples uniformly on the centered interval `[-A,A]`. -/
def centeredUniformClockProbabilityMeasure (A : ℝ) :
    ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map unitIntervalProbabilityMeasure
    (f := fun u : ℝ => A * (2 * u - 1))
    (by fun_prop)

/-- The centered uniform clock has the sinc transfer function. -/
theorem charFun_centeredUniformClockProbabilityMeasure
    (A ξ : ℝ) :
    charFun
        (centeredUniformClockProbabilityMeasure A : Measure ℝ) ξ =
      Real.sinc (A * ξ) := by
  rw [centeredUniformClockProbabilityMeasure,
    ProbabilityMeasure.toMeasure_map]
  rw [charFun_apply_real]
  rw [integral_map (by fun_prop) (by fun_prop)]
  rw [show
    (unitIntervalProbabilityMeasure : Measure ℝ) =
      volume.restrict (Set.Ioc 0 1) by rfl]
  rw [← intervalIntegral.integral_of_le
    (by norm_num : (0 : ℝ) ≤ 1)]
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    interval_exp_centered_eq_sinc (A * ξ)

/-- A nonzero continuous-window clock has no aliases when the spectrum has
no nontrivial projective resonance. -/
theorem centeredUniformClock_constraintSpace_eq_bot
    {d : Type*} [Fintype d]
    (omega : d → ℝ)
    (hfaithful : ∀ k : ProjectiveCharacter d,
      finiteTorusCharacterDetuning
        (finiteCharacterOfProjective k) omega = 0 →
          k = 0)
    {A : ℝ} (hA : A ≠ 0) :
    clockSamplingConstraintRationalSpace
        (centeredUniformClockProbabilityMeasure A) omega = ⊥ := by
  rw [clockSamplingConstraintRationalSpace]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro q ⟨k, hk, rfl⟩
    have hproduct :
        A * finiteTorusCharacterDetuning
          (finiteCharacterOfProjective k) omega = 0 := by
      rw [← coe_real_sinc_eq_one_iff]
      simpa [charFun_centeredUniformClockProbabilityMeasure] using hk
    have hdetuning :
        finiteTorusCharacterDetuning
          (finiteCharacterOfProjective k) omega = 0 := by
      exact (mul_eq_zero.mp hproduct).resolve_left hA
    have hkzero := hfaithful k hdetuning
    subst k
    change projectiveCharacterToRational
      (0 : ProjectiveCharacter d) = 0
    ext i
    rfl
  · exact bot_le

/-- **Same-spectrum clock separation.** One Hamiltonian with no projective
resonance has temporal dimension zero for a time-zero clock and maximal
projective temporal dimension for every nonzero centered continuous-window
clock. Only the observation-time law changes. -/
theorem sameSpectrum_twoClockTemporalDimensions
    {d : Type*} [Fintype d]
    (omega : d → ℝ)
    (hfaithful : ∀ k : ProjectiveCharacter d,
      finiteTorusCharacterDetuning
        (finiteCharacterOfProjective k) omega = 0 →
          k = 0)
    {A : ℝ} (hA : A ≠ 0) :
    phaseLawTemporalDimension
        (finiteClockSampledPhaseProbabilityMeasure
          zeroClockProbabilityMeasure omega) = 0 ∧
      phaseLawTemporalDimension
        (finiteClockSampledPhaseProbabilityMeasure
          (centeredUniformClockProbabilityMeasure A) omega) =
        Module.finrank ℚ (ProjectiveRationalCharacter d) := by
  constructor
  · rw [finiteClockSampled_temporalDimension_eq_quotientRank,
      zeroClock_constraintSpace_eq_top]
    simp
  · rw [finiteClockSampled_temporalDimension_eq_quotientRank,
      centeredUniformClock_constraintSpace_eq_bot
        omega hfaithful hA]
    simp

/-- **Nonzero-clock dimensional fracture.** For one fixed two-level
Hamiltonian, a deterministic clock at the nonzero full-revival time has
temporal dimension zero, whereas every nonzero centered continuous-window
clock has maximal projective temporal dimension. -/
theorem unitGapTwoLevelSpectrum_fullRevival_vs_continuous_dimensions
    {A : ℝ} (hA : A ≠ 0) :
    phaseLawTemporalDimension
        (finiteClockSampledPhaseProbabilityMeasure
          (deterministicClockProbabilityMeasure (2 * Real.pi))
          unitGapTwoLevelSpectrum) = 0 ∧
      phaseLawTemporalDimension
        (finiteClockSampledPhaseProbabilityMeasure
          (centeredUniformClockProbabilityMeasure A)
          unitGapTwoLevelSpectrum) =
        Module.finrank ℚ
          (ProjectiveRationalCharacter (Fin 2)) := by
  constructor
  · rw [finiteClockSampled_temporalDimension_eq_quotientRank,
      deterministicFullRevivalClock_constraintSpace_eq_top]
    simp
  · rw [finiteClockSampled_temporalDimension_eq_quotientRank,
      centeredUniformClock_constraintSpace_eq_bot
        unitGapTwoLevelSpectrum
        unitGapTwoLevelSpectrum_projectiveFaithful hA]
    simp

/-- The canonical finite rationally independent spectrum has no nonzero
projective resonance. -/
theorem rationalIndependentWeights_projectiveFaithful
    (d : Type*) [Fintype d] :
    ∀ k : ProjectiveCharacter d,
      finiteTorusCharacterDetuning
        (finiteCharacterOfProjective k)
        (rationalIndependentWeights d) = 0 →
          k = 0 := by
  intro k hdetuning
  have hsum :
      ∑ i ∈ Finset.univ,
          ((finiteCharacterOfProjective k i : ℤ) : ℚ) •
            rationalIndependentWeights d i = 0 := by
    calc
      (∑ i ∈ Finset.univ,
          ((finiteCharacterOfProjective k i : ℤ) : ℚ) •
            rationalIndependentWeights d i) =
          ∑ i,
            ((finiteCharacterOfProjective k i : ℤ) : ℝ) *
              rationalIndependentWeights d i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Rat.smul_def]
        norm_num
      _ = 0 := hdetuning
  have hcoeff :=
    linearIndependent_iff'.mp
      (rationalIndependentWeights_linearIndependent d)
      Finset.univ
      (fun i =>
        ((finiteCharacterOfProjective k i : ℤ) : ℚ))
      hsum
  apply Subtype.ext
  ext i
  have hi := hcoeff i (Finset.mem_univ i)
  exact_mod_cast hi

/-- **Unconditional fixed-spectrum clock fracture.** One canonical finite
rationally independent spectrum has temporal dimension zero for the
time-zero clock and maximal dimension for every nonzero centered continuous
window.  The spectrum is identical in the two observations. -/
theorem rationalIndependentSpectrum_twoClockTemporalDimensions
    (d : Type*) [Fintype d] {A : ℝ} (hA : A ≠ 0) :
    phaseLawTemporalDimension
        (finiteClockSampledPhaseProbabilityMeasure
          zeroClockProbabilityMeasure
          (rationalIndependentWeights d)) = 0 ∧
      phaseLawTemporalDimension
        (finiteClockSampledPhaseProbabilityMeasure
          (centeredUniformClockProbabilityMeasure A)
          (rationalIndependentWeights d)) =
        Module.finrank ℚ (ProjectiveRationalCharacter d) :=
  sameSpectrum_twoClockTemporalDimensions
    (rationalIndependentWeights d)
    (rationalIndependentWeights_projectiveFaithful d) hA

/-! ## Countably infinite spectra -/

/-- Phase point for arbitrary sampled time on a product torus. -/
def countableClockPhasePoint
    {I : Type*} (omega : I → ℝ) (t : ℝ) :
    I → UnitAddCircle :=
  fun i =>
    ((t * omega i / (2 * Real.pi) : ℝ) : UnitAddCircle)

/-- The countable product phase point is continuous in sampled time. -/
theorem countableClockPhasePoint_continuous
    {I : Type*} (omega : I → ℝ) :
    Continuous (countableClockPhasePoint omega) := by
  unfold countableClockPhasePoint
  apply continuous_pi
  intro i
  exact
    (AddCircle.continuous_mk' (1 : ℝ)).comp
      (by fun_prop)

/-- Countable phase law produced by an arbitrary clock distribution. -/
def countableClockSampledPhaseProbabilityMeasure
    {I : Type*} [Countable I]
    (clockLaw : ProbabilityMeasure ℝ) (omega : I → ℝ) :
    ProbabilityMeasure (I → UnitAddCircle) :=
  ProbabilityMeasure.map clockLaw
    (f := countableClockPhasePoint omega)
    (countableClockPhasePoint_continuous omega).aemeasurable

/-- Evaluation of a finite-support character at one sampled time. -/
theorem infiniteTorusFourier_countableClockPhasePoint
    {I : Type*} (n : I →₀ ℤ)
    (omega : I → ℝ) (t : ℝ) :
    infiniteTorusFourier n
        (countableClockPhasePoint omega t) =
      Complex.exp
        (((t * infiniteTorusCharacterDetuning n omega : ℝ) : ℂ) *
          Complex.I) := by
  classical
  rw [infiniteTorusFourier]
  simp only [ContinuousMap.coe_mk, countableClockPhasePoint,
    fourier_coe_apply]
  rw [Finsupp.prod]
  calc
    (∏ i ∈ n.support,
        Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I * (n i : ℂ) *
            ((t * omega i / (2 * Real.pi) : ℝ) : ℂ) / 1)) =
      ∏ i ∈ n.support,
        Complex.exp
          ((((t * ((n i : ℝ) * omega i) : ℝ) : ℂ) *
            Complex.I)) := by
      apply Finset.prod_congr rfl
      intro i hi
      congr 1
      push_cast
      field_simp [Real.pi_ne_zero]
    _ = Complex.exp
        (∑ i ∈ n.support,
          ((((t * ((n i : ℝ) * omega i) : ℝ) : ℂ) *
            Complex.I))) := by
      rw [Complex.exp_sum]
    _ = Complex.exp
        (((t * infiniteTorusCharacterDetuning n omega : ℝ) : ℂ) *
          Complex.I) := by
      congr 1
      simp only [infiniteTorusCharacterDetuning, Finsupp.sum]
      push_cast
      rw [Finset.mul_sum, Finset.sum_mul]

/-- Countable clock transfer law for every finite-support character. -/
theorem countableClockSampledPhaseProbabilityMeasure_fourier_integral
    {I : Type*} [Countable I]
    (clockLaw : ProbabilityMeasure ℝ)
    (n : I →₀ ℤ) (omega : I → ℝ) :
    (∫ x, infiniteTorusFourier n x
        ∂(countableClockSampledPhaseProbabilityMeasure
          clockLaw omega :
            Measure (I → UnitAddCircle))) =
      charFun (clockLaw : Measure ℝ)
        (infiniteTorusCharacterDetuning n omega) := by
  rw [countableClockSampledPhaseProbabilityMeasure,
    ProbabilityMeasure.toMeasure_map]
  rw [integral_map
    (countableClockPhasePoint_continuous omega).aemeasurable
    (by fun_prop)]
  simp_rw [infiniteTorusFourier_countableClockPhasePoint]
  rw [charFun_apply_real]
  apply integral_congr_ae
  filter_upwards with t
  congr 1
  push_cast
  ring

/-- Characteristic-function convergence for every finite-support spectral
character of a countable system. -/
def HasCompleteCountableClockSamplingLimits
    {α I : Type*}
    (l : Filter α)
    (clockLaw : α → ProbabilityMeasure ℝ)
    (omega : α → I → ℝ) : Prop :=
  ∀ n : I →₀ ℤ, ∃ c : ℂ,
    Tendsto
      (fun x =>
        charFun (clockLaw x : Measure ℝ)
          (infiniteTorusCharacterDetuning n (omega x)))
      l (𝓝 c)

/-- **Arbitrary-sampling countable phase law.** For every countable
spectrum and every family of probability clock laws, the full product-phase
history has a unique weak limit exactly when all finite-support
characteristic coefficients converge. -/
theorem existsUnique_countableClockSampledPhaseLimit_iff_complete
    {α I : Type*} [Countable I]
    {l : Filter α} [l.NeBot]
    (clockLaw : α → ProbabilityMeasure ℝ)
    (omega : α → I → ℝ) :
    (∃! μ : ProbabilityMeasure (I → UnitAddCircle),
      Tendsto
        (fun x =>
          countableClockSampledPhaseProbabilityMeasure
            (clockLaw x) (omega x))
        l (𝓝 μ)) ↔
      HasCompleteCountableClockSamplingLimits
        l clockLaw omega := by
  constructor
  · rintro ⟨μ, hμ, hμunique⟩
    intro n
    refine
      ⟨∫ y, infiniteTorusFourier n y
          ∂(μ : Measure (I → UnitAddCircle)), ?_⟩
    have hcoefficient :=
      (continuous_integral_complex_continuousMap_infinite
        (infiniteTorusFourier n)).continuousAt.tendsto.comp hμ
    apply hcoefficient.congr'
    filter_upwards [] with x
    simp only [Function.comp_apply]
    exact
      countableClockSampledPhaseProbabilityMeasure_fourier_integral
        (clockLaw x) n (omega x)
  · intro hcomplete
    choose limit hlimit using hcomplete
    have hcoefficient : ∀ n : I →₀ ℤ,
        Tendsto
          (fun x =>
            ∫ y, infiniteTorusFourier n y
              ∂(countableClockSampledPhaseProbabilityMeasure
                (clockLaw x) (omega x) :
                  Measure (I → UnitAddCircle)))
          l (𝓝 (limit n)) := by
      intro n
      apply (hlimit n).congr'
      filter_upwards [] with x
      symm
      exact
        countableClockSampledPhaseProbabilityMeasure_fourier_integral
          (clockLaw x) n (omega x)
    obtain ⟨μ, hμ, hμunique⟩ :=
      existsUnique_probabilityMeasure_tendsto_of_infiniteTorusFourier_limit
        (fun x =>
          countableClockSampledPhaseProbabilityMeasure
            (clockLaw x) (omega x))
        limit hcoefficient
    refine ⟨μ, hμ.1, ?_⟩
    intro ν hν
    exact tendsto_nhds_unique hν hμ.1

end

end GaloisForLFunctions.HTGeometry
