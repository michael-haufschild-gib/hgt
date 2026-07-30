import GaloisForLFunctions.RHTower.QuantumRecurrenceGlobalCompletionLaw
import GaloisForLFunctions.RHTower.DissipativeQuantumReturnInformationTransition
import GaloisForLFunctions.RHTower.ProjectiveGaussianRateDistortion
import GaloisForLFunctions.RHTower.FiniteQuantumObserverCoherenceLaw
import GaloisForLFunctions.RHTower.FiniteQuantumObserverGraphRecurrenceBound
import GaloisForLFunctions.RHTower.SummablePurePointPhaseRecurrence

/-!
# Universal quantum recurrence anatomy

This capstone packages the exact threshold, finite-packet clock,
observer-visible content, arbitrary-spectrum long-time distribution, and
local/global determinacy boundary into one theorem.

The clauses deliberately retain different exact domains.  Every finite
contraction reduces to its persistent finite phase packet; arbitrary
probability spectra receive the complete collision-hierarchy law rather than
a finite-packet deadline.
-/

open Complex Filter MeasureTheory Set
open scoped ENNReal Topology BigOperators

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry
open SpectralMemory

/-- Every finite contraction has an exact state-dependent asymptotic
return-amplitude ceiling. -/
def UniversalFiniteContractionThresholdLaw : Prop :=
  ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [FiniteDimensional ℂ H],
    ∀ (T : H →L[ℂ] H), ‖T‖ ≤ 1 → ∀ x : H,
      IsExactAsymptoticReturnAmplitudeCeiling
        (fun n : ℕ => inner ℂ x ((T ^ n) x))
        (finiteContractionPersistentMass T x)

/-- Every positive finite phase packet obeys the exact minimax
recurrence--rate-distortion sandwich. -/
def UniversalFinitePacketClockLaw : Prop :=
  ∀ {d : ℕ} (hd : 2 ≤ d) (w : Fin d → ℝ),
    ∀ (hw : ∀ j, 0 < w j) (hmass : ∑ j, w j = 1)
      (eta : ℝ) (heta0 : 0 < eta) (heta1 : eta ≤ 1),
      projectiveGaussianRateDistortionMinimum (by omega) w eta -
          (Real.pi / 4) * (d - 1 : ℕ) - Real.log (2 * (d : ℝ)) <
        Real.log (universalWeightedFloquetFidelityRecurrenceTime
          hd w (fun j => (hw j).le)
          hmass eta heta0 heta1 : ℝ) ∧
      Real.log (universalWeightedFloquetFidelityRecurrenceTime
          hd w (fun j => (hw j).le)
          hmass eta heta0 heta1 : ℝ) ≤
        projectiveGaussianRateDistortionMinimum (by omega) w eta +
          (d - 1 : ℕ) * Real.log projectivePhaseResolutionConstant

/- Below the persistent ceiling of a finite contraction, the surviving
phase packet's universal clock supplies a post-burn-in return. -/
set_option linter.unusedVariables false in
def UniversalFiniteContractionDeadlineLaw : Prop :=
  ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [FiniteDimensional ℂ H],
    ∀ (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (x : H)
      (hpersistent : 0 < finiteContractionPersistentMass T x)
      (hperipheral :
        2 ≤ Fintype.card (FiniteContractionPeripheralEigenvalue T))
      (target : ℝ) (htarget0 : 0 ≤ target)
      (htarget : target < finiteContractionPersistentMass T x),
    let eta :=
      (finiteContractionPersistentMass T x - target) /
        (2 * finiteContractionPersistentMass T x)
    ∃ (heta0 : 0 < eta) (heta1 : eta ≤ 1) (B n : ℕ),
      B < n ∧
      n ≤ (B + 1) *
        universalWeightedFloquetFidelityRecurrenceTime
          hperipheral
          (finiteContractionPeripheralWeight T x)
          (finiteContractionPeripheralWeight_nonneg T x hpersistent)
          (sum_finiteContractionPeripheralWeight T x hpersistent)
          eta heta0 heta1 ∧
      target ≤ ‖inner ℂ x ((T ^ n) x)‖

/-- Every finite observer family has an exact phase-energy identity,
zero-return law, and coherence-graph phase capacity. -/
def UniversalFiniteObserverLaw : Prop :=
  ∀ {d : ℕ} {J : Type*} [Fintype J]
      (lam : J → ℝ) (block : J → Fin d → Fin d → ℂ),
    (∀ a, 0 ≤ lam a) → ∀ (t : ℝ) (energy : Fin d → ℝ),
      finiteQuantumObserverDistanceSq lam
          (finiteObserverHamiltonianVertexPhase t energy) block =
        finiteQuantumObserverPhaseEnergy lam
          (finiteObserverHamiltonianVertexPhase t energy) block ∧
      (finiteQuantumObserverPhaseEnergy lam
            (finiteObserverHamiltonianVertexPhase t energy) block = 0 ↔
        ∀ i j, (finiteObserverCoherenceGraph lam block).Adj i j →
          finiteObserverHamiltonianVertexPhase t energy i =
            finiteObserverHamiltonianVertexPhase t energy j) ∧
      Module.finrank ℝ
          (LinearMap.range
            (GaloisForLFunctions.graphCoboundary
              (finiteObserverCoherenceGraph lam block) ℝ)) =
        d -
          Fintype.card
            (finiteObserverCoherenceGraph lam block).ConnectedComponent

/-- The visible graph rank is the exponent of a universal finite-observer
recurrence deadline. -/
def UniversalFiniteObserverClockLaw : Prop :=
  ∀ {d : ℕ} {J : Type*} [Fintype J]
      (lam : J → ℝ) (block : J → Fin d → Fin d → ℂ),
    (∀ a, 0 ≤ lam a) → ∀ (energy : Fin d → ℝ) (Q : ℕ),
      ∃ n : ℕ, 0 < n ∧
        n ≤ (Q + 1) ^
          (d - Nat.card
            (finiteObserverCoherenceGraph lam block).ConnectedComponent) ∧
        finiteQuantumObserverDistanceSq lam
            (finiteObserverHamiltonianVertexPhase (n : ℝ) energy) block ≤
          4 * (2 * Real.pi / (Q + 1 : ℝ)) ^ 2 *
            ∑ i, ∑ j, finiteObserverUnionWeight lam block i j

/-- Every probability energy spectrum has exact additive collision moments
and a long-time mean for every continuous fidelity statistic. -/
def UniversalLongTimeRecurrenceLaw : Prop :=
  (∀ (mu : Measure ℝ) [IsProbabilityMeasure mu] (n : ℕ),
    Tendsto (spectralReturnMomentMeanReal mu n) atTop
      (𝓝 ((convPow (spectralDifferenceMeasure mu) n).real {0}))) ∧
  (∀ (mu : Measure ℝ) [IsProbabilityMeasure mu]
      (statistic : ℝ → ℝ),
    ContinuousOn statistic (Icc (0 : ℝ) 1) →
      ∃ L : ℝ,
        Tendsto (spectralReturnStatisticMeanReal mu statistic)
          atTop (𝓝 L))

/-- Countable pure-point spectra recur at every positive phase-energy
resolution; exact recurrence is cyclic-gap rigidity; atomless spectra have
continuum temporal dimension and zero-density positive-fidelity returns. -/
def UniversalSpectralPhaseClassificationLaw : Prop :=
  (∀ (a omega : ℕ → ℝ), (∀ p, 0 ≤ a p) → Summable a →
    ∀ {epsilon : ℝ}, 0 < epsilon →
      ∃ n : ℕ, 0 < n ∧
        summablePhaseEnergy a omega n < epsilon) ∧
  (∀ (mu : Measure ℝ) [IsProbabilityMeasure mu],
    (∃ t : ℝ, 0 < t ∧ Complex.normSq (charFun mu t) = 1) ↔
      ∃ omega : ℝ,
        measureVisibleFrequencyGroup (spectralDifferenceMeasure mu) =
          AddSubgroup.zmultiples omega) ∧
  (∀ (mu : Measure ℝ) [IsProbabilityMeasure mu] [NullSingletonClass mu],
    projectiveObserverTemporalDimension mu = Cardinal.continuum ∧
      ∀ eta : ℝ, 0 < eta →
        Tendsto (highFidelityWindowDensity mu eta)
          atTop (𝓝 0))

/-- Complete polynomial local data and complete compact perturbative data
do not universally decide the exact recurrence phase. -/
def UniversalRecurrenceNonidentifiabilityLaw : Prop :=
  (∀ (v : NNReal), 0 < v →
    ¬ ∃ classifier : CompletePolynomialLocalData → Prop,
      ∀ mu : ProbabilityMeasure ℝ,
        HasStrictlyPositiveEnergy (mu : Measure ℝ) →
        HasAllEnergyMoments (mu : Measure ℝ) →
        (classifier
            (completePolynomialLocalData (mu : Measure ℝ)) ↔
          HasPersistentMeanRecurrence (mu : Measure ℝ))) ∧
  (∀ (g : ℝ), 0 < g →
    ¬ ∃ classifier :
        (BoundedContinuousFunction ℝ ℂ → ℕ → ℂ) → Prop,
      ∀ family : ℝ → ProbabilityMeasure ℝ,
        IsUniformlyCompactPositiveSpectrumFamily family →
        (classifier
            (perturbativeBoundedSpectralObservableJet family) ↔
          HasPersistentMeanRecurrence (family g : Measure ℝ))) ∧
  (∀ (g : ℝ), 0 < g →
    ¬ ∃ classifier : (ℕ → ℝ → ℂ) → Prop,
      ∀ family : ℝ → ProbabilityMeasure ℝ,
        IsUniformlyCompactPositiveSpectrumFamily family →
        (classifier
            (perturbativeSpectralFormFactorJet family) ↔
          HasPersistentMeanRecurrence (family g : Measure ℝ)))

/-- Compact support is the exact positive boundary at which complete moment
data determine the entire spectrum. -/
def UniversalCompactMomentDeterminacyLaw : Prop :=
  ∀ {s : ℕ → ℝ} {mu nu : ProbabilityMeasure ℝ}
      {c r : ℝ}, 0 < r →
    (mu : Measure ℝ) (Icc (c - r) (c + r))ᶜ = 0 →
    GaloisForLFunctions.HTGeometry.HasHamburgerMoments
      s (mu : Measure ℝ) →
    GaloisForLFunctions.HTGeometry.HasHamburgerMoments
      s (nu : Measure ℝ) →
    (mu : Measure ℝ) = (nu : Measure ℝ)

universe u v

/-- The complete whether--when--what--global-data anatomy of quantum
recurrence. -/
structure UniversalQuantumRecurrenceAnatomyLaw : Prop where
  whetherAndHowMuch : UniversalFiniteContractionThresholdLaw.{u}
  coupledFiniteDeadline : UniversalFiniteContractionDeadlineLaw.{u}
  whenFinite : UniversalFinitePacketClockLaw
  whatObserverSees : UniversalFiniteObserverLaw.{v}
  observerDeadline : UniversalFiniteObserverClockLaw.{v}
  globalLongTimeStatistics : UniversalLongTimeRecurrenceLaw
  spectralPhaseClassification : UniversalSpectralPhaseClassificationLaw
  localDataDoNotDecide : UniversalRecurrenceNonidentifiabilityLaw
  compactExactDataDecide : UniversalCompactMomentDeterminacyLaw

/-- **Universal quantum recurrence anatomy law.**  The exact returnability
threshold, finite-packet information clock, observer-visible phase quotient,
arbitrary-spectrum collision hierarchy, and local/global determinacy boundary
hold simultaneously with their full universal quantifiers. -/
theorem universalQuantumRecurrenceAnatomyLaw :
    UniversalQuantumRecurrenceAnatomyLaw.{u, v} := by
  refine {
    whetherAndHowMuch := ?_
    coupledFiniteDeadline := ?_
    whenFinite := ?_
    whatObserverSees := ?_
    observerDeadline := ?_
    globalLongTimeStatistics := ?_
    spectralPhaseClassification := ?_
    localDataDoNotDecide := ?_
    compactExactDataDecide := ?_
  }
  · intro H _ _ _ _ T hT x
    exact finiteContraction_returnAmplitude_exactAsymptoticCeiling T hT x
  · intro H _ _ _ _ T hT x hpersistent hperipheral
      target htarget0 htarget
    exact finiteContraction_exists_return_at_target_before_waterDeadline
      T hT x hpersistent hperipheral target htarget0 htarget
  · intro d hd w hw hmass eta heta0 heta1
    exact
      universalWeightedFloquetFidelityRecurrenceTime_rateDistortionSandwich
        hd w hw hmass eta heta0 heta1
  · intro d J _ lam block hlam t energy
    exact finite_quantum_observer_coherence_law
      lam block hlam t energy
  · intro d J _ lam block hlam energy Q
    exact exists_finiteQuantumObserver_graphRank_distance_recurrence
      lam block hlam energy Q
  · constructor
    · intro mu _ n
      exact spectralReturnMomentMeanReal_tendsto_collisionHierarchy mu n
    · intro mu _ statistic hstatistic
      exact exists_tendsto_spectralReturnStatisticMeanReal
        mu statistic hstatistic
  · constructor
    · intro a omega ha hsum epsilon hepsilon
      exact exists_summablePhaseEnergy_recurrence
        a omega ha hsum hepsilon
    · constructor
      · intro mu _
        exact exists_positive_unitFidelity_iff_cyclic mu
      · intro mu _ _
        exact atomlessProjectiveObserverTemporalPhaseLaw mu
  · constructor
    · intro v hv
      exact globalCompletion_no_completeLocal_recurrenceClassifier v hv
    · constructor
      · intro g hg
        exact
          globalCompletion_no_completePerturbativeTheory_recurrenceClassifier
            g hg
      · intro g hg
        exact globalCompletion_no_completePerturbativeSFF_recurrenceClassifier
          g hg
  · intro s mu nu c r hr hcarried hmu hnu
    exact compactExactMoments_determine_spectrum
      hr hcarried hmu hnu

end RHTower
