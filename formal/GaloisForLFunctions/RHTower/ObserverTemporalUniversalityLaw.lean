import GaloisForLFunctions.RHTower.ObserverTemporalDimensionLaw

/-!
# Observer temporal universality

This file packages the observer-dependent temporal-dimension law into two
same-dynamics statements.

* One fixed finite rationally independent Hamiltonian saturates the temporal
  capacity of every observer coherence graph on its energy sectors.
* One fixed stationary spectrum admits two localized Schwartz observers with
  the two extreme infinite-system phases: temporal dimension zero with
  perfect recurrence, and temporal dimension continuum with zero-density
  return above every positive fidelity threshold.

The second result is an exact same-spectrum separation.  No change of
Hamiltonian, spectral measure, or external time parameter is made; only the
observer probe changes.
-/

open Complex Filter MeasureTheory Set
open SchwartzMap
open scoped Cardinal Topology

noncomputable section

namespace RHTower

open SpectralMemory

/-- Projective temporal dimension of a state: rational rank of its visible
energy-gap spectrum.  Using the spectral-difference measure removes the
unobservable common energy origin. -/
def projectiveObserverTemporalDimension (mu : Measure ℝ) : Cardinal :=
  measureTemporalDimension (spectralDifferenceMeasure mu)

/-- Exact projective return means phase locking of every visible energy gap;
the state itself may acquire one common global phase. -/
def projectiveMeasureExactReturn (mu : Measure ℝ) (t : ℝ) : Prop :=
  measureExactReturn (spectralDifferenceMeasure mu) t

/-- Translation of every energy by one common constant. -/
def translateObserverSpectrum (mu : Measure ℝ) (c : ℝ) : Measure ℝ :=
  mu.map (· + c)

noncomputable instance translateObserverSpectrum.instIsProbabilityMeasure
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (c : ℝ) :
    IsProbabilityMeasure (translateObserverSpectrum mu c) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

/-- The complete energy-gap distribution is invariant under an arbitrary
change of energy origin. -/
theorem spectralDifferenceMeasure_translateObserverSpectrum
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (c : ℝ) :
    spectralDifferenceMeasure (translateObserverSpectrum mu c) =
      spectralDifferenceMeasure mu := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_spectralDifferenceMeasure,
    charFun_spectralDifferenceMeasure,
    translateObserverSpectrum, charFun_map_add_const,
    Complex.normSq_mul]
  have hphase :
      Complex.normSq
          (Complex.exp
            (((inner ℝ c t : ℝ) : ℂ) * Complex.I)) = 1 := by
    rw [Complex.normSq_eq_norm_sq,
      Complex.norm_exp_ofReal_mul_I]
    norm_num
  rw [hphase, mul_one]

/-- Projective temporal dimension is invariant under the arbitrary global
choice of zero energy. -/
theorem projectiveObserverTemporalDimension_translate_invariant
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (c : ℝ) :
    projectiveObserverTemporalDimension
        (translateObserverSpectrum mu c) =
      projectiveObserverTemporalDimension mu := by
  unfold projectiveObserverTemporalDimension
  rw [
    spectralDifferenceMeasure_translateObserverSpectrum]

/-- Absolute-continuity refinement of visible state spectra cannot decrease
projective temporal dimension. -/
theorem projectiveObserverTemporalDimension_mono_of_absolutelyContinuous
    {mu nu : Measure ℝ} [IsFiniteMeasure nu] (h : mu ≪ nu) :
    projectiveObserverTemporalDimension mu ≤
      projectiveObserverTemporalDimension nu := by
  apply measureTemporalDimension_mono_of_absolutelyContinuous
  rw [spectralDifferenceMeasure, spectralDifferenceMeasure]
  exact (h.prod h).map (by fun_prop)

/-- Exact projective return is invariant under the arbitrary global choice
of zero energy. -/
theorem projectiveMeasureExactReturn_translate_invariant
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (c t : ℝ) :
    projectiveMeasureExactReturn
        (translateObserverSpectrum mu c) t ↔
      projectiveMeasureExactReturn mu t := by
  unfold projectiveMeasureExactReturn
  rw [
    spectralDifferenceMeasure_translateObserverSpectrum]

/-- Every atomless state spectrum has an atomless energy-gap distribution. -/
theorem spectralDifferenceMeasure_noAtoms
    (mu : Measure ℝ) [NullSingletonClass mu] :
    NullSingletonClass (spectralDifferenceMeasure mu) := by
  rw [spectralDifferenceMeasure]
  exact noAtoms_map_prod_of_countable_fibers
    mu mu (fun p : ℝ × ℝ ↦ p.1 - p.2)
    (by fun_prop)
    (fun x energy ↦ by
      have h :
          {y : ℝ | x - y = energy} =
            {x - energy} := by
        ext y
        simp
        constructor <;> intro hy <;> linarith
      rw [h]
      exact Set.finite_singleton _ |>.countable)

/-- Atomless projective phase law.  Every atomless state has continuum
energy-gap dimension, while every fixed positive-fidelity return set has
zero asymptotic time density. -/
theorem atomlessProjectiveObserverTemporalPhaseLaw
    (mu : Measure ℝ) [IsProbabilityMeasure mu] [NullSingletonClass mu] :
    projectiveObserverTemporalDimension mu = Cardinal.continuum ∧
      ∀ eta : ℝ, 0 < eta →
        Tendsto (highFidelityWindowDensity mu eta)
          atTop (𝓝 0) := by
  haveI : NullSingletonClass (spectralDifferenceMeasure mu) :=
    spectralDifferenceMeasure_noAtoms mu
  exact
    ⟨measureTemporalDimension_eq_continuum_of_noAtoms
        (spectralDifferenceMeasure mu),
      fun eta heta ↦
        highFidelityWindowDensity_tendsto_zero_of_noAtoms
          mu heta⟩

/-- Universal projective dispersive phase law.  Any normalized real energy
law obtained from a source absolutely continuous with respect to a product
having one atomless coordinate, through a countable-fiber dispersion, has
continuum projective temporal dimension and zero-density positive-fidelity
returns. -/
theorem dispersiveSpatialProjectiveObserverTemporalPhaseLaw
    {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (mu : Measure α) (nu : Measure β) [NullSingletonClass nu]
    (source : Measure (α × β))
    (hsource : source ≪ mu.prod nu)
    (dispersion : α × β → ℝ)
    (hdispersion : Measurable dispersion)
    (hfiber :
      ∀ a energy, {b | dispersion (a, b) = energy}.Countable)
    [IsProbabilityMeasure (source.map dispersion)] :
    projectiveObserverTemporalDimension
        (source.map dispersion) =
      Cardinal.continuum ∧
      ∀ eta : ℝ, 0 < eta →
        Tendsto
          (highFidelityWindowDensity
            (source.map dispersion) eta)
          atTop (𝓝 0) := by
  letI : NullSingletonClass (source.map dispersion) :=
    noAtoms_map_of_absolutelyContinuous_prod_of_countable_fibers
      mu nu source hsource dispersion hdispersion hfiber
  exact atomlessProjectiveObserverTemporalPhaseLaw
    (source.map dispersion)

/-- Relativistic specialization of the projective dispersive phase law,
uniform over every mass mixture and every normalized correlated source
absolutely continuous with respect to an arbitrary mass law times an
atomless momentum law. -/
theorem relativisticSpatialProjectiveObserverTemporalPhaseLaw
    (massMeasure momentumMeasure : Measure ℝ)
    [NullSingletonClass momentumMeasure]
    (source : Measure (ℝ × ℝ))
    (hsource :
      source ≪ massMeasure.prod momentumMeasure)
    [IsProbabilityMeasure (source.map relativisticEnergy)] :
    projectiveObserverTemporalDimension
        (source.map relativisticEnergy) =
      Cardinal.continuum ∧
      ∀ eta : ℝ, 0 < eta →
        Tendsto
          (highFidelityWindowDensity
            (source.map relativisticEnergy) eta)
          atTop (𝓝 0) := by
  exact dispersiveSpatialProjectiveObserverTemporalPhaseLaw
    massMeasure momentumMeasure source hsource
    relativisticEnergy
    (by
      unfold relativisticEnergy
      fun_prop)
    (fun mass energy ↦
      (relativisticEnergy_fiber_finite mass energy).countable)

/-- Intrinsic stationary-field projective phase law.  If the positive
spectral measure of a stationary Schwartz form is atomless, every nonzero
Schwartz probe has continuum projective temporal dimension and zero-density
positive-fidelity returns. -/
theorem stationarySchwartzObserverProjectiveTemporalPhaseLaw
    (Q : ContinuousSchwartzSesquilinearForm)
    (hQ : Q.MomentumSymmetric) (hQnonneg : Q.IsNonnegative)
    [NullSingletonClass (Q.compactSpectralRieszMeasure hQ hQnonneg)]
    (probe : SchwartzMap ℝ ℂ)
    (hprobe :
      0 < (Q.fourierPullback probe probe).re) :
    projectiveObserverTemporalDimension
        (@schwartzObserverProbabilityMeasure
          (Q.compactSpectralRieszMeasure hQ hQnonneg)
          (Q.compactSpectralRieszMeasure_hasTemperateGrowth
            hQ hQnonneg) probe : Measure ℝ) =
        Cardinal.continuum ∧
      ∀ eta : ℝ, 0 < eta →
        Tendsto
          (highFidelityWindowDensity
            (@schwartzObserverProbabilityMeasure
              (Q.compactSpectralRieszMeasure hQ hQnonneg)
              (Q.compactSpectralRieszMeasure_hasTemperateGrowth
                hQ hQnonneg) probe : Measure ℝ) eta)
          atTop (𝓝 0) := by
  letI :
      (Q.compactSpectralRieszMeasure hQ hQnonneg).HasTemperateGrowth :=
    Q.compactSpectralRieszMeasure_hasTemperateGrowth hQ hQnonneg
  letI : NullSingletonClass
      (schwartzObserverProbabilityMeasure
        (Q.compactSpectralRieszMeasure hQ hQnonneg) probe :
          Measure ℝ) :=
    schwartzObserverProbabilityMeasure_noAtoms
      (Q.compactSpectralRieszMeasure hQ hQnonneg) probe
      (by
        rw [stationarySchwartzObserverSpectralWeight_eq
          Q hQ hQnonneg probe]
        exact hprobe)
  exact atomlessProjectiveObserverTemporalPhaseLaw
    (schwartzObserverProbabilityMeasure
      (Q.compactSpectralRieszMeasure hQ hQnonneg) probe :
        Measure ℝ)

/-- Projective temporal dimension has the same universal cardinal gap as
arbitrary real spectral dimension: it is at most countable or exactly
continuum. -/
theorem projectiveObserverTemporalDimension_le_aleph0_or_eq_continuum
    (mu : Measure ℝ) :
    projectiveObserverTemporalDimension mu ≤ Cardinal.aleph0 ∨
      projectiveObserverTemporalDimension mu = Cardinal.continuum := by
  exact measureTemporalDimension_le_aleph0_or_eq_continuum
    (spectralDifferenceMeasure mu)

/-- A state has a positive exact projective return precisely when its
visible energy-gap group is cyclic. -/
theorem exists_positive_projectiveMeasureExactReturn_iff_cyclic
    (mu : Measure ℝ) :
    (∃ t : ℝ, 0 < t ∧ projectiveMeasureExactReturn mu t) ↔
      ∃ omega : ℝ,
        measureVisibleFrequencyGroup (spectralDifferenceMeasure mu) =
          AddSubgroup.zmultiples omega :=
  exists_positive_measureExactReturn_iff_cyclic
    (spectralDifferenceMeasure mu)

/-- Integrated squared phase displacement is exactly twice one minus the
real characteristic function. -/
theorem measureObserverDisplacementSq_eq_two_sub_two_mul_charFun_re
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (t : ℝ) :
    measureObserverDisplacementSq mu t =
      2 - 2 * (charFun mu t).re := by
  have hphaseIntegrable :
      Integrable (fun x ↦ observerSpectralPhase t x) mu := by
    have hone :
        Integrable (fun _ : ℝ ↦ (1 : ℝ)) mu :=
      integrable_const 1
    refine hone.mono'
      (observerSpectralPhase_continuous t).aestronglyMeasurable
      ?_
    filter_upwards with x
    rw [observerSpectralPhase,
      Complex.norm_exp_ofReal_mul_I]
  have hchar :
      (∫ x, observerSpectralPhase t x ∂mu) = charFun mu t := by
    rw [charFun_apply_real]
    apply integral_congr_ae
    filter_upwards with x
    rw [observerSpectralPhase]
    congr 1
    push_cast
    ring
  rw [measureObserverDisplacementSq]
  have hpoint (x : ℝ) :
      ‖observerSpectralPhase t x - 1‖ ^ (2 : ℕ) =
        2 - 2 * (observerSpectralPhase t x).re := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
    have hnorm :
        Complex.normSq (observerSpectralPhase t x) = 1 := by
      rw [Complex.normSq_eq_norm_sq, observerSpectralPhase,
        Complex.norm_exp_ofReal_mul_I]
      norm_num
    rw [hnorm]
    norm_num
  simp_rw [hpoint]
  have hreIntegrable :
      Integrable
        (fun x ↦ (observerSpectralPhase t x).re) mu :=
    hphaseIntegrable.re
  have hre :
      (∫ x, (observerSpectralPhase t x).re ∂mu) =
        (charFun mu t).re := by
    rw [← hchar]
    exact integral_re hphaseIntegrable
  rw [integral_sub (integrable_const (μ := mu) (2 : ℝ))
      (hreIntegrable.const_mul 2),
    integral_const, integral_const_mul, hre]
  simp

/-- Exact projective return is exactly unit survival fidelity. -/
theorem projectiveMeasureExactReturn_iff_fidelity_eq_one
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (t : ℝ) :
    projectiveMeasureExactReturn mu t ↔
      Complex.normSq (charFun mu t) = 1 := by
  rw [projectiveMeasureExactReturn,
    ← measureObserverDisplacementSq_eq_zero_iff]
  have hprob :
      IsProbabilityMeasure (spectralDifferenceMeasure mu) := inferInstance
  rw [measureObserverDisplacementSq_eq_two_sub_two_mul_charFun_re,
    charFun_spectralDifferenceMeasure]
  simp only [Complex.ofReal_re]
  constructor <;> intro h <;> nlinarith

/-- Positive-time unit survival fidelity exists exactly in the cyclic
energy-gap phase. -/
theorem exists_positive_unitFidelity_iff_cyclic
    (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    (∃ t : ℝ, 0 < t ∧
        Complex.normSq (charFun mu t) = 1) ↔
      ∃ omega : ℝ,
        measureVisibleFrequencyGroup (spectralDifferenceMeasure mu) =
          AddSubgroup.zmultiples omega := by
  rw [← exists_positive_projectiveMeasureExactReturn_iff_cyclic]
  constructor
  · rintro ⟨t, ht, hfid⟩
    exact
      ⟨t, ht,
        (projectiveMeasureExactReturn_iff_fidelity_eq_one
          mu t).2 hfid⟩
  · rintro ⟨t, ht, hret⟩
    exact
      ⟨t, ht,
        (projectiveMeasureExactReturn_iff_fidelity_eq_one
          mu t).1 hret⟩

/-- One fixed finite rationally independent energy assignment saturates the
temporal capacity of every observer graph on the same energy sectors. -/
theorem oneFiniteHamiltonian_allObserverGraphTemporalDimensions
    {V : Type*} [Fintype V] (G : SimpleGraph V) :
    graphTemporalDimension G
        (GaloisForLFunctions.HTGeometry.rationalIndependentWeights V) =
      Fintype.card V - Nat.card G.ConnectedComponent :=
  universalGraphTemporalDimension_eq_phaseCapacity G

/-- On one fixed `d`-sector Hamiltonian, changing only the observer graph
between no visible coherence and complete visible coherence changes temporal
dimension from zero to `d - 1`. -/
theorem oneFiniteHamiltonian_twoExtremeObserverTemporalDimensions
    {d : ℕ} (hd : 0 < d) :
    graphTemporalDimension (⊥ : SimpleGraph (Fin d))
        (GaloisForLFunctions.HTGeometry.rationalIndependentWeights
          (Fin d)) = 0 ∧
      graphTemporalDimension (⊤ : SimpleGraph (Fin d))
        (GaloisForLFunctions.HTGeometry.rationalIndependentWeights
          (Fin d)) = d - 1 := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  constructor
  · rw [graphTemporalDimension, graphTemporalModule,
      visibleFrequencyModule]
    have hzero :
        graphVisibleGap (⊥ : SimpleGraph (Fin d))
            (GaloisForLFunctions.HTGeometry.rationalIndependentWeights
              (Fin d)) = 0 := by
      funext p
      simp [graphVisibleGap]
    rw [hzero]
    change
      Module.finrank ℚ
          (Submodule.span ℚ
            (Set.range (0 : Fin d × Fin d → ℝ))) = 0
    rw [show Set.range (0 : Fin d × Fin d → ℝ) = {0} by
      ext x
      simp]
    simp
  · have hconnected : (⊤ : SimpleGraph (Fin d)).Connected :=
      SimpleGraph.connected_top
    have hcard :
        Nat.card (⊤ : SimpleGraph (Fin d)).ConnectedComponent = 1 := by
      rw [Nat.card_eq_fintype_card]
      apply Fintype.card_eq_one_iff.mpr
      refine
        ⟨(⊤ : SimpleGraph (Fin d)).connectedComponentMk
            (Classical.arbitrary (Fin d)), ?_⟩
      intro c
      induction c using SimpleGraph.ConnectedComponent.ind with
      | _ v =>
          exact SimpleGraph.ConnectedComponent.eq.mpr
            (hconnected.preconnected v
              (Classical.arbitrary (Fin d)))
    simpa only [Fintype.card_fin, hcard] using
      (universalGraphTemporalDimension_eq_phaseCapacity
        (G := (⊤ : SimpleGraph (Fin d))))

/-- Same stationary spectrum, opposite temporal dimensions and return
phases.  The recurrent probe sees only the zero-frequency atom and therefore
has temporal dimension zero and perfect return.  The dispersive probe sees
only the atomless unit interval and therefore has continuum temporal
dimension and zero-density return above every positive fidelity threshold. -/
theorem oneStationarySpectrum_twoObserverTemporalDimensions :
    projectiveObserverTemporalDimension
        (schwartzObserverProbabilityMeasure
          observerPhaseSeparatedSpectrum
          recurrentPhaseObserverProbe : Measure ℝ) = 0 ∧
      projectiveObserverTemporalDimension
        (schwartzObserverProbabilityMeasure
          observerPhaseSeparatedSpectrum
          dispersivePhaseObserverProbe : Measure ℝ) =
        Cardinal.continuum ∧
      (∀ t : ℝ,
        Complex.normSq
          (charFun
            (schwartzObserverProbabilityMeasure
              observerPhaseSeparatedSpectrum
              recurrentPhaseObserverProbe : Measure ℝ) t) = 1) ∧
      (∀ eta : ℝ, 0 < eta →
        Tendsto
          (highFidelityWindowDensity
            (schwartzObserverProbabilityMeasure
              observerPhaseSeparatedSpectrum
              dispersivePhaseObserverProbe : Measure ℝ) eta)
          atTop (𝓝 0)) := by
  have hrecurrent :
      projectiveObserverTemporalDimension
          (schwartzObserverProbabilityMeasure
            observerPhaseSeparatedSpectrum
            recurrentPhaseObserverProbe : Measure ℝ) = 0 := by
    have hdiff :
        spectralDifferenceMeasure (Measure.dirac (0 : ℝ)) =
          Measure.dirac 0 := by
      apply Measure.ext_of_charFun
      funext t
      rw [charFun_spectralDifferenceMeasure]
      simp
    rw [projectiveObserverTemporalDimension,
      recurrentPhaseObserver_probabilityMeasure,
      hdiff,
      measureTemporalDimension_eq_zero_iff_group_eq_bot,
      measureVisibleFrequencyGroup, AddSubgroup.closure_eq_bot_iff]
    intro y hy
    have hsupp :
        (Measure.dirac (0 : ℝ)).support ⊆ ({0} : Set ℝ) :=
      Measure.support_subset_of_isClosed isClosed_singleton
        (by simp)
    simpa using hsupp hy
  have hdispersive :
      projectiveObserverTemporalDimension
          (schwartzObserverProbabilityMeasure
            observerPhaseSeparatedSpectrum
            dispersivePhaseObserverProbe : Measure ℝ) =
        Cardinal.continuum := by
    haveI : NullSingletonClass
        (schwartzObserverProbabilityMeasure
          observerPhaseSeparatedSpectrum
          dispersivePhaseObserverProbe : Measure ℝ) := by
      rw [dispersivePhaseObserver_probabilityMeasure]
      infer_instance
    exact (atomlessProjectiveObserverTemporalPhaseLaw
      (schwartzObserverProbabilityMeasure
        observerPhaseSeparatedSpectrum
        dispersivePhaseObserverProbe : Measure ℝ)).1
  exact
    ⟨hrecurrent, hdispersive,
      oneStationaryForm_twoObserverTemporalPhases.1,
      oneStationaryForm_twoObserverTemporalPhases.2⟩

/-- Universal phase classification for arbitrary real observer spectra:
temporal dimension has no intermediate uncountable value; exact positive
return occurs precisely in the cyclic visible-frequency phase; and every
atomless probability spectrum lies in the continuum-dimensional,
zero-return-density phase. -/
theorem universalObserverTemporalPhaseClassification
    (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    (projectiveObserverTemporalDimension mu ≤ Cardinal.aleph0 ∨
        projectiveObserverTemporalDimension mu =
          Cardinal.continuum) ∧
      ((∃ t : ℝ, 0 < t ∧
          Complex.normSq (charFun mu t) = 1) ↔
        ∃ omega : ℝ,
          measureVisibleFrequencyGroup
              (spectralDifferenceMeasure mu) =
            AddSubgroup.zmultiples omega) ∧
      (NullSingletonClass mu →
        projectiveObserverTemporalDimension mu =
            Cardinal.continuum ∧
          ∀ eta : ℝ, 0 < eta →
            Tendsto (highFidelityWindowDensity mu eta)
              atTop (𝓝 0)) := by
  refine
    ⟨projectiveObserverTemporalDimension_le_aleph0_or_eq_continuum
        mu,
      exists_positive_unitFidelity_iff_cyclic mu,
      ?_⟩
  intro hNoAtoms
  letI : NullSingletonClass mu := hNoAtoms
  exact atomlessProjectiveObserverTemporalPhaseLaw mu

end RHTower
