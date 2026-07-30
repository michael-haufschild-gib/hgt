import GaloisForLFunctions.HTGeometry.CountableAnalyticPhaseEnsembleWallCrossingLaw
import GaloisForLFunctions.HTGeometry.TemporalCharacterWallCrossingLaw
import GaloisForLFunctions.HTGeometry.ValuatedSpectralCharacterLaw

/-!
# An analytic countable spectrum with no last temporal birth

Finite spectra have a terminal temporal layer. This file gives the sharp
infinite contrast: one explicit countable real-analytic frequency family has
a projective character born at every positive order. Its uniformly
time-sampled phase coefficients cross from unresolved to sinc to dephased
at every corresponding inverse-power horizon.
-/

open Filter MeasureTheory Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Countable analytic staircase spectrum: label zero is the phase
reference and label `n+1` has frequency `g^(n+1)`. -/
def infiniteTemporalCascadeFrequency (g : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => g ^ (n + 1)

/-- Complex analytic continuation of the staircase spectrum. -/
def infiniteTemporalCascadeEnergy (i : ℕ) (g : ℂ) : ℂ :=
  match i with
  | 0 => 0
  | n + 1 => g ^ (n + 1)

theorem infiniteTemporalCascadeEnergy_analyticAt
    (i : ℕ) :
    AnalyticAt ℂ (infiniteTemporalCascadeEnergy i) 0 := by
  cases i with
  | zero =>
      change AnalyticAt ℂ (fun _ : ℂ => 0) 0
      exact analyticAt_const
  | succ n =>
      change AnalyticAt ℂ (fun g : ℂ => g ^ (n + 1)) 0
      fun_prop

/-- Canonical analytic series of each staircase branch. -/
noncomputable def infiniteTemporalCascadeSeries
    (i : ℕ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  Classical.choose (infiniteTemporalCascadeEnergy_analyticAt i)

theorem infiniteTemporalCascadeSeries_spec
    (i : ℕ) :
    HasFPowerSeriesAt
      (infiniteTemporalCascadeEnergy i)
      (infiniteTemporalCascadeSeries i) 0 :=
  Classical.choose_spec (infiniteTemporalCascadeEnergy_analyticAt i)

theorem infiniteTemporalCascadeEnergy_eventually_real
    (i : ℕ) :
    ∀ᶠ (g : ℝ) in 𝓝[>] (0 : ℝ),
      infiniteTemporalCascadeEnergy i (g : ℂ) =
        (infiniteTemporalCascadeFrequency g i : ℂ) := by
  have h :
      ∀ g : ℝ,
        infiniteTemporalCascadeEnergy i (g : ℂ) =
          (infiniteTemporalCascadeFrequency g i : ℂ) := by
    intro g
    cases i <;>
      simp [infiniteTemporalCascadeEnergy,
        infiniteTemporalCascadeFrequency]
  exact Filter.Eventually.of_forall h

/-- Projective character comparing layer `b+1` with the zero-frequency
reference. -/
def infiniteTemporalCascadeCharacter (b : ℕ) : ℕ →₀ ℤ :=
  Finsupp.single (b + 1) 1 - Finsupp.single 0 1

theorem infiniteTemporalCascadeCharacter_charge_zero
    (b : ℕ) :
    integerCharacterCharge ℕ
      (infiniteTemporalCascadeCharacter b) = 0 := by
  rw [infiniteTemporalCascadeCharacter, map_sub]
  simp [integerCharacterCharge]

/-- The `b`th staircase character has exact detuning `g^(b+1)`. -/
theorem infiniteTemporalCascadeCharacter_detuning
    (b : ℕ) (g : ℝ) :
    infiniteTorusCharacterDetuning
        (infiniteTemporalCascadeCharacter b)
        (infiniteTemporalCascadeFrequency g) =
      g ^ (b + 1) := by
  rw [infiniteTemporalCascadeCharacter,
    infiniteTorusCharacterDetuning,
    Finsupp.sum_sub_index (by
      intro i m n
      push_cast
      ring)]
  simp [infiniteTemporalCascadeFrequency]

/-- Every positive integer occurs as an exact birth order in one fixed
countable analytic spectrum. -/
theorem infiniteTemporalCascadeCharacter_birthProfile
    (b : ℕ) :
    HasPositiveBirthProfile
      (fun g =>
        |infiniteTorusCharacterDetuning
          (infiniteTemporalCascadeCharacter b)
          (infiniteTemporalCascadeFrequency g)|)
      (b + 1) 1 := by
  constructor
  · apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with g hg
    change 0 < g at hg
    rw [infiniteTemporalCascadeCharacter_detuning,
      abs_of_pos (pow_pos hg _)]
    exact (div_self (pow_ne_zero _ (ne_of_gt hg))).symm
  · norm_num

/-- Fourier coefficient of one staircase character in the actual
countable uniformly sampled phase ensemble. -/
def infiniteTemporalCascadePhaseCoefficient
    (b : ℕ) (g A : ℝ) : ℂ :=
  ∫ x, infiniteTorusFourier
      (infiniteTemporalCascadeCharacter b) x
    ∂(infiniteTorusPhaseProbabilityMeasure
      (infiniteTemporalCascadeFrequency g) A :
        Measure (ℕ → UnitAddCircle))

/-- **No-terminal-layer witness.** For every positive order `b+1`, the
same countable analytic spectrum has a character that is unresolved at all
shorter inverse-power horizons, has the universal sinc law at order `b+1`,
and is dephased at every longer horizon. -/
theorem infiniteTemporalCascade_wallCrossing
    (b : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    (∀ r < b + 1,
      Tendsto
        (fun g =>
          infiniteTemporalCascadePhaseCoefficient
            b g (τ / g ^ r))
        (𝓝[>] 0) (𝓝 1)) ∧
    Tendsto
      (fun g =>
        infiniteTemporalCascadePhaseCoefficient
          b g (τ / g ^ (b + 1)))
      (𝓝[>] 0) (𝓝 (Real.sinc τ)) ∧
    (∀ r, b + 1 < r →
      Tendsto
        (fun g =>
          infiniteTemporalCascadePhaseCoefficient
            b g (τ / g ^ r))
        (𝓝[>] 0) (𝓝 0)) := by
  have hwall :=
    spectralCharacterReporter_wallCrossing
      (infiniteTemporalCascadeCharacter_birthProfile b) hτ
  constructor
  · intro r hr
    have ht := hwall.1 r hr
    apply
      (Complex.continuous_ofReal.continuousAt.tendsto.comp ht).congr'
    filter_upwards [self_mem_nhdsWithin] with g hg
    change 0 < g at hg
    rw [infiniteTemporalCascadePhaseCoefficient,
      infiniteTorusPhaseProbabilityMeasure_fourier_integral,
      infiniteTemporalCascadeCharacter_detuning]
    simp only [Function.comp_apply,
      infiniteTemporalCascadeCharacter_detuning,
      abs_of_pos (pow_pos hg _)]
    apply congrArg (fun x : ℝ => (Real.sinc x : ℂ))
    ring
  constructor
  · have ht :
        Tendsto
          (fun g =>
            Real.sinc
              (τ *
                (|infiniteTorusCharacterDetuning
                    (infiniteTemporalCascadeCharacter b)
                    (infiniteTemporalCascadeFrequency g)| /
                  g ^ (b + 1))))
          (𝓝[>] 0) (𝓝 (Real.sinc τ)) := by
      simpa using hwall.2.1
    apply
      (Complex.continuous_ofReal.continuousAt.tendsto.comp ht).congr'
    filter_upwards [self_mem_nhdsWithin] with g hg
    change 0 < g at hg
    rw [infiniteTemporalCascadePhaseCoefficient,
      infiniteTorusPhaseProbabilityMeasure_fourier_integral,
      infiniteTemporalCascadeCharacter_detuning]
    simp only [Function.comp_apply,
      infiniteTemporalCascadeCharacter_detuning,
      abs_of_pos (pow_pos hg _)]
    apply congrArg (fun x : ℝ => (Real.sinc x : ℂ))
    ring
  · intro r hr
    have ht := hwall.2.2 r hr
    apply
      (Complex.continuous_ofReal.continuousAt.tendsto.comp ht).congr'
    filter_upwards [self_mem_nhdsWithin] with g hg
    change 0 < g at hg
    rw [infiniteTemporalCascadePhaseCoefficient,
      infiniteTorusPhaseProbabilityMeasure_fourier_integral,
      infiniteTemporalCascadeCharacter_detuning]
    simp only [Function.comp_apply,
      infiniteTemporalCascadeCharacter_detuning,
      abs_of_pos (pow_pos hg _)]
    apply congrArg (fun x : ℝ => (Real.sinc x : ℂ))
    ring

/-- At every inverse-power horizon the complete probability law of the
nonterminating countable cascade still has one unique weak limit. -/
theorem existsUnique_infiniteTemporalCascadePhaseLaw_limit
    (r : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    ∃! μ : ProbabilityMeasure (ℕ → UnitAddCircle),
      Tendsto
        (fun g =>
          infiniteTorusPhaseProbabilityMeasure
            (infiniteTemporalCascadeFrequency g)
            (τ / g ^ r))
        (𝓝[>] 0) (𝓝 μ) := by
  exact existsUnique_countableAnalyticPhaseEnsemble_limit
    infiniteTemporalCascadeEnergy
    infiniteTemporalCascadeSeries
    infiniteTemporalCascadeSeries_spec
    infiniteTemporalCascadeFrequency
    infiniteTemporalCascadeEnergy_eventually_real
    r hτ

end

end GaloisForLFunctions.HTGeometry
