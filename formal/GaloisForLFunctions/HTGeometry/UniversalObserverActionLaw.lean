import GaloisForLFunctions.HTGeometry.FiniteTorusPhaseEnsembleLaw
import GaloisForLFunctions.HTGeometry.TorusFourierWeakConvergenceLaw
import GaloisForLFunctions.HTGeometry.InfiniteTorusFourierWeakConvergenceLaw
import GaloisForLFunctions.HTGeometry.TemporalCharacterWallCrossingLaw
import GaloisForLFunctions.HTGeometry.ObserverTemporalPhaseSupportLaw

/-!
# Universal observer-action law

The inverse-power horizons of analytic perturbation theory are slices of a
more general invariant.  For an arbitrary observation clock `T` and an
arbitrary real spectrum, a character sees only the dimensionless action

`T * character detuning`.

There are two convergent regimes relevant to the complete probability law:
the action has a finite limit, or its absolute value diverges.  In the first
case the limiting character coefficient is the sinc of that finite action;
in the second it is zero.  If every finite-support character has one of
these regimes, the entire phase probability law has one unique weak limit.

No analyticity, perturbative parameter, Hamiltonian realization, finite
matrix dimension, or inverse-power clock is used in the master theorem.
Those structures enter only when one wants to calculate the action regime.
-/

open Filter MeasureTheory Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The convergent asymptotic possibilities for one observed character
action.  A finite limit includes both a frozen relation (`a = 0`) and a
finite crossover (`a ≠ 0`). -/
inductive ObserverActionRegime where
  | finite (a : ℝ)
  | dephased
  deriving DecidableEq

/-- Universal Fourier coefficient carried by an observer-action regime. -/
def observerActionRegimeCoefficient :
    ObserverActionRegime → ℂ
  | .finite a => Real.sinc a
  | .dephased => 0

/-- An action family realizes a finite or dephased observer-action regime
along a filter. -/
def HasObserverActionRegime
    {α : Type*} (l : Filter α) (action : α → ℝ) :
    ObserverActionRegime → Prop
  | .finite a => Tendsto action l (𝓝 a)
  | .dephased => Tendsto (fun x => |action x|) l atTop

/-- Sinc is unchanged after replacing a real action by its magnitude. -/
theorem real_sinc_abs (x : ℝ) :
    Real.sinc |x| = Real.sinc x := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg (lt_of_not_ge hx), Real.sinc_neg]

/-- **Character observer-action law.** Every realized action regime has
the corresponding universal sinc Fourier limit. -/
theorem tendsto_sinc_of_hasObserverActionRegime
    {α : Type*} {l : Filter α}
    {action : α → ℝ} {regime : ObserverActionRegime}
    (hregime : HasObserverActionRegime l action regime) :
    Tendsto
      (fun x => (Real.sinc (action x) : ℂ))
      l (𝓝 (observerActionRegimeCoefficient regime)) := by
  cases regime with
  | finite a =>
      have hsinc :
          Tendsto (fun x => Real.sinc (action x))
            l (𝓝 (Real.sinc a)) :=
        Real.continuous_sinc.continuousAt.tendsto.comp hregime
      change
        Tendsto
          (Complex.ofReal ∘ fun x => Real.sinc (action x))
          l (𝓝 (Real.sinc a : ℂ))
      exact
        Complex.continuous_ofReal.continuousAt.tendsto.comp hsinc
  | dephased =>
      have hsinc :
          Tendsto (fun x => Real.sinc |action x|)
            l (𝓝 0) :=
        tendsto_real_sinc_atTop_zero.comp hregime
      have hsinc' :
          Tendsto (fun x => Real.sinc (action x))
            l (𝓝 0) := by
        apply hsinc.congr'
        filter_upwards [] with x
        exact real_sinc_abs (action x)
      change
        Tendsto
          (Complex.ofReal ∘ fun x => Real.sinc (action x))
          l (𝓝 (0 : ℂ))
      exact
        Complex.continuous_ofReal.continuousAt.tendsto.comp hsinc'

/-- A finite observer action leaves a character perfectly locked exactly
when that action is zero. -/
theorem coe_real_sinc_eq_one_iff
    (a : ℝ) :
    (Real.sinc a : ℂ) = 1 ↔ a = 0 := by
  constructor
  · intro h
    by_contra ha
    apply real_sinc_ne_one_of_ne_zero ha
    apply Complex.ofReal_injective
    simpa using h
  · rintro rfl
    simp

/-- The zero-action regime is exactly the regime whose universal Fourier
coefficient equals one. -/
theorem observerActionRegimeCoefficient_eq_one_iff
    (regime : ObserverActionRegime) :
    observerActionRegimeCoefficient regime = 1 ↔
      regime = .finite 0 := by
  cases regime with
  | finite a =>
      simp only [observerActionRegimeCoefficient,
        coe_real_sinc_eq_one_iff]
      constructor
      · rintro rfl
        rfl
      · exact ObserverActionRegime.finite.inj
  | dephased =>
      simp [observerActionRegimeCoefficient]

/-- Dimensionless action of a finite-torus character under an arbitrary
observation clock. -/
def finiteObserverAction
    {α d : Type*} [Fintype d]
    (omega : α → d → ℝ) (clock : α → ℝ)
    (n : d → ℤ) (x : α) : ℝ :=
  clock x * finiteTorusCharacterDetuning n (omega x)

/-- Every finite-torus observer action has a convergent window coefficient.
This is the exact characterwise criterion; it is more general than asking
the underlying action itself to converge or diverge. -/
def HasCompleteFiniteObserverActionLimits
    {α d : Type*} [Fintype d]
    (l : Filter α) (omega : α → d → ℝ)
    (clock : α → ℝ) : Prop :=
  ∀ n : d → ℤ, ∃ c : ℂ,
    Tendsto
      (fun x =>
        (Real.sinc (finiteObserverAction omega clock n x) : ℂ))
      l (𝓝 c)

/-- **Finite observer-action completeness law.** A phase-history scaling
law exists if and only if every integer spectral relation has a convergent
windowed action coefficient.  Whenever it exists, the complete probability
law is unique. -/
theorem existsUnique_finitePhaseLimit_iff_completeObserverActionLimits
    {α d : Type*} [Fintype d]
    {l : Filter α} [l.NeBot]
    (omega : α → d → ℝ) (clock : α → ℝ) :
    (∃! μ : ProbabilityMeasure (UnitAddTorus d),
      Tendsto
        (fun x =>
          finiteTorusPhaseProbabilityMeasure
            (omega x) (clock x))
        l (𝓝 μ)) ↔
      HasCompleteFiniteObserverActionLimits
        l omega clock := by
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
    symm
    rw [finiteTorusPhaseProbabilityMeasure_mFourier_integral]
    rfl
  · intro hcomplete
    choose limit hlimit using hcomplete
    have hcoefficient : ∀ n : d → ℤ,
        Tendsto
          (fun x =>
            ∫ y, UnitAddTorus.mFourier n y
              ∂(finiteTorusPhaseProbabilityMeasure
                (omega x) (clock x) :
                  Measure (UnitAddTorus d)))
          l (𝓝 (limit n)) := by
      intro n
      apply (hlimit n).congr'
      filter_upwards [] with x
      rw [finiteTorusPhaseProbabilityMeasure_mFourier_integral]
      rfl
    obtain ⟨μ, hμ, hμunique⟩ :=
      existsUnique_probabilityMeasure_tendsto_of_mFourier_limit
        (fun x =>
          finiteTorusPhaseProbabilityMeasure
            (omega x) (clock x))
        limit hcoefficient
    refine ⟨μ, hμ.1, ?_⟩
    intro ν hν
    exact tendsto_nhds_unique hν hμ.1

/-- **Finite-spectrum universal observer-action law.** For every real
finite spectrum and every observation clock, if every integer character
action has a finite or dephased regime, then the complete phase ensemble
has one unique weak limit.  Every continuous phase statistic is therefore
fixed by the regime profile. -/
theorem existsUnique_finiteObserverActionLimitLaw
    {α d : Type*} [Fintype d]
    {l : Filter α} [l.NeBot]
    (omega : α → d → ℝ) (clock : α → ℝ)
    (profile : (d → ℤ) → ObserverActionRegime)
    (hprofile : ∀ n,
      HasObserverActionRegime l
        (finiteObserverAction omega clock n) (profile n)) :
    ∃! μ : ProbabilityMeasure (UnitAddTorus d),
      Tendsto
          (fun x =>
            finiteTorusPhaseProbabilityMeasure
              (omega x) (clock x))
          l (𝓝 μ) ∧
        ∀ n : d → ℤ,
          (∫ y, UnitAddTorus.mFourier n y
              ∂(μ : Measure (UnitAddTorus d))) =
            observerActionRegimeCoefficient (profile n) := by
  apply existsUnique_probabilityMeasure_tendsto_of_mFourier_limit
    (fun x =>
      finiteTorusPhaseProbabilityMeasure
        (omega x) (clock x))
    (fun n => observerActionRegimeCoefficient (profile n))
  intro n
  have hlimit :=
    tendsto_sinc_of_hasObserverActionRegime (hprofile n)
  apply hlimit.congr'
  filter_upwards [] with x
  rw [finiteTorusPhaseProbabilityMeasure_mFourier_integral]
  rfl

/-- Projective rational span of exactly those characters whose limiting
observer action is zero. -/
def observerActionZeroConstraintRationalSpace
    {d : Type*} [Fintype d]
    (profile : (d → ℤ) → ObserverActionRegime) :
    Submodule ℚ (ProjectiveRationalCharacter d) :=
  Submodule.span ℚ
    (projectiveCharacterToRational ''
      {k : ProjectiveCharacter d |
        profile (finiteCharacterOfProjective k) = .finite 0})

/-- **Observer-time constraint identification.** Almost-sure phase
relations in an observer-action limit law are exactly its zero-action
characters.  Finite nonzero crossover actions and dephased actions are
both operationally unlocked. -/
theorem phaseLawConstraint_iff_observerAction_zero
    {d : Type*} [Fintype d]
    (μ : ProbabilityMeasure (UnitAddTorus d))
    (profile : (d → ℤ) → ObserverActionRegime)
    (hcoeff : ∀ n : d → ℤ,
      (∫ y, UnitAddTorus.mFourier n y
          ∂(μ : Measure (UnitAddTorus d))) =
        observerActionRegimeCoefficient (profile n))
    (k : ProjectiveCharacter d) :
    phaseLawConstraint μ k ↔
      profile (finiteCharacterOfProjective k) = .finite 0 := by
  rw [phaseLawConstraint_iff_integral_eq_one,
    hcoeff (finiteCharacterOfProjective k),
    observerActionRegimeCoefficient_eq_one_iff]

/-- The complete rational constraint space of a limiting phase law is the
rational span of its zero-action characters. -/
theorem phaseLawConstraintRationalSpace_eq_observerActionZero
    {d : Type*} [Fintype d]
    (μ : ProbabilityMeasure (UnitAddTorus d))
    (profile : (d → ℤ) → ObserverActionRegime)
    (hcoeff : ∀ n : d → ℤ,
      (∫ y, UnitAddTorus.mFourier n y
          ∂(μ : Measure (UnitAddTorus d))) =
        observerActionRegimeCoefficient (profile n)) :
    phaseLawConstraintRationalSpace μ =
      observerActionZeroConstraintRationalSpace profile := by
  rw [phaseLawConstraintRationalSpace,
    observerActionZeroConstraintRationalSpace]
  congr 1
  ext q
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact
      ⟨k,
        (phaseLawConstraint_iff_observerAction_zero
          μ profile hcoeff k).mp hk,
        rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact
      ⟨k,
        (phaseLawConstraint_iff_observerAction_zero
          μ profile hcoeff k).mpr hk,
        rfl⟩

/-- **Arbitrary-clock temporal-dimension law.** Observer-dependent
temporal dimension is the projective character rank left after quotienting
by zero-action relations. -/
theorem phaseLawTemporalDimension_eq_observerActionQuotientRank
    {d : Type*} [Fintype d]
    (μ : ProbabilityMeasure (UnitAddTorus d))
    (profile : (d → ℤ) → ObserverActionRegime)
    (hcoeff : ∀ n : d → ℤ,
      (∫ y, UnitAddTorus.mFourier n y
          ∂(μ : Measure (UnitAddTorus d))) =
        observerActionRegimeCoefficient (profile n)) :
    phaseLawTemporalDimension μ =
      Module.finrank ℚ (ProjectiveRationalCharacter d) -
        Module.finrank ℚ
          (observerActionZeroConstraintRationalSpace profile) := by
  unfold phaseLawTemporalDimension
  rw [phaseLawConstraintRationalSpace_eq_observerActionZero
    μ profile hcoeff]

/-- **Observer-time rank conservation for arbitrary clocks.** Resolved
temporal dimension plus zero-action relation rank is the fixed complete
projective rank. -/
theorem observerAction_temporalDimension_add_zeroConstraintRank
    {d : Type*} [Fintype d]
    (μ : ProbabilityMeasure (UnitAddTorus d))
    (profile : (d → ℤ) → ObserverActionRegime)
    (hcoeff : ∀ n : d → ℤ,
      (∫ y, UnitAddTorus.mFourier n y
          ∂(μ : Measure (UnitAddTorus d))) =
        observerActionRegimeCoefficient (profile n)) :
    phaseLawTemporalDimension μ +
        Module.finrank ℚ
          (observerActionZeroConstraintRationalSpace profile) =
      Module.finrank ℚ (ProjectiveRationalCharacter d) := by
  rw [phaseLawTemporalDimension_eq_observerActionQuotientRank
    μ profile hcoeff]
  have hle :
      Module.finrank ℚ
          (observerActionZeroConstraintRationalSpace profile) ≤
        Module.finrank ℚ (ProjectiveRationalCharacter d) :=
    Submodule.finrank_le _
  omega

/-- Dimensionless action of a finite-support character of an arbitrary
countable spectrum under an arbitrary observation clock. -/
def countableObserverAction
    {α I : Type*}
    (omega : α → I → ℝ) (clock : α → ℝ)
    (n : I →₀ ℤ) (x : α) : ℝ :=
  clock x * infiniteTorusCharacterDetuning n (omega x)

/-- Every finite-support character of a countable spectrum has a convergent
windowed observer-action coefficient. -/
def HasCompleteCountableObserverActionLimits
    {α I : Type*}
    (l : Filter α) (omega : α → I → ℝ)
    (clock : α → ℝ) : Prop :=
  ∀ n : I →₀ ℤ, ∃ c : ℂ,
    Tendsto
      (fun x =>
        (Real.sinc (countableObserverAction
          omega clock n x) : ℂ))
      l (𝓝 c)

/-- **Countably infinite observer-action completeness law.** For an
arbitrary countable real spectrum and arbitrary clock, the full
product-phase probability law has a scaling limit exactly when every
finite-support spectral relation has a convergent windowed action
coefficient.  The law, if it exists, is unique. -/
theorem existsUnique_countablePhaseLimit_iff_completeObserverActionLimits
    {α I : Type*} [Countable I]
    {l : Filter α} [l.NeBot]
    (omega : α → I → ℝ) (clock : α → ℝ) :
    (∃! μ : ProbabilityMeasure (I → UnitAddCircle),
      Tendsto
        (fun x =>
          infiniteTorusPhaseProbabilityMeasure
            (omega x) (clock x))
        l (𝓝 μ)) ↔
      HasCompleteCountableObserverActionLimits
        l omega clock := by
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
    symm
    rw [infiniteTorusPhaseProbabilityMeasure_fourier_integral]
    rfl
  · intro hcomplete
    choose limit hlimit using hcomplete
    have hcoefficient : ∀ n : I →₀ ℤ,
        Tendsto
          (fun x =>
            ∫ y, infiniteTorusFourier n y
              ∂(infiniteTorusPhaseProbabilityMeasure
                (omega x) (clock x) :
                  Measure (I → UnitAddCircle)))
          l (𝓝 (limit n)) := by
      intro n
      apply (hlimit n).congr'
      filter_upwards [] with x
      rw [infiniteTorusPhaseProbabilityMeasure_fourier_integral]
      rfl
    obtain ⟨μ, hμ, hμunique⟩ :=
      existsUnique_probabilityMeasure_tendsto_of_infiniteTorusFourier_limit
        (fun x =>
          infiniteTorusPhaseProbabilityMeasure
            (omega x) (clock x))
        limit hcoefficient
    refine ⟨μ, hμ.1, ?_⟩
    intro ν hν
    exact tendsto_nhds_unique hν hμ.1

/-- **Countably infinite universal observer-action law.** For every
countable real spectrum and every observation clock, characterwise action
regimes determine one unique weak limit of the entire product-torus phase
law.  Since finite-support characters are dense, this simultaneously
determines every continuous reporter, not only the listed coefficients. -/
theorem existsUnique_countableObserverActionLimitLaw
    {α I : Type*} [Countable I]
    {l : Filter α} [l.NeBot]
    (omega : α → I → ℝ) (clock : α → ℝ)
    (profile : (I →₀ ℤ) → ObserverActionRegime)
    (hprofile : ∀ n,
      HasObserverActionRegime l
        (countableObserverAction omega clock n) (profile n)) :
    ∃! μ : ProbabilityMeasure (I → UnitAddCircle),
      Tendsto
          (fun x =>
            infiniteTorusPhaseProbabilityMeasure
              (omega x) (clock x))
          l (𝓝 μ) ∧
        ∀ n : I →₀ ℤ,
          (∫ y, infiniteTorusFourier n y
              ∂(μ : Measure (I → UnitAddCircle))) =
            observerActionRegimeCoefficient (profile n) := by
  apply
    existsUnique_probabilityMeasure_tendsto_of_infiniteTorusFourier_limit
      (fun x =>
        infiniteTorusPhaseProbabilityMeasure
          (omega x) (clock x))
      (fun n => observerActionRegimeCoefficient (profile n))
  intro n
  have hlimit :=
    tendsto_sinc_of_hasObserverActionRegime (hprofile n)
  apply hlimit.congr'
  filter_upwards [] with x
  rw [infiniteTorusPhaseProbabilityMeasure_fourier_integral]
  rfl

end

end GaloisForLFunctions.HTGeometry
