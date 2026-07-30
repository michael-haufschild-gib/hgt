import GaloisForLFunctions.HTGeometry.InfiniteTorusFourierWeakConvergenceLaw
import GaloisForLFunctions.HTGeometry.TemporalCharacterWallCrossingLaw

/-!
# Complete phase-law wall crossing for countable analytic spectra

Finite-support characters make analytic birth and Fourier convergence
well-defined for every countable pure-point spectrum.  If each real
spectral branch is analytic near the reference coupling, then every
character is either an exact local relation or has one exact birth order.
At every inverse-power horizon the entire probability law on the countable
product phase torus consequently has one unique weak limit.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Analytic response of a finite-support character of an arbitrary
spectrum. -/
def countableAnalyticCharacterResponse
    {I : Type*} (energy : I → ℂ → ℂ)
    (n : I →₀ ℤ) (g : ℂ) : ℂ :=
  n.sum fun i m => (m : ℂ) * energy i g

/-- Formal series of a finite-support arbitrary-spectrum character. -/
def countableAnalyticCharacterSeries
    {I : Type*}
    (series : I → FormalMultilinearSeries ℂ ℂ ℂ)
    (n : I →₀ ℤ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  n.sum fun i m => (m : ℂ) • series i

/-- Every finite-support character inherits a finite sum analytic series. -/
theorem hasFPowerSeriesAt_countableAnalyticCharacterResponse
    {I : Type*}
    (energy : I → ℂ → ℂ)
    (series : I → FormalMultilinearSeries ℂ ℂ ℂ)
    (henergy : ∀ i, HasFPowerSeriesAt (energy i) (series i) 0)
    (n : I →₀ ℤ) :
    HasFPowerSeriesAt
      (countableAnalyticCharacterResponse energy n)
      (countableAnalyticCharacterSeries series n) 0 := by
  classical
  unfold countableAnalyticCharacterResponse
    countableAnalyticCharacterSeries
  change
    HasFPowerSeriesAt
      (fun g =>
        n.support.sum fun i => (n i : ℂ) * energy i g)
      (n.support.sum fun i => (n i : ℂ) • series i) 0
  induction n.support using Finset.induction_on with
  | empty =>
      simpa using
        (hasFPowerSeriesAt_const
          (𝕜 := ℂ) (E := ℂ) (c := (0 : ℂ)) (e := (0 : ℂ)))
  | @insert i indices hi ih =>
      simp only [Finset.sum_insert hi]
      have hterm :=
        (henergy i).const_smul (c := (n i : ℂ))
      have hsmulFun :
          ((n i : ℂ) • energy i) =
            (fun g => (n i : ℂ) * energy i g) := by
        funext g
        change (n i : ℂ) • energy i g =
          (n i : ℂ) * energy i g
        exact smul_eq_mul _ _
      rw [hsmulFun] at hterm
      convert hterm.add ih using 1
      funext g
      rfl

/-- Complete birth-profile dichotomy for every finite-support character of
a countable spectrum. -/
def HasCompleteCountableCharacterBirthProfiles
    {I : Type*} (omega : ℝ → I → ℝ) : Prop :=
  ∀ n : I →₀ ℤ,
    (∀ᶠ g in 𝓝[>] (0 : ℝ),
      infiniteTorusCharacterDetuning n (omega g) = 0) ∨
    ∃ b : ℕ, ∃ c : ℝ,
      HasPositiveBirthProfile
        (fun g =>
          |infiniteTorusCharacterDetuning n (omega g)|) b c

/-- Analytic real branches automatically give a complete birth profile to
every finite-support character, without a finite ambient spectrum. -/
theorem hasCompleteCountableCharacterBirthProfiles_of_analytic
    {I : Type*}
    (energy : I → ℂ → ℂ)
    (series : I → FormalMultilinearSeries ℂ ℂ ℂ)
    (henergy : ∀ i, HasFPowerSeriesAt (energy i) (series i) 0)
    (omega : ℝ → I → ℝ)
    (hreal : ∀ i, ∀ᶠ (g : ℝ) in 𝓝[>] (0 : ℝ),
      energy i (g : ℂ) = (omega g i : ℂ)) :
    HasCompleteCountableCharacterBirthProfiles omega := by
  classical
  intro n
  let response := countableAnalyticCharacterResponse energy n
  let responseSeries := countableAnalyticCharacterSeries series n
  have hseries :
      HasFPowerSeriesAt response responseSeries 0 :=
    hasFPowerSeriesAt_countableAnalyticCharacterResponse
      energy series henergy n
  have hallReal :
      ∀ᶠ (g : ℝ) in 𝓝[>] (0 : ℝ), ∀ i ∈ n.support,
        energy i (g : ℂ) = (omega g i : ℂ) := by
    rw [Finset.eventually_all]
    intro i hi
    exact hreal i
  have hresponseReal :
      ∀ᶠ (g : ℝ) in 𝓝[>] (0 : ℝ),
        response (g : ℂ) =
          (infiniteTorusCharacterDetuning n (omega g) : ℂ) := by
    filter_upwards [hallReal] with g hg
    unfold response countableAnalyticCharacterResponse
    unfold infiniteTorusCharacterDetuning
    rw [Finsupp.sum, Finsupp.sum]
    push_cast
    apply Finset.sum_congr rfl
    intro i hi
    rw [hg i hi]
  by_cases hactive : AnalyticSectorActive response
  · right
    refine ⟨analyticBirthOrder responseSeries,
      ‖analyticBirthUnit response responseSeries 0‖, ?_⟩
    have hprofile :=
      hasPositiveBirthProfile_norm_of_active hseries hactive
    refine ⟨?_, hprofile.2⟩
    apply hprofile.1.congr'
    filter_upwards [hresponseReal] with g hg
    rw [hg]
    simp [Complex.norm_real, Real.norm_eq_abs]
  · left
    have hzero :
        response =ᶠ[𝓝 0] (fun _ : ℂ => 0) := by
      simpa [AnalyticSectorActive] using hactive
    have ht :
        Tendsto (fun g : ℝ => (g : ℂ))
          (𝓝[>] 0) (𝓝 0) :=
      Complex.continuous_ofReal.continuousAt.tendsto.mono_left
        inf_le_left
    have hzeroReal := hzero.comp_tendsto ht
    filter_upwards [hzeroReal, hresponseReal] with g hg hgr
    apply Complex.ofReal_eq_zero.mp
    rw [← hgr]
    exact hg

private theorem countable_sinc_mul_abs_eq
    (a x : ℝ) (ha : 0 ≤ a) :
    Real.sinc (a * |x|) = Real.sinc (a * x) := by
  have h : Real.sinc |a * x| = Real.sinc (a * x) := by
    by_cases hx : 0 ≤ a * x
    · rw [abs_of_nonneg hx]
    · rw [abs_of_neg (lt_of_not_ge hx)]
      exact Real.sinc_neg (a * x)
  rw [abs_mul, abs_of_nonneg ha] at h
  exact h

private theorem countable_coe_sinc_scaled_abs_eq
    (τ x g : ℝ) (r : ℕ) (hτ : 0 ≤ τ) (hg : 0 < g) :
    (Real.sinc ((τ / g ^ r) * x) : ℂ) =
      (Real.sinc (τ * (|x| / g ^ r)) : ℂ) := by
  apply congrArg (fun y : ℝ => (y : ℂ))
  rw [show
    τ * (|x| / g ^ r) = (τ / g ^ r) * |x| by
      field_simp]
  exact
    (countable_sinc_mul_abs_eq
      (τ / g ^ r) x
      (div_nonneg hτ (pow_nonneg hg.le r))).symm

/-- Every finite-support Fourier coefficient of the countable phase
ensemble converges at every inverse-power horizon. -/
theorem exists_countablePhaseCharacterCoefficient_limit
    {I : Type*} [Countable I]
    (omega : ℝ → I → ℝ)
    (hcomplete : HasCompleteCountableCharacterBirthProfiles omega)
    (r : ℕ) {τ : ℝ} (hτ : 0 < τ)
    (n : I →₀ ℤ) :
    ∃ L : ℂ,
      Tendsto
        (fun g =>
          ∫ x, infiniteTorusFourier n x
            ∂(infiniteTorusPhaseProbabilityMeasure
              (omega g) (τ / g ^ r) :
                Measure (I → UnitAddCircle)))
        (𝓝[>] 0) (𝓝 L) := by
  rcases hcomplete n with hinactive | ⟨b, c, hprofile⟩
  · refine ⟨1, ?_⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [hinactive, self_mem_nhdsWithin] with g hgzero hg
    change 0 < g at hg
    rw [infiniteTorusPhaseProbabilityMeasure_fourier_integral, hgzero]
    simp
  · have hwall :=
      spectralCharacterReporter_wallCrossing hprofile hτ
    rcases lt_trichotomy r b with hrb | hrb | hbr
    · refine ⟨1, ?_⟩
      have ht := hwall.1 r hrb
      apply
        (Complex.continuous_ofReal.continuousAt.tendsto.comp ht).congr'
      filter_upwards [self_mem_nhdsWithin] with g hg
      change 0 < g at hg
      rw [infiniteTorusPhaseProbabilityMeasure_fourier_integral]
      exact (countable_coe_sinc_scaled_abs_eq τ
        (infiniteTorusCharacterDetuning n (omega g))
        g r hτ.le hg).symm
    · subst b
      refine ⟨Real.sinc (τ * c), ?_⟩
      have ht := hwall.2.1
      apply
        (Complex.continuous_ofReal.continuousAt.tendsto.comp ht).congr'
      filter_upwards [self_mem_nhdsWithin] with g hg
      change 0 < g at hg
      rw [infiniteTorusPhaseProbabilityMeasure_fourier_integral]
      exact (countable_coe_sinc_scaled_abs_eq τ
        (infiniteTorusCharacterDetuning n (omega g))
        g r hτ.le hg).symm
    · refine ⟨0, ?_⟩
      have ht := hwall.2.2 r hbr
      apply
        (Complex.continuous_ofReal.continuousAt.tendsto.comp ht).congr'
      filter_upwards [self_mem_nhdsWithin] with g hg
      change 0 < g at hg
      rw [infiniteTorusPhaseProbabilityMeasure_fourier_integral]
      exact (countable_coe_sinc_scaled_abs_eq τ
        (infiniteTorusCharacterDetuning n (omega g))
        g r hτ.le hg).symm

/-- **Complete countable phase-law wall crossing.** At every inverse-power
observation horizon, the entire uniformly time-sampled phase law of a
countable analytic real spectrum has one unique weak limit. -/
theorem existsUnique_countableAnalyticPhaseEnsemble_limit
    {I : Type*} [Countable I]
    (energy : I → ℂ → ℂ)
    (series : I → FormalMultilinearSeries ℂ ℂ ℂ)
    (henergy : ∀ i, HasFPowerSeriesAt (energy i) (series i) 0)
    (omega : ℝ → I → ℝ)
    (hreal : ∀ i, ∀ᶠ (g : ℝ) in 𝓝[>] (0 : ℝ),
      energy i (g : ℂ) = (omega g i : ℂ))
    (r : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    ∃! μ : ProbabilityMeasure (I → UnitAddCircle),
      Tendsto
        (fun g =>
          infiniteTorusPhaseProbabilityMeasure
            (omega g) (τ / g ^ r))
        (𝓝[>] 0) (𝓝 μ) := by
  have hcomplete :=
    hasCompleteCountableCharacterBirthProfiles_of_analytic
      energy series henergy omega hreal
  have hcoeff :
      ∀ n : I →₀ ℤ, ∃ L : ℂ,
        Tendsto
          (fun g =>
            ∫ x, infiniteTorusFourier n x
              ∂(infiniteTorusPhaseProbabilityMeasure
                (omega g) (τ / g ^ r) :
                  Measure (I → UnitAddCircle)))
          (𝓝[>] 0) (𝓝 L) :=
    exists_countablePhaseCharacterCoefficient_limit
      omega hcomplete r hτ
  let limit : (I →₀ ℤ) → ℂ :=
    fun n => Classical.choose (hcoeff n)
  have hlimit : ∀ n : I →₀ ℤ,
      Tendsto
        (fun g =>
          ∫ x, infiniteTorusFourier n x
            ∂(infiniteTorusPhaseProbabilityMeasure
              (omega g) (τ / g ^ r) :
                Measure (I → UnitAddCircle)))
        (𝓝[>] 0) (𝓝 (limit n)) :=
    fun n => Classical.choose_spec (hcoeff n)
  obtain ⟨μ, hμ, hunique⟩ :=
    existsUnique_probabilityMeasure_tendsto_of_infiniteTorusFourier_limit
      (fun g =>
        infiniteTorusPhaseProbabilityMeasure
          (omega g) (τ / g ^ r))
      limit hlimit
  refine ⟨μ, hμ.1, ?_⟩
  intro ν hν
  exact tendsto_nhds_unique hν hμ.1

end

end GaloisForLFunctions.HTGeometry
