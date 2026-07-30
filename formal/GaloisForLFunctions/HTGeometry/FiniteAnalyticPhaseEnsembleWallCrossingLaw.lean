import GaloisForLFunctions.HTGeometry.FiniteTorusPhaseEnsembleLaw
import GaloisForLFunctions.HTGeometry.TorusFourierWeakConvergenceLaw
import GaloisForLFunctions.HTGeometry.TemporalCharacterWallCrossingLaw

/-!
# Complete phase-law wall crossing for finite analytic spectra

Every integer character of a finite analytic real spectrum is either an
exact local relation or has one positive exact birth profile.  Therefore
all Fourier coefficients of the actual uniformly time-sampled phase law
converge at every inverse-power observation horizon.  Compact Fourier
rigidity then upgrades these characterwise limits to one unique weak limit
of the whole phase probability law.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Complex analytic response of one finite torus character. -/
def finiteAnalyticCharacterResponse
    {d : Type*} [Fintype d]
    (energy : d → ℂ → ℂ) (n : d → ℤ) (g : ℂ) : ℂ :=
  ∑ i, (n i : ℂ) * energy i g

/-- Formal series of one finite torus character response. -/
def finiteAnalyticCharacterSeries
    {d : Type*} [Fintype d]
    (series : d → FormalMultilinearSeries ℂ ℂ ℂ)
    (n : d → ℤ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  ∑ i, (n i : ℂ) • series i

/-- Finite character combinations inherit the branchwise analytic series. -/
theorem hasFPowerSeriesAt_finiteAnalyticCharacterResponse
    {d : Type*} [Fintype d]
    (energy : d → ℂ → ℂ)
    (series : d → FormalMultilinearSeries ℂ ℂ ℂ)
    (henergy : ∀ i, HasFPowerSeriesAt (energy i) (series i) 0)
    (n : d → ℤ) :
    HasFPowerSeriesAt
      (finiteAnalyticCharacterResponse energy n)
      (finiteAnalyticCharacterSeries series n) 0 := by
  classical
  unfold finiteAnalyticCharacterResponse finiteAnalyticCharacterSeries
  induction (Finset.univ : Finset d) using Finset.induction_on with
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

/-- Every finite character is either an exact local relation or has a
positive exact birth profile. -/
def HasCompleteFiniteCharacterBirthProfiles
    {d : Type*} [Fintype d]
    (omega : ℝ → d → ℝ) : Prop :=
  ∀ n : d → ℤ,
    (∀ᶠ g in 𝓝[>] (0 : ℝ),
      finiteTorusCharacterDetuning n (omega g) = 0) ∨
    ∃ b : ℕ, ∃ c : ℝ,
      HasPositiveBirthProfile
        (fun g =>
          |finiteTorusCharacterDetuning n (omega g)|) b c

/-- Analytic real spectral branches automatically give complete birth
profiles for every integer character. -/
theorem hasCompleteFiniteCharacterBirthProfiles_of_analytic
    {d : Type*} [Fintype d]
    (energy : d → ℂ → ℂ)
    (series : d → FormalMultilinearSeries ℂ ℂ ℂ)
    (henergy : ∀ i, HasFPowerSeriesAt (energy i) (series i) 0)
    (omega : ℝ → d → ℝ)
    (hreal : ∀ i, ∀ᶠ (g : ℝ) in 𝓝[>] (0 : ℝ),
      energy i (g : ℂ) = (omega g i : ℂ)) :
    HasCompleteFiniteCharacterBirthProfiles omega := by
  classical
  intro n
  let response := finiteAnalyticCharacterResponse energy n
  let responseSeries := finiteAnalyticCharacterSeries series n
  have hseries :
      HasFPowerSeriesAt response responseSeries 0 :=
    hasFPowerSeriesAt_finiteAnalyticCharacterResponse
      energy series henergy n
  have hallReal :
      ∀ᶠ (g : ℝ) in 𝓝[>] (0 : ℝ), ∀ i,
        energy i (g : ℂ) = (omega g i : ℂ) := by
    rw [Filter.eventually_all]
    exact hreal
  have hresponseReal :
      ∀ᶠ (g : ℝ) in 𝓝[>] (0 : ℝ),
        response (g : ℂ) =
          (finiteTorusCharacterDetuning n (omega g) : ℂ) := by
    filter_upwards [hallReal] with g hg
    unfold response finiteAnalyticCharacterResponse
    unfold finiteTorusCharacterDetuning
    push_cast
    apply Finset.sum_congr rfl
    intro i hi
    rw [hg]
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

/-- Sinc is even after multiplying by a nonnegative scale. -/
private theorem sinc_mul_abs_eq
    (a x : ℝ) (ha : 0 ≤ a) :
    Real.sinc (a * |x|) = Real.sinc (a * x) := by
  have h : Real.sinc |a * x| = Real.sinc (a * x) := by
    by_cases hx : 0 ≤ a * x
    · rw [abs_of_nonneg hx]
    · rw [abs_of_neg (lt_of_not_ge hx)]
      exact Real.sinc_neg (a * x)
  rw [abs_mul, abs_of_nonneg ha] at h
  exact h

/-- The physical positive-coupling ray makes division by `g ^ r`
compatible with sinc evenness. -/
private theorem coe_sinc_scaled_abs_eq
    (τ x g : ℝ) (r : ℕ) (hτ : 0 ≤ τ) (hg : 0 < g) :
    (Real.sinc ((τ / g ^ r) * x) : ℂ) =
      (Real.sinc (τ * (|x| / g ^ r)) : ℂ) := by
  apply congrArg (fun y : ℝ => (y : ℂ))
  rw [show
    τ * (|x| / g ^ r) = (τ / g ^ r) * |x| by
      field_simp]
  exact
    (sinc_mul_abs_eq
      (τ / g ^ r) x
      (div_nonneg hτ (pow_nonneg hg.le r))).symm

/-- Every Fourier coefficient of the finite phase ensemble converges at
every inverse-power observation horizon. -/
theorem exists_finitePhaseCharacterCoefficient_limit
    {d : Type*} [Fintype d]
    (omega : ℝ → d → ℝ)
    (hcomplete : HasCompleteFiniteCharacterBirthProfiles omega)
    (r : ℕ) {τ : ℝ} (hτ : 0 < τ)
    (n : d → ℤ) :
    ∃ L : ℂ,
      Tendsto
        (fun g =>
          ∫ x, UnitAddTorus.mFourier n x
            ∂(finiteTorusPhaseProbabilityMeasure
              (omega g) (τ / g ^ r) :
                Measure (UnitAddTorus d)))
        (𝓝[>] 0) (𝓝 L) := by
  rcases hcomplete n with hinactive | ⟨b, c, hprofile⟩
  · refine ⟨1, ?_⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [hinactive, self_mem_nhdsWithin] with g hgzero hg
    change 0 < g at hg
    rw [finiteTorusPhaseProbabilityMeasure_mFourier_integral, hgzero]
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
      rw [finiteTorusPhaseProbabilityMeasure_mFourier_integral]
      exact (coe_sinc_scaled_abs_eq τ
        (finiteTorusCharacterDetuning n (omega g)) g r hτ.le hg).symm
    · subst b
      refine ⟨Real.sinc (τ * c), ?_⟩
      have ht := hwall.2.1
      apply
        (Complex.continuous_ofReal.continuousAt.tendsto.comp ht).congr'
      filter_upwards [self_mem_nhdsWithin] with g hg
      change 0 < g at hg
      rw [finiteTorusPhaseProbabilityMeasure_mFourier_integral]
      exact (coe_sinc_scaled_abs_eq τ
        (finiteTorusCharacterDetuning n (omega g)) g r hτ.le hg).symm
    · refine ⟨0, ?_⟩
      have ht := hwall.2.2 r hbr
      apply
        (Complex.continuous_ofReal.continuousAt.tendsto.comp ht).congr'
      filter_upwards [self_mem_nhdsWithin] with g hg
      change 0 < g at hg
      rw [finiteTorusPhaseProbabilityMeasure_mFourier_integral]
      exact (coe_sinc_scaled_abs_eq τ
        (finiteTorusCharacterDetuning n (omega g)) g r hτ.le hg).symm

/-- **Complete finite phase-law wall crossing.**  At every inverse-power
observation horizon, the entire uniformly time-sampled phase probability
law of a finite analytic real spectrum has one unique weak limit. -/
theorem existsUnique_finitePhaseBirthEnsemble_limit
    {d : Type*} [Fintype d]
    (omega : ℝ → d → ℝ)
    (hcomplete : HasCompleteFiniteCharacterBirthProfiles omega)
    (r : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    ∃! μ : ProbabilityMeasure (UnitAddTorus d),
      Tendsto
        (fun g =>
          finiteTorusPhaseProbabilityMeasure
            (omega g) (τ / g ^ r))
        (𝓝[>] 0) (𝓝 μ) := by
  have hcoeff :
      ∀ n : d → ℤ, ∃ L : ℂ,
        Tendsto
          (fun g =>
            ∫ x, UnitAddTorus.mFourier n x
              ∂(finiteTorusPhaseProbabilityMeasure
                (omega g) (τ / g ^ r) :
                  Measure (UnitAddTorus d)))
          (𝓝[>] 0) (𝓝 L) :=
    exists_finitePhaseCharacterCoefficient_limit
      omega hcomplete r hτ
  let limit : (d → ℤ) → ℂ :=
    fun n => Classical.choose (hcoeff n)
  have hlimit : ∀ n : d → ℤ,
      Tendsto
        (fun g =>
          ∫ x, UnitAddTorus.mFourier n x
            ∂(finiteTorusPhaseProbabilityMeasure
              (omega g) (τ / g ^ r) :
                Measure (UnitAddTorus d)))
        (𝓝[>] 0) (𝓝 (limit n)) :=
    fun n => Classical.choose_spec (hcoeff n)
  obtain ⟨μ, hμ, hunique⟩ :=
    existsUnique_probabilityMeasure_tendsto_of_mFourier_limit
      (fun g =>
        finiteTorusPhaseProbabilityMeasure
          (omega g) (τ / g ^ r))
      limit hlimit
  refine ⟨μ, hμ.1, ?_⟩
  intro ν hν
  exact tendsto_nhds_unique hν hμ.1

/-- Direct analytic-spectrum form of complete finite phase-law wall
crossing. -/
theorem existsUnique_finiteAnalyticPhaseEnsemble_limit
    {d : Type*} [Fintype d]
    (energy : d → ℂ → ℂ)
    (series : d → FormalMultilinearSeries ℂ ℂ ℂ)
    (henergy : ∀ i, HasFPowerSeriesAt (energy i) (series i) 0)
    (omega : ℝ → d → ℝ)
    (hreal : ∀ i, ∀ᶠ (g : ℝ) in 𝓝[>] (0 : ℝ),
      energy i (g : ℂ) = (omega g i : ℂ))
    (r : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    ∃! μ : ProbabilityMeasure (UnitAddTorus d),
      Tendsto
        (fun g =>
          finiteTorusPhaseProbabilityMeasure
            (omega g) (τ / g ^ r))
        (𝓝[>] 0) (𝓝 μ) :=
  existsUnique_finitePhaseBirthEnsemble_limit omega
    (hasCompleteFiniteCharacterBirthProfiles_of_analytic
      energy series henergy omega hreal)
    r hτ

end

end GaloisForLFunctions.HTGeometry
