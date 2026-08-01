import GaloisForLFunctions.RHTower.FiniteContractionObserverTimeGapLaw
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Universal persistent recurrence selection

Completed recurrence has two logically separate stages. Vanishing transients
are invisible to every Lipschitz observable after Cesaro completion. For a
finite contraction, the surviving carrier is exactly its peripheral spectral
packet; if its mass is positive, that carrier is persistent mass times the
characteristic function of the normalized peripheral spectrum. The complete
return history tends to zero exactly when peripheral mass vanishes.

This removes transient subtraction from the operational open-system law:
raw histories and peripheral histories have the same completed observations.
-/

open Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

namespace RHTower

/-- Discrete Cesaro average of a complex observable. -/
def complexCesaroAverage (u : ℕ → ℂ) (N : ℕ) : ℂ :=
  (N⁻¹ : ℝ) • ∑ n ∈ Finset.range N, u n

/-- A Lipschitz observable preserves asymptotic equivalence. -/
theorem tendsto_lipschitz_difference_zero
    {a b : ℕ → ℂ} (hab : Tendsto (fun n => a n - b n) atTop (𝓝 0))
    {K : NNReal} {φ : ℂ → ℂ} (hφ : LipschitzWith K φ) :
    Tendsto (fun n => φ (a n) - φ (b n)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hnorm : Tendsto (fun n => ‖a n - b n‖) atTop (𝓝 0) := by
    simpa only [norm_zero] using hab.norm
  have hupper :
      Tendsto (fun n => (K : ℝ) * ‖a n - b n‖) atTop (𝓝 0) := by
    simpa using hnorm.const_mul (K : ℝ)
  refine squeeze_zero' (f := fun n => ‖φ (a n) - φ (b n)‖)
    (g := fun n => (K : ℝ) * ‖a n - b n‖) ?_ ?_ hupper
  · exact Filter.Eventually.of_forall fun n => norm_nonneg _
  · exact Filter.Eventually.of_forall fun n => by
      simpa only [dist_eq_norm] using hφ.dist_le_mul (a n) (b n)

/-- Vanishing pointwise perturbations are invisible to every Lipschitz
observable after Cesaro completion. -/
theorem tendsto_complexCesaroAverage_lipschitz_difference_zero
    {a b : ℕ → ℂ} (hab : Tendsto (fun n => a n - b n) atTop (𝓝 0))
    {K : NNReal} {φ : ℂ → ℂ} (hφ : LipschitzWith K φ) :
    Tendsto
      (fun N => complexCesaroAverage (fun n => φ (a n)) N -
        complexCesaroAverage (fun n => φ (b n)) N)
      atTop (𝓝 0) := by
  have hpoint := tendsto_lipschitz_difference_zero hab hφ
  have hcesaro := hpoint.cesaro_smul
  apply hcesaro.congr'
  filter_upwards with N
  simp only [complexCesaroAverage, Finset.sum_sub_distrib, smul_sub]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]

/-- Persistent peripheral carrier of a finite contraction, defined without
any nonzero-mass condition. -/
def finiteContractionPersistentReturnCarrier
    (T : H →L[ℂ] H) (x : H) (n : ℕ) : ℂ :=
  ∑ μ : FiniteContractionPeripheralEigenvalue T,
    ((‖finiteContractionPeripheralComponent T x μ‖ ^ 2 : ℝ) : ℂ) *
      ((μ : ℂ) ^ n)

omit [CompleteSpace H] in
/-- When persistent mass is positive, the unconditional carrier is exactly
mass times the normalized peripheral characteristic function. -/
theorem finiteContractionPersistentReturnCarrier_eq_peripheralCharFun
    (T : H →L[ℂ] H) (x : H)
    (hpersistent : 0 < finiteContractionPersistentMass T x) (n : ℕ) :
    finiteContractionPersistentReturnCarrier T x n =
      (finiteContractionPersistentMass T x : ℂ) *
        charFun (finiteContractionPeripheralObserverSpectrum T x) (n : ℝ) := by
  rw [finiteContractionPersistentReturnCarrier,
    finiteContraction_persistentSum_eq_scaledWeightedFloquet T x hpersistent,
    charFun_finiteContractionPeripheralObserverSpectrum T x hpersistent]

/-- Raw return amplitude differs from its persistent carrier by exactly the
transient amplitude, hence the difference tends to zero. -/
theorem finiteContraction_returnAmplitude_sub_persistentCarrier_tendsto_zero
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (x : H) :
    Tendsto
      (fun n : ℕ => inner ℂ x ((T ^ n) x) -
        finiteContractionPersistentReturnCarrier T x n)
      atTop (𝓝 0) := by
  have htransient := tendsto_finiteContractionTransientReturnAmplitude_zero T hT x
  apply htransient.congr'
  filter_upwards with n
  rw [finiteContraction_returnAmplitude_eq_persistent_sum_add_transient
    T hT x n]
  simp [finiteContractionPersistentReturnCarrier]

/-- **Persistent-selection law for every finite open evolution.** Every
Lipschitz observable of the raw return-amplitude history has the same
completed Cesaro law as the persistent peripheral carrier. No transient
subtraction is performed in the observable. -/
theorem finiteContraction_rawHistory_cesaroEquivalent_persistentCarrier
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (x : H)
    {K : NNReal} {φ : ℂ → ℂ} (hφ : LipschitzWith K φ) :
    Tendsto
      (fun N =>
        complexCesaroAverage
            (fun n : ℕ => φ (inner ℂ x ((T ^ n) x))) N -
          complexCesaroAverage
            (fun n : ℕ => φ
              (finiteContractionPersistentReturnCarrier T x n)) N)
      atTop (𝓝 0) := by
  exact tendsto_complexCesaroAverage_lipschitz_difference_zero
    (finiteContraction_returnAmplitude_sub_persistentCarrier_tendsto_zero
      T hT x) hφ

/-- Exact extinction criterion: the complete return history tends to zero
exactly when the state has no peripheral mass. -/
theorem finiteContraction_returnAmplitude_tendsto_zero_iff_persistentMass_zero
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (x : H) :
    Tendsto (fun n : ℕ => inner ℂ x ((T ^ n) x)) atTop (𝓝 0) ↔
      finiteContractionPersistentMass T x = 0 := by
  constructor
  · intro hzero
    by_contra hmass
    have hmassPos : 0 < finiteContractionPersistentMass T x :=
      lt_of_le_of_ne (finiteContractionPersistentMass_nonneg T x) (Ne.symm hmass)
    have hnorm :
        Tendsto (fun n : ℕ => ‖inner ℂ x ((T ^ n) x)‖) atTop (𝓝 0) := by
      simpa only [norm_zero] using hzero.norm
    obtain ⟨B, hB⟩ := Metric.tendsto_atTop.1 hnorm
      (finiteContractionPersistentMass T x / 4) (by positivity)
    have hceiling := finiteContraction_returnAmplitude_exactAsymptoticCeiling T hT x
    obtain ⟨n, hnB, hnLower⟩ := hceiling.2
      (finiteContractionPersistentMass T x / 2) (by positivity) B
    have hnUpper := hB n (Nat.le_of_lt hnB)
    have hnUpper' :
        ‖inner ℂ x ((T ^ n) x)‖ <
          finiteContractionPersistentMass T x / 4 := by
      simpa [dist_zero_right, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _)] using hnUpper
    linarith
  · intro hmass
    have hprojectionNorm :
        ‖(finiteContractionPeripheralSubspace T).starProjection x‖ ^ 2 = 0 := by
      rw [← finiteContractionPersistentMass_eq_norm_sq_projection T hT x]
      exact hmass
    have hprojection :
        (finiteContractionPeripheralSubspace T).starProjection x = 0 := by
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg
        ((finiteContractionPeripheralSubspace T).starProjection x)]
    have htransientComponent :
        (finiteContractionTransientComponent T x : H) = x := by
      change x -
        (finiteContractionPeripheralSubspace T).starProjection x = x
      rw [hprojection, sub_zero]
    have htransient :=
      tendsto_finiteContractionTransientReturnAmplitude_zero T hT x
    apply htransient.congr'
    filter_upwards with n
    rw [finiteContractionTransientReturnAmplitude, htransientComponent]

/-- Positive persistent mass identifies the raw completed history directly
with the normalized peripheral characteristic-function carrier for every
Lipschitz observable. -/
theorem finiteContraction_rawHistory_cesaroEquivalent_peripheralCharFun
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (x : H)
    (hpersistent : 0 < finiteContractionPersistentMass T x)
    {K : NNReal} {φ : ℂ → ℂ} (hφ : LipschitzWith K φ) :
    Tendsto
      (fun N =>
        complexCesaroAverage
            (fun n : ℕ => φ (inner ℂ x ((T ^ n) x))) N -
          complexCesaroAverage
            (fun n : ℕ => φ
              ((finiteContractionPersistentMass T x : ℂ) *
                charFun (finiteContractionPeripheralObserverSpectrum T x)
                  (n : ℝ))) N)
      atTop (𝓝 0) := by
  apply tendsto_complexCesaroAverage_lipschitz_difference_zero
    (b := fun n : ℕ =>
      (finiteContractionPersistentMass T x : ℂ) *
        charFun (finiteContractionPeripheralObserverSpectrum T x) (n : ℝ))
    _ hφ
  have hcarrier :=
    finiteContraction_returnAmplitude_sub_persistentCarrier_tendsto_zero T hT x
  apply hcarrier.congr'
  filter_upwards with n
  rw [finiteContractionPersistentReturnCarrier_eq_peripheralCharFun
    T x hpersistent n]

end RHTower
