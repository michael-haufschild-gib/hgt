import GaloisForLFunctions.RHTower.ObserverTimeGapMeasureLaw
import GaloisForLFunctions.HTGeometry.EnergyGapCocycleLaw

/-!
# Finite atomic observer-time gap law

For a finite observer spectrum, the abstract observer-time gap measure is
exactly the weighted atomic measure on every ordered energy difference.  This
is the bridge from controlled eigenvalue branches to the measure that
classifies the complete projective return record.
-/

open MeasureTheory

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Finite observer spectrum with prescribed real weights and energies. -/
def finiteAtomicObserverSpectrum
    {I : Type*} [Fintype I]
    (weight energy : I → ℝ) : Measure ℝ :=
  Measure.sum fun i =>
    ENNReal.ofReal (weight i) • Measure.dirac (energy i)

/-- Nonnegative weights summing to one make the finite atomic spectrum a
probability measure. -/
theorem finiteAtomicObserverSpectrum_isProbabilityMeasure
    {I : Type*} [Fintype I]
    (weight energy : I → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hsum : ∑ i, weight i = 1) :
    IsProbabilityMeasure
      (finiteAtomicObserverSpectrum weight energy) := by
  unfold finiteAtomicObserverSpectrum
  apply HasSum.isProbabilityMeasure_sum_dirac hweight
  simpa [hsum] using (hasSum_fintype weight)

/-- Explicit ordered-pair energy-gap measure of a finite spectrum. -/
def finiteAtomicObserverGapMeasure
    {I : Type*} [Fintype I]
    (weight energy : I → ℝ) : Measure ℝ :=
  Measure.sum fun p : I × I =>
    (ENNReal.ofReal (weight p.1) *
        ENNReal.ofReal (weight p.2)) •
      Measure.dirac (energyGapCocycle energy p.1 p.2)

/-- **Finite atomic bridge.**  Taking two independent samples from a finite
observer spectrum and subtracting them gives exactly the double Dirac family
on all ordered energy gaps. -/
theorem observerTimeGapMeasure_finiteAtomicObserverSpectrum
    {I : Type*} [Fintype I]
    (weight energy : I → ℝ) :
    observerTimeGapMeasure
        (finiteAtomicObserverSpectrum weight energy) =
      finiteAtomicObserverGapMeasure weight energy := by
  unfold observerTimeGapMeasure spectralDifferenceMeasure
  unfold finiteAtomicObserverSpectrum finiteAtomicObserverGapMeasure
  rw [Measure.prod_sum]
  rw [Measure.map_sum (by fun_prop)]
  congr
  funext p
  rw [Measure.prod_smul_left, Measure.prod_smul_right,
    Measure.dirac_prod_dirac]
  rw [Measure.map_smul, Measure.map_smul, Measure.map_dirac]
  simp only [smul_smul, energyGapCocycle]

/-- Characteristic function of a finite nonnegative atomic spectrum. -/
theorem charFun_finiteAtomicObserverSpectrum
    {I : Type*} [Fintype I]
    (weight energy : I → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (t : ℝ) :
    charFun (finiteAtomicObserverSpectrum weight energy) t =
      ∑ i, (weight i : ℂ) *
        Complex.exp ((t * energy i : ℝ) * Complex.I) := by
  rw [charFun_apply_real, finiteAtomicObserverSpectrum]
  rw [integral_sum_dirac (by simp), tsum_fintype]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ENNReal.toReal_ofReal (hweight i)]
  congr 2
  push_cast
  ring

/-- **Finite return-cocycle law.** The complete projective return record of
a finite observer is exactly the Fourier transform of its weighted
energy-gap cocycle. -/
theorem projectiveReturnRecord_finiteAtomicObserverSpectrum
    {I : Type*} [Fintype I]
    (weight energy : I → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hsum : ∑ i, weight i = 1)
    (t : ℝ) :
    (projectiveReturnRecord
        (finiteAtomicObserverSpectrum weight energy) t : ℂ) =
      ∑ p : I × I,
        ((weight p.1 * weight p.2 : ℝ) : ℂ) *
          Complex.exp
            ((t * energyGapCocycle energy p.1 p.2 : ℝ) *
              Complex.I) := by
  letI : IsProbabilityMeasure
      (finiteAtomicObserverSpectrum weight energy) :=
    finiteAtomicObserverSpectrum_isProbabilityMeasure
      weight energy hweight hsum
  rw [← charFun_observerTimeGapMeasure]
  rw [observerTimeGapMeasure_finiteAtomicObserverSpectrum]
  rw [charFun_apply_real, finiteAtomicObserverGapMeasure]
  rw [integral_sum_dirac
    (by
      intro p
      exact ENNReal.mul_ne_top
        ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
    tsum_fintype]
  apply Finset.sum_congr rfl
  intro p hp
  rw [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (hweight p.1),
    ENNReal.toReal_ofReal (hweight p.2)]
  congr 2
  push_cast
  ring

end RHTower
