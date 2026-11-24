import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Readings
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.Complex.Circle

/-! # Born probability on the composition phase circle -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open MeasureTheory Filter Topology
open scoped ENNReal

/-- The unitary composition phase of one occupied energy shell. -/
def occupationPhase (t : ℝ) (n : ℕ+) : Circle :=
  ⟨splitPhase t n,mem_sphere_zero_iff_norm.mpr (splitPhase_norm t n)⟩

/-- The phase distribution measured in a split pair, including coincident eigenphases with their full mass. -/
def occupationPhaseLaw (v : MissingWave) (t : ℝ) : ProbabilityMeasure Circle :=
  ⟨Measure.sum (fun n => ENNReal.ofReal (occupationProbability v n) • Measure.dirac (occupationPhase t n)),⟨by
    rw [Measure.sum_apply _ MeasurableSet.univ]
    simp only [Measure.smul_apply,Measure.dirac_apply_of_mem (Set.mem_univ _),smul_eq_mul,mul_one,
      ← ENNReal.ofReal_tsum_of_nonneg (occupationLaw_nonneg v) (occupationLaw_hasSum v).summable,
      (occupationLaw_hasSum v).tsum_eq,ENNReal.ofReal_one]⟩⟩

theorem phaseObservable_hasSum (v : MissingWave) (t : ℝ) (f : C(Circle,ℂ)) :
    HasSum (fun n => (occupationProbability v n:ℂ)*f (occupationPhase t n))
      (∫ z, f z ∂(occupationPhaseLaw v t : Measure Circle)) := by
  have hi := f.continuous.integrable_of_hasCompactSupport (μ := (occupationPhaseLaw v t : Measure Circle))
    (HasCompactSupport.of_compactSpace _)
  change Integrable _ (Measure.sum (fun n => ENNReal.ofReal (occupationProbability v n) •
    Measure.dirac (occupationPhase t n))) at hi
  apply (hasSum_integral_measure hi).congr_fun
  intro n
  rw [integral_smul_measure,integral_dirac,ENNReal.toReal_ofReal (occupationLaw_nonneg v n),Complex.real_smul]

/-- The positive moments of the physical probability measure are the clock readings. -/
theorem occupationPhaseLaw_moment (v : MissingWave) (t : ℝ) (k : ℕ) :
    (∫ z : Circle, (z:ℂ)^k ∂(occupationPhaseLaw v t : Measure Circle)) = harmonicReading v t k :=
  (phaseObservable_hasSum v t ⟨fun z : Circle => (z:ℂ)^k,continuous_subtype_val.pow k⟩).unique
    (harmonicTerms_hasSum v t k)

theorem occupationPhase_limit {t : ℕ → ℝ} (ht : Tendsto t atTop (𝓝 0)) (n : ℕ+) :
    Tendsto (fun j => occupationPhase (t j) n) atTop (𝓝 1) := by
  apply tendsto_subtype_rng.mpr
  exact clockPhase_limit ht n

#print axioms phaseObservable_hasSum
#print axioms occupationPhaseLaw_moment
#print axioms occupationPhase_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
