import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Fourier
import GaloisForLFunctions.HTGeometry.FiniteRealAtomicMeasure
import GaloisForLFunctions.HTGeometry.BernsteinSzegoProbabilityApproximation
import GaloisForLFunctions.HTGeometry.SummableCircleFourierDensity

/-! # Weak Haar limit of harmonic prime phases -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn

open Finset Filter MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped Topology

/-- Probability law of a measurement on the finite elementary ensemble. -/
def packetLaw {A : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]
    (x : ℕ → A) (N : ℕ) : ProbabilityMeasure A :=
  ⟨(normalizedFiniteRealAtomicMeasure (primes N) x weight : Measure A),
    isProbabilityMeasure_normalizedFiniteRealAtomicMeasure _ _ _ (fun p _ => weight_nonneg p)
      (mass_pos N)⟩

def phaseLaw (t : ℝ) := packetLaw (phase t)

def uniform : ProbabilityMeasure Circle := ⟨circleLebesgue,inferInstance⟩

theorem expectation (t : ℝ) (N : ℕ) (f : Circle → ℝ) :
    (∫ z, f z ∂(phaseLaw t N : Measure Circle)) =
      (∑ p ∈ primes N, weight p * f (phase t p)) / mass N :=
  integral_normalizedFiniteRealAtomicMeasure _ _ _ (fun p _ => weight_nonneg p) (mass_pos N) f

/-- Integration against the finite elementary packet is the normalized
weighted sum, including for complex-valued measurements. -/
theorem packet_integral {A : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]
    (x : ℕ → A) (N : ℕ) (f : A → ℂ) :
    (∫ z, f z ∂(packetLaw x N : Measure A)) =
      (∑ p ∈ primes N, (weight p : ℂ)*f (x p))/(mass N : ℂ) := by
  change (∫ z, f z ∂(∑ p ∈ primes N,
    (Real.toNNReal (weight p/mass N)) • Measure.dirac (x p))) = _
  rw [integral_finsetSum_measure (by
    intro i _
    exact (integrable_dirac (by finiteness)).smul_measure_nnreal)]
  rw [Finset.sum_div]
  apply sum_congr rfl
  intro p _
  rw [integral_smul_nnreal_measure,integral_dirac]
  change ((Real.toNNReal (weight p/mass N) : ℝ) : ℂ)*f (x p)=_
  rw [Real.coe_toNNReal _ (div_nonneg (weight_nonneg p) (mass_pos N).le),Complex.ofReal_div]
  ring

theorem moment (t : ℝ) (N : ℕ) (k : ℤ) :
    circleMeasureMomentZ (phaseLaw t N : Measure Circle) k = coefficient t k N :=
  packet_integral (phase t) N (fun z => (z : ℂ)^(-k))

/-- Nonzero physical height yields equidistribution on the entire circle. -/
theorem phase_limit (t : ℝ) (ht : t≠0) :
    Tendsto (phaseLaw t) atTop (𝓝 uniform) := by
  rw [isClosedEmbedding_completeCircleMomentSequence.isEmbedding.tendsto_nhds_iff,tendsto_pi_nhds]
  intro k
  change Tendsto (fun N => circleMeasureMomentZ (phaseLaw t N : Measure Circle) k) atTop
    (𝓝 (circleMeasureMomentZ circleLebesgue k))
  have haar : circleMeasureMomentZ circleLebesgue k = (if k=0 then 1 else 0) := by
    simp only [circleMeasureMomentZ,integral_circleLebesgue_coe_zpow,neg_eq_zero]
  rw [haar]
  simp only [moment]
  by_cases h : k=0
  · subst k; simp only [zero_mode,if_true]; exact tendsto_const_nhds
  · simpa only [if_neg h] using nonzero_mode t ht k h

/-- At zero height the finite ensemble is already concentrated at the real unit. -/
theorem zero_height (N : ℕ) : phaseLaw 0 N = ⟨Measure.dirac 1,inferInstance⟩ := by
  apply ProbabilityMeasure.toMeasure_injective
  apply circle_measure_eq_of_forall_zpow_integral_eq
  intro k
  have hm := moment 0 N (-k)
  rw [circleMeasureMomentZ,neg_neg] at hm
  change (∫ z : Circle, (z : ℂ)^k ∂(phaseLaw 0 N : Measure Circle)) =
    ∫ z : Circle, (z : ℂ)^k ∂Measure.dirac (1 : Circle)
  rw [hm,zero_height_coefficient,integral_dirac,Circle.coe_one,one_zpow]

#print axioms expectation
#print axioms packet_integral
#print axioms moment
#print axioms phase_limit
#print axioms zero_height

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn
