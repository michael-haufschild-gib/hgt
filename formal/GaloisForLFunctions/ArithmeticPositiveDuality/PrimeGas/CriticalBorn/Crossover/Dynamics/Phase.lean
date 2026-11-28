import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Dynamics.Laws
import GaloisForLFunctions.HTGeometry.TorusFourierWeakConvergenceLaw

/-! # Clock response at inverse maximal energy -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Dynamics

open Real Filter MeasureTheory ProbabilityTheory
open GaloisForLFunctions.HTGeometry
open scoped Topology

/-- Phase read at relative clock displacement h and energy fraction y. -/
def clockPhase (h y : ℝ) := Complex.exp (((h*y:ℝ):ℂ)*Complex.I)

private def probe (h : ℝ) : C(unitInterval,ℂ) :=
  ⟨fun z => clockPhase h (decode z),
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
      (continuous_const.mul decode_continuous)).mul continuous_const)⟩

/-- Coherent mean of the scaled phase in the finite elementary packet. -/
def phaseAverage (a h : ℝ) (N : ℕ) :=
  ∫ z, probe h z ∂(codeLaw a N : Measure unitInterval)

theorem phaseAverage_eq (a h : ℝ) (N : ℕ) :
    phaseAverage a h N =
      (∑ p ∈ primes (cutoff N), (((p:ℝ)^(a-1):ℝ):ℂ)*clockPhase h (energyFraction N p))/
        (powerMass a N:ℂ) := by
  change (∫ z, probe h z ∂((labelLaw ((1-a)/2) N : Measure ℕ).map
    (fun p => code (energyFraction N p)))) = _
  rw [integral_map (measurable_of_countable _).aemeasurable (probe h).continuous.aestronglyMeasurable,
    label_expectation_complex]
  simp only [probe,ContinuousMap.coe_mk,decode_code]

/-- The two energy populations contribute phases 1 and exp(ih) to
the limiting clock response. -/
theorem phase_response (c h : ℝ) :
    Tendsto (fun N : ℕ => phaseAverage (drift c N/log N) h N) atTop
      (𝓝 (((Bulk.bulkWeight c:ℝ):ℂ)+(1-((Bulk.bulkWeight c:ℝ):ℂ))*clockPhase h 1)) := by
  have lim := (continuous_integral_complex_continuousMap (probe h)).continuousAt.tendsto.comp
    (code_law_limit c)
  change Tendsto _ _ (𝓝 (∫ z, probe h z ∂bernoulliMeasure (code 0) (code 1) (Bulk.bulkWeight c))) at lim
  rw [integral_bernoulliMeasure] at lim
  have lo : probe h (code 0)=1 := by
    change clockPhase h (decode (code 0))=1
    rw [decode_code]
    simp [clockPhase]
  have hi : probe h (code 1)=clockPhase h 1 := congrArg (clockPhase h) (decode_code 1)
  simpa only [Function.comp_def,phaseAverage,lo,hi,Complex.real_smul,Complex.ofReal_sub,Complex.ofReal_one,mul_one] using lim

#print axioms phaseAverage_eq
#print axioms phase_response

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Dynamics
