import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Edges
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Transition

/-! # Reading the fraction of the maximal elementary energy -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Dynamics

open Real Finset MeasureTheory Set
open GaloisForLFunctions.HTGeometry

/-- Compact reading of the energy in units of the largest allowed energy. -/
def energyFraction (N p : ℕ) : unitInterval :=
  let y := log p/log N
  ⟨max 0 (min 1 y),le_max_left _ _,max_le zero_le_one (min_le_left _ _)⟩

theorem energyFraction_on_prime {N p : ℕ} (hN : 2≤N) (hp : p∈primes (cutoff N)) :
    (energyFraction N p:ℝ)=log p/log N := by
  obtain ⟨pr,le⟩ := (mem_cutoff (by exact_mod_cast hN : (2:ℝ)≤N)).mp hp
  have ln := log_pos (show (1:ℝ)<N by exact_mod_cast (by omega : 1<N))
  have lp := log_pos (show (1:ℝ)<p by exact_mod_cast pr.one_lt)
  have lo := div_nonneg lp.le ln.le
  have hi := (div_le_one ln).mpr (log_le_log (Nat.cast_pos.mpr pr.pos) le)
  exact (congrArg (max 0) (min_eq_right hi)).trans (max_eq_right lo)

/-- The exponential reading maps the unit energy interval onto [exp(−1),1]. -/
def code (y : unitInterval) : unitInterval :=
  ⟨exp ((y:ℝ)-1),(exp_pos _).le,exp_le_one_iff.mpr (sub_nonpos.mpr y.property.2)⟩

/-- Born law of the exponential reading, sampled from the elementary heat state. -/
def codeLaw (a : ℝ) (N : ℕ) : ProbabilityMeasure unitInterval :=
  (labelLaw ((1-a)/2) N).map
    (show Measurable (fun p => code (energyFraction N p)) from measurable_of_countable _).aemeasurable

private theorem index_weight (a : ℝ) : bornWeight ((1-a)/2) = fun p => (p:ℝ)^(a-1) := by
  funext p
  rw [bornWeight,show -(2*((1-a)/2))=a-1 by ring]

/-- Integrating a real observable of the label gives its weighted prime sum. -/
theorem label_expectation (a x : ℝ) (f : ℕ → ℝ) :
    (∫ p, f p ∂(labelLaw ((1-a)/2) x : Measure ℕ)) =
      (∑ p ∈ primes (cutoff x), (p:ℝ)^(a-1)*f p)/powerMass a x := by
  change (∫ p, f p ∂(normalizedFiniteRealAtomicMeasure (primes (cutoff x))
    id (bornWeight ((1-a)/2)) : Measure ℕ)) = _
  rw [index_weight]
  exact integral_normalizedFiniteRealAtomicMeasure _ id _ (fun p _ => rpow_nonneg (Nat.cast_nonneg p) _)
    (powerMass_pos a x) f

/-- Complex phase probes use the same normalized elementary weights. -/
theorem label_expectation_complex (a x : ℝ) (f : ℕ → ℂ) :
    (∫ p, f p ∂(labelLaw ((1-a)/2) x : Measure ℕ)) =
      (∑ p ∈ primes (cutoff x), (((p:ℝ)^(a-1):ℝ):ℂ)*f p)/(powerMass a x:ℂ) := by
  change (∫ p, f p ∂(normalizedFiniteRealAtomicMeasure (primes (cutoff x))
    id (bornWeight ((1-a)/2)) : Measure ℕ)) = _
  rw [index_weight]
  change (∫ p, f p ∂(∑ p ∈ primes (cutoff x),
    (Real.toNNReal ((p:ℝ)^(a-1)/powerMass a x)) • Measure.dirac p)) = _
  rw [integral_finsetSum_measure (fun i _ => (integrable_dirac (by finiteness)).smul_measure_nnreal),
    Finset.sum_div]
  refine sum_congr rfl fun p _ => ?_
  rw [integral_smul_nnreal_measure,integral_dirac]
  change ((Real.toNNReal ((p:ℝ)^(a-1)/powerMass a x):ℝ):ℂ)*f p=_
  rw [Real.coe_toNNReal _ (div_nonneg (rpow_nonneg (Nat.cast_nonneg p) _) (powerMass_pos a x).le),
    Complex.ofReal_div]
  ring

/-- A moment of the coded energy shifts the tilt by an integer in units of
the inverse maximal energy. -/
theorem code_moment (a : ℝ) {N : ℕ} (hN : 2≤N) (k : ℕ) :
    (∫ y, (y:ℝ)^k ∂(codeLaw a N : Measure unitInterval)) =
      exp (-(k:ℝ))*powerMass (a+k/log N) N/powerMass a N := by
  change (∫ y : unitInterval, (y:ℝ)^k ∂((labelLaw ((1-a)/2) N : Measure ℕ).map
    (fun p => code (energyFraction N p)))) = _
  rw [integral_map (measurable_of_countable _).aemeasurable
    ((measurable_subtype_coe.pow_const k).aestronglyMeasurable),label_expectation]
  congr 1
  rw [powerMass,Finset.mul_sum]
  refine sum_congr rfl fun p hp => ?_
  have pp : 0<(p:ℝ) := Nat.cast_pos.mpr (Nat.mem_primesBelow.mp hp).2.pos
  change (p:ℝ)^(a-1)*(exp ((energyFraction N p:ℝ)-1))^k = _
  rw [energyFraction_on_prime hN hp,←exp_nat_mul,rpow_def_of_pos pp,rpow_def_of_pos pp,
    ←exp_add,←exp_add]
  congr 1
  ring

#print axioms energyFraction_on_prime
#print axioms label_expectation
#print axioms label_expectation_complex
#print axioms code_moment

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Dynamics
