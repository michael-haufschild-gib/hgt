import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Energy.Binomial

/-! # The limiting binomial Hamiltonian on actual multiplicative shells -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Energy

open Filter Finset Real MeasureTheory
open Crossover
open scoped Topology

private def decode (m : ℕ) (z : unitInterval) :=
  (m:ℝ)+log (max (exp (-(m:ℝ))) (z:ℝ))

private theorem decode_cont (m : ℕ) : Continuous (decode m) :=
  continuous_const.add ((continuous_const.max continuous_subtype_val).log
    (fun _ => ((exp_pos _).trans_le (le_max_left _ _)).ne'))

private theorem decode_shell {m N : ℕ} (hN : 2≤N) {n : ℕ+} (hn : n∈shells m N) :
    decode m (code m N n)=energy n/log N := by
  have lower : -(m:ℝ)≤energy n/log N-m := by linarith only [(energy_bounds hN hn).1]
  rw [decode,code_on_shell hN hn,max_eq_right (exp_le_exp.mpr lower),log_exp]
  ring

private theorem decode_level {m j : ℕ} (hj : j ≤ m) : decode m (binCode m j)=(j:ℝ) := by
  change (m:ℝ)+log (max (exp (-(m:ℝ))) (exp (-((m-j:ℕ):ℝ))))=_
  rw [Nat.cast_sub hj,max_eq_right (exp_le_exp.mpr (by linarith only [(Nat.cast_nonneg j : 0≤(j:ℝ))])),log_exp]
  ring

/-- Born law of the Hamiltonian log n / log N in the positive-integer gas basis. -/
def energyLaw (m : ℕ) (a t : ℝ) (N : ℕ) :=
  observation m (indexParameter a t) N (fun n => energy n/log N)

private theorem decoded_law (m : ℕ) (a t : ℝ) {N : ℕ} (hN : 2≤N) :
    (codedLaw m a t N).map (decode_cont m).measurable.aemeasurable = energyLaw m a t N := by
  apply ProbabilityMeasure.toMeasure_injective
  refine MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [ProbabilityMeasure.toMeasure_map,integral_map (decode_cont m).measurable.aemeasurable
    f.continuous.aestronglyMeasurable,codedLaw,energyLaw,expectation,expectation]
  apply congrArg (fun u : ℝ => u/‖wave m (indexParameter a t) N‖^2)
  exact sum_congr rfl fun n hn => by rw [decode_shell hN hn]

private theorem decoded_bin (m : ℕ) (r : unitInterval) :
    (binRead m r (binCode m)).map (decode_cont m).measurable.aemeasurable =
      binRead m r (fun j : ℕ => (j:ℝ)) := by
  apply ProbabilityMeasure.toMeasure_injective
  refine MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [ProbabilityMeasure.toMeasure_map,integral_map (decode_cont m).measurable.aemeasurable
    f.continuous.aestronglyMeasurable,bin_expectation,bin_expectation]
  exact sum_congr rfl fun j hj => by rw [decode_level (Nat.le_of_lt_succ (mem_range.mp hj))]

/-- The measured total energy converges weakly to a binomial law on
levels 0,...,m. Both the vacuum and coincident elementary labels are included. -/
theorem energy_limit (m : ℕ) (c : ℝ) (t : ℕ → ℝ) :
    Tendsto (fun N : ℕ => energyLaw m (drift c N/log N) (t N) N) atTop
      (𝓝 (binRead m (Bulk.bulkWeight c) (fun j : ℕ => (j:ℝ)))) := by
  have h := (ProbabilityMeasure.continuous_map (decode_cont m)).continuousAt.tendsto.comp (coded_limit m c t)
  rw [decoded_bin] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact decoded_law m _ _ hN

#print axioms energy_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Energy
