import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Ordinary.Dilution
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Ordinary.Variation
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Energy.Hamiltonian

/-! # The ordinary bosonic energy measurement in the transition window -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Ordinary

open Filter Finset Real MeasureTheory Crossover
open GaloisForLFunctions.HTGeometry
open scoped Topology

private theorem index_value (a t : ℝ) : 1-2*(indexParameter a t).re=a := by
  simp only [indexParameter,Complex.add_re,Complex.ofReal_re,Complex.mul_I_re,Complex.ofReal_im]
  ring

private theorem weight_on {m : ℕ} (a t x : ℝ) {n : ℕ+} (hn : n∈shells m x) :
    ‖wave m (indexParameter a t) x n‖^2=exp ((a-1)*energy n) := by
  rw [wave_apply,if_pos hn,heat_square,index_value]

private theorem total (m : ℕ) (a t x : ℝ) :
    (∑ n ∈ shells m x, ‖wave m (indexParameter a t) x n‖^2)=mass m a x :=
  sum_congr rfl fun _ hn => weight_on a t x hn

/-- Read the actual integer energy from the one-amplitude-per-label state. -/
def energyLaw (m : ℕ) (a t : ℝ) (N : ℕ) : ProbabilityMeasure ℝ :=
  let S := shells m N
  let w := fun n => ‖wave m (indexParameter a t) N n‖^2
  let read := fun n => energy n/log N
  ⟨normalizedFiniteRealAtomicMeasure S read w,
    isProbabilityMeasure_normalizedFiniteRealAtomicMeasure S read w (fun _ _ => sq_nonneg _)
      (by change 0 < ∑ n ∈ shells m N, ‖wave m (indexParameter a t) N n‖^2
          rw [total]; exact mass_pos _ _ _)⟩

theorem energy_expectation (m : ℕ) (a t : ℝ) (N : ℕ) (f : ℝ → ℝ) :
    (∫ y,f y ∂(energyLaw m a t N : Measure ℝ)) =
      ∑ n ∈ shells m N, plainWeight m a N n*f (energy n/log N) := by
  have hp : 0 < ∑ n ∈ shells m N, ‖wave m (indexParameter a t) N n‖^2 := by
    rw [total]; exact mass_pos _ _ _
  change (∫ y,f y ∂(normalizedFiniteRealAtomicMeasure (shells m N)
    (fun n => energy n/log N) (fun n => ‖wave m (indexParameter a t) N n‖^2) : Measure ℝ))=_
  rw [integral_normalizedFiniteRealAtomicMeasure _ _ _ (fun _ _ => sq_nonneg _) hp,total,sum_div]
  refine sum_congr rfl fun n hn => ?_
  rw [weight_on a t _ hn,plainWeight]
  ring

private theorem ordered_expectation (m : ℕ) (a t : ℝ) (N : ℕ) (f : ℝ → ℝ) :
    (∫ y,f y ∂(Energy.energyLaw m a t N : Measure ℝ)) =
      ∑ n ∈ shells m N, orderedWeight m a N n*f (energy n/log N) := by
  rw [Energy.energyLaw,Energy.expectation,Composite.wave_mass,rawWave_sq,index_value,sum_div]
  refine sum_congr rfl fun n _ => ?_
  rw [Composite.wave_apply,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    sq_sqrt (Nat.cast_nonneg _),heat_square,index_value,orderedWeight]
  ring

/-- The limiting Hamiltonian law is unchanged when every distinct bosonic
occupation receives one heat amplitude, with arbitrary moving clock times. -/
theorem energy_limit (m : ℕ) (c : ℝ) (t : ℕ → ℝ) :
    Tendsto (fun N : ℕ => energyLaw m (drift c N/log N) (t N) N) atTop
      (𝓝 (Energy.binRead m (Bulk.bulkWeight c) (fun j : ℕ => (j:ℝ)))) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  let plain N := ∫ y,f y ∂(energyLaw m (drift c N/log N) (t N) N : Measure ℝ)
  let ord N := ∫ y,f y ∂(Energy.energyLaw m (drift c N/log N) (t N) N : Measure ℝ)
  have e := excess_limit m c
  have hi := ((e.div (e.const_add 1) (by norm_num)).const_mul 2).const_mul ‖f‖
  rw [zero_div,mul_zero,mul_zero] at hi
  have diff : Tendsto (fun N => plain N-ord N) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hi (fun _ => norm_nonneg _) _
    intro N
    change |plain N-ord N| ≤ _
    dsimp only [plain,ord]
    rw [energy_expectation,ordered_expectation]
    exact test_difference m _ _ (fun n => f (energy n/log N)) (norm_nonneg f)
      (fun _ _ => f.norm_coe_le_norm _)
  have h := diff.add (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp (Energy.energy_limit m c t) f)
  rw [zero_add] at h
  exact h.congr fun N => show plain N-ord N+ord N=plain N from sub_add_cancel _ _

#print axioms energy_expectation
#print axioms energy_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Ordinary
