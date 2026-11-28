import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Gram
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Dynamics.Measurement
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.EqualTime

/-! # Hamiltonian readings in the original composite gas state -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Energy

open Finset Real MeasureTheory
open Crossover Crossover.Dynamics
open GaloisForLFunctions.HTGeometry

/-- Energy of a product shell equals the sum of its elementary energies. -/
theorem energy_product {m : ℕ} {x : ℝ} (q : Fin m → PrimeAt x) :
    energy (productLabel q)=∑ i, energy (primeLabel (q i)) := by
  have h (S : Finset (Fin m)) : energy (∏ i ∈ S, primeLabel (q i)) =
      ∑ i ∈ S, energy (primeLabel (q i)) := by
    induction S using Finset.induction_on with
    | empty => simp [energy]
    | insert a S ha ih => rw [prod_insert ha,sum_insert ha,energy_mul,ih]
  exact h univ

/-- Every occupied shell at cutoff N lies between zero and m times
the maximum elementary energy. -/
theorem energy_bounds {m N : ℕ} (hN : 2≤N) {n : ℕ+} (hn : n∈shells m N) :
    0≤energy n/log N ∧ energy n/log N ≤ m := by
  obtain ⟨q,_,rfl⟩ := mem_image.mp hn
  have resolved (i : Fin m) : energy (primeLabel (q i))/log N=(energyFraction N (q i).val:ℝ) :=
    (energyFraction_on_prime hN (q i).property).symm
  rw [energy_product,sum_div]
  simp only [resolved]
  refine ⟨sum_nonneg fun i _ => (energyFraction N (q i).val).property.1,?_⟩
  calc
    _ ≤ ∑ _ : Fin m, (1:ℝ) := sum_le_sum fun i _ => (energyFraction N (q i).val).property.2
    _ = _ := by simp

/-- A positive bounded reading of the total scaled energy. -/
def code (m N : ℕ) (n : ℕ+) : unitInterval :=
  ⟨exp (min 0 (energy n/log N-(m:ℝ))),(exp_pos _).le,exp_le_one_iff.mpr (min_le_left _ _)⟩

theorem code_on_shell {m N : ℕ} (hN : 2≤N) {n : ℕ+} (hn : n∈shells m N) :
    (code m N n:ℝ)=exp (energy n/log N-(m:ℝ)) := by
  change exp (min 0 _)=_
  rw [min_eq_right (sub_nonpos.mpr (energy_bounds hN hn).2)]

private theorem mass_pos (m : ℕ) (s : ℂ) (x : ℝ) :
    0<∑ n ∈ shells m x, ‖wave m s x n‖^2 := by
  rw [←norm_shell_sum,wave_mass,rawWave_sq]
  exact pow_pos (powerMass_pos _ _) _

/-- Probability law of a shell observable, using the actual gas wave coefficients. -/
def observation {A : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]
    (m : ℕ) (s : ℂ) (x : ℝ) (read : ℕ+ → A) : ProbabilityMeasure A :=
  ⟨normalizedFiniteRealAtomicMeasure (shells m x) read (fun n => ‖wave m s x n‖^2),
    isProbabilityMeasure_normalizedFiniteRealAtomicMeasure _ _ _ (fun _ _ => sq_nonneg _) (mass_pos m s x)⟩

theorem expectation {A : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]
    (m : ℕ) (s : ℂ) (x : ℝ) (read : ℕ+ → A) (f : A → ℝ) :
    (∫ y,f y ∂(observation m s x read : Measure A)) =
      (∑ n ∈ shells m x, ‖wave m s x n‖^2 * f (read n))/‖wave m s x‖^2 := by
  rw [norm_shell_sum]
  exact integral_normalizedFiniteRealAtomicMeasure _ _ _ (fun _ _ => sq_nonneg _) (mass_pos m s x) f

def codedLaw (m : ℕ) (a t : ℝ) (N : ℕ) := observation m (indexParameter a t) N (code m N)

#print axioms energy_product
#print axioms energy_bounds
#print axioms code_on_shell
#print axioms expectation

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Energy
