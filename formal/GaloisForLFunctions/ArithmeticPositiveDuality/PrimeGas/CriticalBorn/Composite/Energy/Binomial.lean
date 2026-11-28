import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Energy.Moments
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Occupation.Limit

/-! # Compact binomial limit of the composite energy reading -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Energy

open Finset Filter Real MeasureTheory
open Crossover
open ExactSubsystems.ThermalShells.Packets.Occupation
open GaloisForLFunctions.HTGeometry
open scoped Topology

private theorem bin_nonneg (m j : ℕ) (r : unitInterval) : 0≤bin m j (1-(r:ℝ)) := by
  rw [bin,show 1-(1-(r:ℝ))=(r:ℝ) by ring]
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (sub_nonneg.mpr r.property.2) _))
    (pow_nonneg r.property.1 _)

private theorem sum_one (m : ℕ) (r : unitInterval) :
    (∑ j ∈ range (m+1), bin m j (1-(r:ℝ)))=1 := bin_sum m _

/-- The binomial energy law read through any observable of the terminal count. -/
def binRead {A : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]
    (m : ℕ) (r : unitInterval) (read : ℕ → A) : ProbabilityMeasure A :=
  ⟨normalizedFiniteRealAtomicMeasure (range (m+1)) read (fun j => bin m j (1-(r:ℝ))),
    isProbabilityMeasure_normalizedFiniteRealAtomicMeasure _ _ _ (fun j _ => bin_nonneg m j r)
      (by rw [sum_one]; exact zero_lt_one)⟩

theorem bin_expectation {A : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]
    (m : ℕ) (r : unitInterval) (read : ℕ → A) (f : A → ℝ) :
    (∫ z, f z ∂(binRead m r read : Measure A)) = ∑ j ∈ range (m+1), bin m j (1-(r:ℝ))*f (read j) := by
  change (∫ z, f z ∂(normalizedFiniteRealAtomicMeasure (range (m+1)) read
    (fun j => bin m j (1-(r:ℝ))) : Measure A)) = _
  rw [integral_normalizedFiniteRealAtomicMeasure _ _ _ (fun j _ => bin_nonneg m j r)
    (by rw [sum_one]; exact zero_lt_one),sum_one,div_one]

/-- Coded Hamiltonian level of j terminal excitations among m particles. -/
def binCode (m j : ℕ) : unitInterval :=
  ⟨exp (-((m-j:ℕ):ℝ)),(exp_pos _).le,exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg _))⟩

private theorem bin_moment (m : ℕ) (r : unitInterval) (k : ℕ) :
    (∫ q, (q:ℝ)^k ∂(binRead m r (binCode m) : Measure unitInterval)) =
      ((r:ℝ)*exp (-(k:ℝ))+(1-(r:ℝ)))^m := by
  rw [bin_expectation,add_comm ((r:ℝ)*_) _,add_pow]
  refine sum_congr rfl fun j _ => ?_
  change bin m j (1-(r:ℝ))*(exp (-((m-j:ℕ):ℝ)))^k=_
  rw [bin,show 1-(1-(r:ℝ))=(r:ℝ) by ring,mul_pow,←exp_nat_mul,←exp_nat_mul]
  rw [show (k:ℝ)*(-((m-j:ℕ):ℝ))=((m-j:ℕ):ℝ)*(-(k:ℝ)) by ring]
  ring

/-- The compact coded observations converge weakly, including every
atomic energy level and the vacuum. -/
theorem coded_limit (m : ℕ) (c : ℝ) (t : ℕ → ℝ) :
    Tendsto (fun N : ℕ => codedLaw m (drift c N/log N) (t N) N) atTop
      (𝓝 (binRead m (Bulk.bulkWeight c) (binCode m))) := by
  apply probabilityMeasure_tendsto_of_integral_pow_tendsto
  intro k
  rw [bin_moment]
  exact moment_limit m c t k

#print axioms bin_expectation
#print axioms coded_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Energy
