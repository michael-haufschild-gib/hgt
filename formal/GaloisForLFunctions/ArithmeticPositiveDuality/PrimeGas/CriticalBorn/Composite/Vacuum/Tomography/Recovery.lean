import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.Tomography.Extraction

/-! # What a repeated binary vacuum measurement can distinguish -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.Tomography

open Finset Filter InverseSpectrum.ShellMixing
open scoped Topology

/-- Agreement of all binary readings identifies every integer population.
The phases of both clocks may vary independently with depth. -/
theorem readings_iff (z t : ℕ → SplitParameter) (f g : Gas) :
    (∀ j, survival z f j = survival t g j) ↔ ∀ n : ℕ+, ‖f n‖^2 = ‖g n‖^2 := by
  constructor
  · intro same
    have levels (k : ℕ) : population f k = population g k := by
      induction k using Nat.strong_induction_on with
      | h k ih =>
        have agree (j : ℕ) : estimate z f k j = estimate t g k j := by
          rw [estimate,estimate,same]
          congr 2
          exact sum_congr rfl fun i hi => congrArg (occupationWeight i^j * ·) (ih i (mem_range.mp hi))
        exact tendsto_nhds_unique ((estimate_limit z f k).congr agree) (estimate_limit t g k)
    intro n
    obtain ⟨k,rfl⟩ := number_surjective n
    exact levels k
  · intro same j
    rw [survival_moment,survival_moment]
    exact tsum_congr fun k => congrArg (occupationWeight k^j * ·) (same (number k))

private theorem single_mass (r k : ℕ) :
    population (lp.single 2 (number r) (1:ℂ)) k = if k=r then 1 else 0 := by
  by_cases h : k=r
  · subst k
    simp [population,lp.single_apply]
  · have ne : number k ≠ number r := fun e => h (number_injective e)
    simp [population,lp.single_apply,Pi.single_eq_of_ne ne,h]

/-- A unit input on the next integer attains the geometric error at every depth. -/
theorem exact_error_on_next (z : ℕ → SplitParameter) (k j : ℕ) :
    estimate z (lp.single 2 (number (k+1)) (1:ℂ)) k j = ratio k^j := by
  have eqn := error_eq z (lp.single 2 (number (k+1)) (1:ℂ)) k j
  rw [single_mass,if_neg (Nat.ne_of_lt (Nat.lt_succ_self k)),sub_zero] at eqn
  rw [eqn,tsum_eq_single 0]
  · rw [zero_add,single_mass,if_pos rfl,mul_one]
    rfl
  · intro i hi
    rw [single_mass,if_neg (show i+(k+1)≠k+1 by omega),mul_zero]

#print axioms readings_iff
#print axioms exact_error_on_next

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.Tomography
