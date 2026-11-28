import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.Tomography.Moments

/-! # Quantitative recovery of each occupation from vacuum survival -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.Tomography

open Finset Filter InverseSpectrum.ShellMixing
open scoped Topology

/-- Remove the lower energy populations and divide by the response on k. -/
def estimate (z : ℕ → SplitParameter) (f : Gas) (k j : ℕ) :=
  (survival z f j - ∑ i ∈ range k, occupationWeight i^j * population f i) / occupationWeight k^j

def tailMass (f : Gas) (k : ℕ) := ∑' i, population f (i+(k+1))

def ratio (k : ℕ) := occupationWeight (k+1)/occupationWeight k

private theorem ratio_lt_one (k : ℕ) : ratio k < 1 :=
  (div_lt_one (occupationWeight_pos k)).mpr (occupationWeight_strictAnti (Nat.lt_succ_self k))

/-- The residual error is exactly the positive contribution from higher shells. -/
theorem error_eq (z : ℕ → SplitParameter) (f : Gas) (k j : ℕ) :
    estimate z f k j - population f k =
      ∑' i, (occupationWeight (i+(k+1))/occupationWeight k)^j * population f (i+(k+1)) := by
  have h := (survival_hasSum z f j).summable.sum_add_tsum_nat_add (k+1)
  rw [Finset.sum_range_succ,(survival_hasSum z f j).tsum_eq] at h
  have nz := (pow_pos (occupationWeight_pos k) j).ne'
  rw [estimate,←h]
  have cancel (a b t d : ℝ) (hd : d≠0) : (a+d*b+t-a)/d-b=t/d := by
    field_simp [hd]
    ring
  rw [cancel _ _ _ _ nz,←tsum_div_const]
  refine tsum_congr fun i => ?_
  rw [div_pow]
  ring

/-- The first unremoved occupation gives a uniform geometric error bound. -/
theorem error_bounds (z : ℕ → SplitParameter) (f : Gas) (k j : ℕ) :
    0 ≤ estimate z f k j - population f k ∧
    estimate z f k j - population f k ≤ ratio k^j * tailMass f k := by
  rw [error_eq,tailMass,←tsum_mul_left]
  let W (i : ℕ) := population f (i+(k+1))
  have sumW : Summable W :=
    (summable_nat_add_iff (f := population f) (k+1)).mpr (gas_coords_summable f)
  have lower (i : ℕ) : 0 ≤ (occupationWeight (i+(k+1))/occupationWeight k)^j * W i :=
    mul_nonneg (pow_nonneg (div_pos (occupationWeight_pos _) (occupationWeight_pos _)).le _) (sq_nonneg _)
  have upper (i : ℕ) : (occupationWeight (i+(k+1))/occupationWeight k)^j * W i ≤ ratio k^j * W i := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply pow_le_pow_left₀ (div_pos (occupationWeight_pos _) (occupationWeight_pos _)).le
    exact div_le_div_of_nonneg_right (occupationWeight_antitone (Nat.le_add_left _ _)) (occupationWeight_pos _).le
  have summ := sumW.mul_left (ratio k^j)
  exact ⟨tsum_nonneg lower,Summable.tsum_le_tsum upper (summ.of_nonneg_of_le lower upper) summ⟩

theorem estimate_limit (z : ℕ → SplitParameter) (f : Gas) (k : ℕ) :
    Tendsto (estimate z f k) atTop (𝓝 (population f k)) := by
  have dec := tendsto_pow_atTop_nhds_zero_of_lt_one
    (div_pos (occupationWeight_pos (k+1)) (occupationWeight_pos k)).le (ratio_lt_one k)
  have bound := dec.mul_const (tailMass f k)
  rw [zero_mul] at bound
  have err := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds bound
    (fun j => (error_bounds z f k j).1) (fun j => (error_bounds z f k j).2)
  simpa only [zero_add,sub_add_cancel] using err.add_const (population f k)

#print axioms error_bounds
#print axioms estimate_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.Tomography
