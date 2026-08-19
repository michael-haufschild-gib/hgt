import GaloisForLFunctions.RHTower.Sieve.CoprimeMoebiusHarmonic

/-!
# Basic bounds for the coprime harmonic sum

Elementary positivity and comparison facts for `H_e(z) = ∑_{k ≤ z, (e,k)=1} 1/k`: it is
nonnegative, dominated by the full harmonic sum, and at least `1` as soon as the window is
nonempty, because `k = 1` is coprime to every modulus.
-/

open Finset
open scoped BigOperators

namespace RHTower.Sieve

theorem coprimeHarmonic_nonneg (e z : ℕ) : 0 ≤ coprimeHarmonic e z := by
  refine Finset.sum_nonneg fun k hk => ?_
  obtain ⟨hkmem, -⟩ := Finset.mem_filter.mp hk
  obtain ⟨hk1, -⟩ := Finset.mem_Icc.mp hkmem
  have : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  positivity

theorem coprimeHarmonic_le (e z : ℕ) :
    coprimeHarmonic e z ≤ ∑ k ∈ Finset.Icc 1 z, 1 / (k : ℝ) := by
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
  intro k hk _
  obtain ⟨hk1, -⟩ := Finset.mem_Icc.mp hk
  have : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  positivity

theorem one_le_coprimeHarmonic {e z : ℕ} (hz : 1 ≤ z) : 1 ≤ coprimeHarmonic e z := by
  have hmem : (1 : ℕ) ∈ (Finset.Icc 1 z).filter (fun k => Nat.Coprime e k) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_refl 1, hz⟩, ?_⟩
    exact Nat.coprime_one_right e
  have hle : 1 / ((1 : ℕ) : ℝ) ≤ coprimeHarmonic e z := by
    rw [coprimeHarmonic]
    refine Finset.single_le_sum (f := fun k : ℕ => 1 / (k : ℝ)) ?_ hmem
    intro k hk
    obtain ⟨hkmem, -⟩ := Finset.mem_filter.mp hk
    obtain ⟨hk1, -⟩ := Finset.mem_Icc.mp hkmem
    have : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    positivity
  simpa using hle

end RHTower.Sieve
