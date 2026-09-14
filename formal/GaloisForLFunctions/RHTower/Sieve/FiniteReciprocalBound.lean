import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound

/-!
# Lightweight bounded reciprocal sum

A finite family of positive integers below `N` has reciprocal mass at most `1 + log N`.  This
elementary estimate lives independently of later paper-scale asymptotics so harmonic Kloosterman
bounds do not inherit unrelated analytic imports.
-/

namespace RHTower.Sieve

open Finset

/-- Reciprocal mass of a finite positive family below `N`. -/
theorem sum_inv_finset_bounded_le_one_add_log
    (S : Finset ℕ) (N : ℕ)
    (hpos : ∀ q ∈ S, 1 ≤ q) (hupper : ∀ q ∈ S, q ≤ N) :
    ∑ q ∈ S, 1 / (q : ℝ) ≤ 1 + Real.log N := by
  have hsub : S ⊆ Finset.Icc 1 N := by
    intro q hq
    exact Finset.mem_Icc.mpr ⟨hpos q hq, hupper q hq⟩
  calc
    ∑ q ∈ S, 1 / (q : ℝ) ≤ ∑ q ∈ Finset.Icc 1 N, 1 / (q : ℝ) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q hqS _ => by
        rw [Finset.mem_Icc] at hqS
        positivity)
    _ ≤ 1 + Real.log N := sum_Icc_one_div_le_one_add_log N

end RHTower.Sieve
