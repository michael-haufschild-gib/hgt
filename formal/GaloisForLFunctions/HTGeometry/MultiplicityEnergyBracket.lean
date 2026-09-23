import Mathlib

/-!
# The multiplicity energy of a finite multiset of points

Given finitely many points carrying positive integer multiplicities `m i`, the *multiplicity energy*
`∑ (m i)^(2 : ℕ)` is at least the total count `∑ m i`, with equality exactly when every multiplicity is
one.  Normalising, the mean squared multiplicity `(∑ (m i)^(2 : ℕ)) / (∑ m i)` is at least `1`, and equals
`1` exactly in the simple case.

For the zeros of a Dirichlet series in a bounded region this is the statement that the fine-scale
diagonal of the pair correlation of the zeros — the number of ordered pairs of zeros at distance
zero, divided by the number of zeros — measures the mean squared multiplicity, is always at least
one, and detects exactly the failure of the zeros to be simple.  It therefore carries no information
about a factorisation whose factors have disjoint simple zeros.
-/

open Finset

namespace HTGeometry

variable {ι : Type*}

/-- **Energy bracket.**  For positive integer multiplicities the energy dominates the count. -/
theorem sum_le_sum_sq (s : Finset ι) (m : ι → ℕ) :
    ∑ i ∈ s, m i ≤ ∑ i ∈ s, m i ^ (2 : ℕ) :=
  Finset.sum_le_sum fun i _ => by nlinarith [Nat.zero_le (m i)]

/-- Equality in the energy bracket holds exactly when every multiplicity is one, i.e. exactly when
the underlying configuration is simple. -/
theorem sum_sq_eq_sum_iff (s : Finset ι) (m : ι → ℕ) (hm : ∀ i ∈ s, 1 ≤ m i) :
    ∑ i ∈ s, m i ^ (2 : ℕ) = ∑ i ∈ s, m i ↔ ∀ i ∈ s, m i = 1 := by
  constructor
  · intro h i hi
    by_contra hne
    have h1 := hm i hi
    have h2 : 2 ≤ m i := by omega
    have hlt : ∑ j ∈ s, m j < ∑ j ∈ s, m j ^ (2 : ℕ) := by
      refine Finset.sum_lt_sum (fun j hj => by nlinarith [hm j hj]) ⟨i, hi, by nlinarith⟩
    exact absurd h.symm (Nat.ne_of_lt hlt)
  · intro h
    exact Finset.sum_congr rfl fun i hi => by simp [h i hi]

/-- The mean squared multiplicity is at least one. -/
theorem sum_sq_div_sum_ge_one (s : Finset ι) (m : ι → ℕ) (hm : ∀ i ∈ s, 1 ≤ m i)
    (hpos : 0 < ∑ i ∈ s, m i) :
    (1 : ℝ) ≤ (∑ i ∈ s, (m i : ℝ) ^ (2 : ℕ)) / (∑ i ∈ s, (m i : ℝ)) := by
  have hsum : (0 : ℝ) < ∑ i ∈ s, (m i : ℝ) := by
    have : ((∑ i ∈ s, m i : ℕ) : ℝ) = ∑ i ∈ s, (m i : ℝ) := by push_cast; ring
    rw [← this]
    exact_mod_cast hpos
  rw [le_div_iff₀ hsum, one_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have : (1 : ℝ) ≤ (m i : ℝ) := by exact_mod_cast hm i hi
  nlinarith

end HTGeometry
