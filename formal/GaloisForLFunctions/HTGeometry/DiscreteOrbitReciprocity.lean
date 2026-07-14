import Mathlib

/-!
# Discrete 2D exactness and corner reciprocity

The direct proof of triptic orbit-residue reciprocity reduces its analytic content to a purely
discrete statement about a doubly-indexed coefficient array `c : ℤ → ℤ → M`.  Two structural
constraints hold: the horizontal increment is independent of the column and the vertical increment
is independent of the row (this is what the mixed-difference constancy of the primitive `F`
imposes).  Such an array is additively separable, `c n m = c n 0 + (c 0 m - c 0 0)`, and its two
boundary jump families `A, B` have equal total sums once the meromorphic local-finiteness inputs —
the corner accumulation identities — are supplied.  This file isolates that discrete core; the only
analytic step (accumulation vanishing in the two mixed quadrants) enters as explicit hypotheses.
-/

open Finset

namespace GaloisForLFunctions

/-- **Discrete 2D exactness / additive separability.**  If the vertical increments of a
doubly-indexed array `c : ℤ → ℤ → M` over an additive commutative group are independent of the row
(`c n (m+1) - c n m = B m`), then the array is additively separable:
`c n m = c n 0 + (c 0 m - c 0 0)`.  The column difference `c n m - c n 0` is the same for every
row, so it equals the reference column difference `c 0 m - c 0 0`. -/
theorem additively_separable_of_indep_increments
    {M : Type*} [AddCommGroup M] (c : ℤ → ℤ → M) (B : ℤ → M)
    (hB : ∀ n m, c n (m + 1) - c n m = B m) :
    ∀ n m, c n m = c n 0 + (c 0 m - c 0 0) := by
  have hcol : ∀ n m, c n m - c n 0 = c 0 m - c 0 0 := by
    intro n m
    induction m using Int.induction_on with
    | zero => simp
    | succ k ih =>
      have h1 := hB n k
      have h2 := hB 0 k
      have e1 : c n (k + 1) - c n 0 = (c n k - c n 0) + B k := by
        rw [← h1]; abel
      have e2 : c 0 (k + 1) - c 0 0 = (c 0 k - c 0 0) + B k := by
        rw [← h2]; abel
      rw [e1, e2, ih]
    | pred k ih =>
      have h1 := hB n (-k - 1)
      have h2 := hB 0 (-k - 1)
      have e1 : c n (-(k:ℤ) - 1) - c n 0 = (c n (-(k:ℤ)) - c n 0) - B (-(k:ℤ) - 1) := by
        have : c n (-(k:ℤ) - 1 + 1) - c n (-(k:ℤ) - 1) = B (-(k:ℤ) - 1) := h1
        rw [show (-(k:ℤ) - 1 + 1) = -(k:ℤ) from by ring] at this
        rw [← this]; abel
      have e2 : c 0 (-(k:ℤ) - 1) - c 0 0 = (c 0 (-(k:ℤ)) - c 0 0) - B (-(k:ℤ) - 1) := by
        have : c 0 (-(k:ℤ) - 1 + 1) - c 0 (-(k:ℤ) - 1) = B (-(k:ℤ) - 1) := h2
        rw [show (-(k:ℤ) - 1 + 1) = -(k:ℤ) from by ring] at this
        rw [← this]; abel
      rw [e1, e2, ih]
  intro n m
  have h := hcol n m
  rw [sub_eq_iff_eq_add] at h
  rw [h]; abel

/-- **Corner reciprocity.**  Given the two boundary jump families `A, B` (supported in a finite set
`s`) and the two corner-accumulation identities coming from meromorphic local finiteness — the
positive-side `A`-mass equals the negative-side `B`-mass, and the positive-side `B`-mass equals the
negative-side `A`-mass — the total jump sums agree: `∑ A = ∑ B`.  This is the triptic reciprocity
`R_τ(F) = R_σ(F)` at one `(g,k)` coordinate, with the accumulation vanishing (the only analytic
input) supplied as hypotheses. -/
theorem corner_reciprocity {M : Type*} [AddCommGroup M] (s : Finset ℤ) (A B : ℤ → M)
    (hAB : ∑ i ∈ s.filter (fun i => 0 ≤ i), A i = ∑ j ∈ s.filter (fun j => j < 0), B j)
    (hBA : ∑ j ∈ s.filter (fun j => 0 ≤ j), B j = ∑ i ∈ s.filter (fun i => i < 0), A i) :
    ∑ i ∈ s, A i = ∑ j ∈ s, B j := by
  have splitA : ∑ i ∈ s, A i
      = ∑ i ∈ s.filter (fun i => 0 ≤ i), A i + ∑ i ∈ s.filter (fun i => ¬ 0 ≤ i), A i :=
    (Finset.sum_filter_add_sum_filter_not s (fun i => 0 ≤ i) A).symm
  have splitB : ∑ j ∈ s, B j
      = ∑ j ∈ s.filter (fun j => 0 ≤ j), B j + ∑ j ∈ s.filter (fun j => ¬ 0 ≤ j), B j :=
    (Finset.sum_filter_add_sum_filter_not s (fun j => 0 ≤ j) B).symm
  have hneg : s.filter (fun i => ¬ 0 ≤ i) = s.filter (fun i => i < 0) := by
    apply Finset.filter_congr; intro x _; simp [not_le]
  rw [splitA, splitB, hneg]
  rw [hAB, hBA]
  abel

end GaloisForLFunctions
