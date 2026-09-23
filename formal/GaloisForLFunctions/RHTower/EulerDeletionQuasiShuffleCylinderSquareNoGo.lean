import GaloisForLFunctions.RHTower.EulerDeletionQuasiShuffleCylinderClosure

/-!
# Repeated-generator obstruction for Euler-deletion cylinders

The pairwise-coprime cylinder formula is squarefree.  It does not extend to a pointwise algebra
inside the zero-mean deletion channels: squaring one modulus introduces a constant component.
For the dyadic channel this is exact pointwise collapse to `1`, so its unweighted square prefixes
grow linearly instead of remaining bounded.

These finite arithmetic identities use no analytic continuation or zeta input.  They rule out
treating the squarefree cylinder system as a closed pointwise algebra for the bounded-prefix Abel
construction.
-/

noncomputable section

open scoped BigOperators

namespace RHTower

/-- Every repeated deletion generator splits into a constant channel and one deletion channel. -/
theorem blockDeletionCoefficient_sq_eq (p n : ℕ) :
    blockDeletionCoefficient p n ^ (2 : ℕ) =
      (p : ℤ) - 1 + (2 - (p : ℤ)) * blockDeletionCoefficient p n := by
  by_cases hpn : p ∣ n
  · simp [blockDeletionCoefficient, hpn]
    ring
  · simp [blockDeletionCoefficient, hpn]

/-- The dyadic deletion generator is pointwise involutive. -/
theorem blockDeletionCoefficient_two_sq (n : ℕ) :
    blockDeletionCoefficient 2 n ^ (2 : ℕ) = 1 := by
  simpa using blockDeletionCoefficient_sq_eq 2 n

/-- Subtracting the constant square component produces only the original channel again. -/
theorem blockDeletionCoefficient_centered_sq_eq (p n : ℕ) :
    blockDeletionCoefficient p n ^ (2 : ℕ) - ((p : ℤ) - 1) =
      (2 - (p : ℤ)) * blockDeletionCoefficient p n := by
  rw [blockDeletionCoefficient_sq_eq]
  ring

/-- Centering the dyadic square erases it completely. -/
theorem blockDeletionCoefficient_two_centered_sq_eq_zero (n : ℕ) :
    blockDeletionCoefficient 2 n ^ (2 : ℕ) - 1 = 0 := by
  rw [blockDeletionCoefficient_two_sq]
  ring

/-- Dyadic square prefixes grow exactly linearly, so the bounded-prefix cancellation is lost. -/
theorem sum_blockDeletionCoefficient_two_sq (N : ℕ) :
    ∑ n ∈ Finset.range N, blockDeletionCoefficient 2 (n + 1) ^ (2 : ℕ) = (N : ℤ) := by
  simp_rw [blockDeletionCoefficient_two_sq]
  simp

end RHTower
