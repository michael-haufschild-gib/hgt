import Mathlib.Analysis.CStarAlgebra.CStarMatrix

/-!
# Congruence preserves positivity in star-ordered rings

In a star-ordered ring the nonnegative elements are the additive closure of the elements
`star s * s`. Conjugating such a sum by `c` gives a sum of `star (s c) * (s c)`, so `0 ≤ a` implies
`0 ≤ star c * a * c`. For a matrix over a non-unital C*-algebra that is nonnegative in the C*-matrix
order, each diagonal entry is a sum of terms `star (S i k) * S i k` and hence nonnegative.

## Main results

- `star_conjugate_nonneg_of_nonneg`: `0 ≤ a` implies `0 ≤ star c * a * c` in a star-ordered ring.
- `cstarMatrix_diagonal_nonneg_of_nonneg`: a nonnegative `CStarMatrix` has nonnegative diagonal
  entries.

## Hypotheses

Unconditional; the only premises are the positivity hypotheses `0 ≤ a` and `0 ≤ M`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- In a star-ordered ring, conjugation preserves nonnegativity: `0 ≤ a` implies
`0 ≤ star c * a * c`. -/
theorem star_conjugate_nonneg_of_nonneg {R : Type*} [NonUnitalRing R]
    [PartialOrder R] [StarRing R] [StarOrderedRing R]
    {a : R} (ha : 0 ≤ a) (c : R) : 0 ≤ star c * a * c := by
  obtain ⟨p, hp, hap⟩ := (StarOrderedRing.le_iff 0 a).mp ha
  have hclosed : star c * p * c ∈
      AddSubmonoid.closure (Set.range fun s : R => star s * s) := by
    refine AddSubmonoid.closure_induction
      (motive := fun p _ => star c * p * c ∈
        AddSubmonoid.closure (Set.range fun s : R => star s * s)) ?_ ?_ ?_ hp
    · intro x hx
      obtain ⟨s, rfl⟩ := hx
      apply AddSubmonoid.subset_closure
      refine ⟨s * c, ?_⟩
      simp only [star_mul]
      noncomm_ring
    · simp
    · intro x y _ _ hx hy
      rw [mul_add, add_mul]
      exact AddSubmonoid.add_mem _ hx hy
  have haeq : a = p := by simpa using hap
  rw [haeq]
  exact (StarOrderedRing.le_iff 0 (star c * p * c)).mpr
    ⟨star c * p * c, hclosed, by simp⟩

/-- Every diagonal entry of a nonnegative matrix over a non-unital C*-algebra is nonnegative. -/
theorem cstarMatrix_diagonal_nonneg_of_nonneg
    {A ι : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [Fintype ι] (M : CStarMatrix ι ι A) (hM : 0 ≤ M) (k : ι) : 0 ≤ M k k := by
  obtain ⟨p, hp, hMp⟩ := (StarOrderedRing.le_iff 0 M).mp hM
  have hdiag : 0 ≤ p k k := by
    refine AddSubmonoid.closure_induction
      (motive := fun p _ => 0 ≤ p k k) ?_ ?_ ?_ hp
    · intro X hX
      obtain ⟨S, rfl⟩ := hX
      change 0 ≤ (star S * S) k k
      rw [CStarMatrix.mul_apply]
      simp only [CStarMatrix.star_apply]
      exact Finset.sum_nonneg fun i _ => star_mul_self_nonneg (S i k)
    · simp
    · intro X Y _ _ hX hY
      simpa using add_nonneg hX hY
  have hMeq : M = p := by simpa using hMp
  rw [hMeq]
  exact hdiag

end GaloisForLFunctions.HTGeometry
