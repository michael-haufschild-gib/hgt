import GaloisForLFunctions.HTGeometry.Moments.FiniteStateLeadingMinors
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Delay is finite-state memory

A geometric response starting at index `d` has minimum state dimension `d + 1`,
independently of its ratio. All positive leading Hankel determinants vanish except
the one of size `d + 1`: reversing its rows gives a triangular matrix with diagonal
one. Thus an arbitrarily long initial run of zero leading determinants need not
imply small state dimension.
-/

open scoped BigOperators Matrix

namespace HTGeometry.FiniteHankel

variable {K : Type*} [Field K]

/-- A geometric response with `d` initial zeros and first nonzero value one. -/
def delayedGeometric (q : K) (d n : ℕ) : K :=
  if d ≤ n then q ^ (n - d) else 0

/-- Row reversal makes the onset-sized Hankel block triangular with diagonal one. -/
theorem delayedGeometric_leadingDet_onset_ne_zero (q : K) (d : ℕ) :
    leadingDet (delayedGeometric q d) (d + 1) ≠ 0 := by
  let H : Matrix (Fin (d + 1)) (Fin (d + 1)) K :=
    Matrix.of fun i j => delayedGeometric q d (i.val + j.val)
  let T := H.submatrix Fin.rev id
  have htri : T.BlockTriangular id := by
    intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    have hji : j.val < i.val := hij
    change delayedGeometric q d ((Fin.rev i).val + j.val) = 0
    rw [Fin.val_rev, delayedGeometric, if_neg (by omega)]
  have hdiag : ∀ i : Fin (d + 1), T i i = 1 := by
    intro i
    have hi := i.isLt
    change delayedGeometric q d ((Fin.rev i).val + i.val) = 1
    rw [Fin.val_rev, show d + 1 - (i.val + 1) + i.val = d by omega]
    simp [delayedGeometric]
  have hdet : T.det = 1 := by
    rw [Matrix.det_of_upperTriangular htri]
    simp only [hdiag, Finset.prod_const_one]
  have hp : T.det = (Equiv.Perm.sign (Fin.revPerm (n := d + 1)) : K) * H.det :=
    Matrix.det_permute (Fin.revPerm (n := d + 1)) H
  intro hz
  change H.det = 0 at hz
  rw [hdet, hz, mul_zero] at hp
  exact one_ne_zero hp

/-- Every smaller nonempty leading block has a zero first row. -/
theorem delayedGeometric_leadingDet_before_onset (q : K) (d n : ℕ)
    (hn : 0 < n) (hnd : n ≤ d) : leadingDet (delayedGeometric q d) n = 0 := by
  apply Matrix.det_eq_zero_of_row_eq_zero (i := ⟨0, hn⟩)
  intro j
  simp only [Matrix.of_apply, zero_add, delayedGeometric]
  exact if_neg (by have hj := j.isLt; omega)

/-- The recurrence remembers the delay before advancing the geometric tail. -/
def delayedGeometricRecurrence (q : K) (d : ℕ) : LinearRecurrence K :=
  ⟨d + 1, Pi.single (Fin.last d) q⟩

theorem delayedGeometric_isSolution (q : K) (d : ℕ) :
    (delayedGeometricRecurrence q d).IsSolution (delayedGeometric q d) := by
  intro n
  change delayedGeometric q d (n + (d + 1)) =
    ∑ j : Fin (d + 1), (Pi.single (Fin.last d) q : Fin (d + 1) → K) j *
      delayedGeometric q d (n + j.val)
  simp only [Pi.single_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, Fin.val_last]
  rw [delayedGeometric, if_pos (by omega), delayedGeometric, if_pos (by omega)]
  rw [show n + (d + 1) - d = n + 1 by omega, show n + d - d = n by omega, pow_succ']

/-- Every leading determinant after the onset-sized block vanishes. -/
theorem delayedGeometric_leading_tail_zero (q : K) (d : ℕ) :
    ∀ n, d + 1 < n → leadingDet (delayedGeometric q d) n = 0 :=
  (leading_tail_zero_iff_recurrence _ _).mpr
    ⟨delayedGeometricRecurrence q d, le_rfl, delayedGeometric_isSolution q d⟩

/-- Exactly one nonempty leading Hankel block is nonsingular. -/
theorem delayedGeometric_leadingDet_ne_zero_iff (q : K) (d n : ℕ) :
    leadingDet (delayedGeometric q d) n ≠ 0 ↔ n = 0 ∨ n = d + 1 := by
  constructor
  · intro h
    by_cases hz : n = 0
    · exact Or.inl hz
    by_cases he : n = d + 1
    · exact Or.inr he
    by_cases hn : n ≤ d
    · exact False.elim (h (delayedGeometric_leadingDet_before_onset q d n (by omega) hn))
    · exact False.elim (h (delayedGeometric_leading_tail_zero q d n (by omega)))
  · rintro (rfl | rfl)
    · simp [leadingDet]
    · exact delayedGeometric_leadingDet_onset_ne_zero q d

/-- The minimum state dimension counts every initial zero as well as the geometric tail. -/
theorem delayedGeometric_minimal_stateSpace (q : K) (d : ℕ) :
    AlgebraicStateSpaceDimensionAtMost (d + 1) (delayedGeometric q d) ∧
      ∀ B, AlgebraicStateSpaceDimensionAtMost B (delayedGeometric q d) → d + 1 ≤ B :=
  last_nonzero_leading_det_minimal_stateSpace _ _
    (delayedGeometric_leadingDet_onset_ne_zero q d) (delayedGeometric_leading_tail_zero q d)

/-- No recurrence of smaller order can produce the delayed response from index zero. -/
theorem delayedGeometric_recurrence_order_le (q : K) (d : ℕ) (E : LinearRecurrence K)
    (hE : E.IsSolution (delayedGeometric q d)) : d + 1 ≤ E.order :=
  (delayedGeometric_minimal_stateSpace q d).2 _ (stateSpace_of_recurrence E hE)

#print axioms delayedGeometric_leadingDet_ne_zero_iff
#print axioms delayedGeometric_minimal_stateSpace
#print axioms delayedGeometric_recurrence_order_le

end HTGeometry.FiniteHankel
