import GaloisForLFunctions.HTGeometry.FundamentalMatrixUniqueness

/-!
# A local system with no fundamental matrix in any extension

The integrability condition is necessary for a fundamental matrix but not sufficient.  If a source
direction acts trivially on the ambient field and the local system is `-1` in that direction, the
defining equation forces the solution matrix to be its own negative, hence zero, hence not
invertible — in every field of characteristic zero, whatever else the extension contains.

So the hypothesis "the homogeneous system has an invertible solution matrix" in the curved rank law
is a genuine hypothesis, not a removable one.
-/

open Set
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

/-- A self-negating matrix over a field of characteristic zero is zero. -/
theorem eq_zero_of_eq_neg {L : Type u} [Field L] [CharZero L] {κ : Type u}
    {Y : Matrix κ κ L} (h : Y = -Y) : Y = 0 := by
  ext p q
  have hpq : Y p q = -Y p q := by rw [← Matrix.neg_apply, ← h]
  have h2 : (2 : L) * Y p q = 0 := by linear_combination hpq
  rcases mul_eq_zero.mp h2 with hzero | hy
  · exact absurd hzero (by norm_num)
  · simpa using hy

/-- A self-negating matrix over a field of characteristic zero has no right inverse. -/
theorem not_invertible_of_eq_neg {L : Type u} [Field L] [CharZero L] {κ : Type u} [Fintype κ]
    [DecidableEq κ] [Nonempty κ] {Y Yinv : Matrix κ κ L} (hYY : Y * Yinv = 1) (h : Y = -Y) :
    False := by
  rw [eq_zero_of_eq_neg h, zero_mul] at hYY
  exact zero_ne_one hYY

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  {I : Type u} (sigma : I → L ≃+* L)
  {κ : Type u} [Fintype κ] [DecidableEq κ]

omit [Fintype κ] in
/-- The image of the negative identity is the negative identity. -/
theorem baseMat_neg_one : baseMat (-1 : Matrix κ κ K) = (-1 : Matrix κ κ L) := by
  ext p q
  simp [baseMat, Matrix.one_apply, apply_ite (algebraMap K L)]

/-- **Existence of a fundamental matrix can fail in every extension.**  If a source direction acts
trivially and the local system is `-1` in that direction, no invertible solution matrix exists,
whatever the ambient field of characteristic zero. -/
theorem not_exists_fundamental_of_neg_one [CharZero L] [Nonempty κ] (i₀ : I)
    (hid : ∀ x : L, sigma i₀ x = x)
    {Y Yinv : Matrix κ κ L} {M : I → Matrix κ κ K}
    (hYY : Y * Yinv = 1) (hM : M i₀ = -1)
    (hfund : ∀ i, Y.map (sigma i) = baseMat (M i) * Y) :
    False := by
  refine not_invertible_of_eq_neg hYY ?_
  have hY : Y.map (sigma i₀) = Y := by
    ext p q
    exact hid (Y p q)
  have h := hfund i₀
  rw [hY, hM, baseMat_neg_one, neg_one_mul] at h
  exact h

end

end GaloisForLFunctions.HTGeometry
