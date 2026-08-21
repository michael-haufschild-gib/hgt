import GaloisForLFunctions.HTGeometry.CassidySl2Graded
import GaloisForLFunctions.HTGeometry.UnipotentParameterSubgroup

/-!
# The adjoint action on `sl₂` is irreducible

A subspace of the traceless `2×2` matrices stable under conjugation by the upper and lower
unipotents is either zero or everything.  The proof is a finite computation: conjugating by
`u(t) = [[1, t], [0, 1]]` moves `A` by a quadratic polynomial in `t`, so taking `t = ±1` and
subtracting the value at `t = 0` isolates its two coefficients; from any nonzero traceless `A` one
of those coefficients is a nonzero multiple of the raising matrix `e`, and conjugating `e` by the
lower unipotents produces `h` and `f`.

This is the irreducibility that makes a Zariski-dense subgroup's Lie algebra span `sl₂`: a stable
subspace has no room to be proper.

* `unipotentLower`, `upperConj`, `lowerConj`, `upperConj_entry`, `lowerConj_entry`;
* `raising_mem_of_adStable`;
* `sl2_of_adStable` — the irreducibility.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {U : Type*} [Field U]

/-- The lower unipotent with parameter `t`. -/
def unipotentLower (t : U) : Matrix (Fin 2) (Fin 2) U := !![1, 0; t, 1]

/-- Conjugation by the upper unipotent. -/
def upperConj (t : U) (A : Matrix (Fin 2) (Fin 2) U) : Matrix (Fin 2) (Fin 2) U :=
  unipotentUpper t * A * unipotentUpper (-t)

/-- Conjugation by the lower unipotent. -/
def lowerConj (t : U) (A : Matrix (Fin 2) (Fin 2) U) : Matrix (Fin 2) (Fin 2) U :=
  unipotentLower t * A * unipotentLower (-t)

theorem upperConj_entry (t : U) (A : Matrix (Fin 2) (Fin 2) U) :
    upperConj t A 0 0 = A 0 0 + t * A 1 0 ∧
    upperConj t A 0 1 = A 0 1 + t * (A 1 1 - A 0 0) - t ^ 2 * A 1 0 ∧
    upperConj t A 1 0 = A 1 0 ∧
    upperConj t A 1 1 = A 1 1 - t * A 1 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    simp [upperConj, unipotentUpper, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul,
      dotProduct]
    try ring

theorem lowerConj_entry (t : U) (A : Matrix (Fin 2) (Fin 2) U) :
    lowerConj t A 0 0 = A 0 0 - t * A 0 1 ∧
    lowerConj t A 0 1 = A 0 1 ∧
    lowerConj t A 1 0 = A 1 0 + t * (A 0 0 - A 1 1) - t ^ 2 * A 0 1 ∧
    lowerConj t A 1 1 = A 1 1 + t * A 0 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    simp [lowerConj, unipotentLower, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul,
      dotProduct]
    try ring

variable [CharZero U]

/-- **The raising matrix is in every nonzero stable subspace of traceless matrices.** -/
theorem raising_mem_of_adStable (V : Submodule U (Matrix (Fin 2) (Fin 2) U))
    (hupper : ∀ t : U, ∀ A ∈ V, upperConj t A ∈ V)
    {A : Matrix (Fin 2) (Fin 2) U} (hA : A ∈ V) (hAne : A ≠ 0) (htr : A 1 1 = -A 0 0) :
    sl2E U ∈ V := by
  have h1 := hupper 1 A hA
  have hm1 := hupper (-1) A hA
  -- the `t²` coefficient
  have hquad : (-(2 : U) * A 1 0) • sl2E U ∈ V := by
    have hsum := V.add_mem (V.add_mem h1 hm1) (V.smul_mem (-(2 : U)) hA)
    have heq : upperConj 1 A + upperConj (-1) A + (-(2 : U)) • A
        = (-(2 : U) * A 1 0) • sl2E U := by
      obtain ⟨p1, p2, p3, p4⟩ := upperConj_entry (1 : U) A
      obtain ⟨q1, q2, q3, q4⟩ := upperConj_entry (-1 : U) A
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j <;>
        simp [sl2E, htr, Matrix.add_apply, Matrix.smul_apply, p1, p2, p3, p4,
          q1, q2, q3, q4] <;> ring
    rwa [heq] at hsum
  -- the `t` coefficient
  have hlin : ((2 : U) * A 1 0) • sl2H U + (-(4 : U) * A 0 0) • sl2E U ∈ V := by
    have hsub := V.add_mem h1 (V.smul_mem (-1 : U) hm1)
    have heq : upperConj 1 A + (-1 : U) • upperConj (-1) A
        = ((2 : U) * A 1 0) • sl2H U + (-(4 : U) * A 0 0) • sl2E U := by
      obtain ⟨p1, p2, p3, p4⟩ := upperConj_entry (1 : U) A
      obtain ⟨q1, q2, q3, q4⟩ := upperConj_entry (-1 : U) A
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j <;>
        simp [sl2E, sl2H, htr, Matrix.add_apply, p1, p2, p3, p4,
          q1, q2, q3, q4] <;> ring
    rwa [heq] at hsub
  by_cases hc : A 1 0 = 0
  · by_cases ha : A 0 0 = 0
    · -- A = A 0 1 • e, and A ≠ 0 forces A 0 1 ≠ 0
      have hb : A 0 1 ≠ 0 := by
        intro hb0
        refine hAne (Matrix.ext fun i j => ?_)
        fin_cases i <;> fin_cases j <;> simp [hc, ha, hb0, htr]
      have hEeq : (A 0 1)⁻¹ • A = sl2E U := by
        refine Matrix.ext fun i j => ?_
        fin_cases i <;> fin_cases j <;>
          simp [sl2E, hc, ha, htr, Matrix.smul_apply, inv_mul_cancel₀ hb]
      rw [← hEeq]
      exact V.smul_mem _ hA
    · -- the `t` coefficient is a nonzero multiple of `e`
      have heq : ((2 : U) * A 1 0) • sl2H U + (-(4 : U) * A 0 0) • sl2E U
          = (-(4 : U) * A 0 0) • sl2E U := by
        rw [hc, mul_zero, zero_smul, zero_add]
      rw [heq] at hlin
      have hne : (-(4 : U) * A 0 0) ≠ 0 := by
        simp only [ne_eq, mul_eq_zero, neg_eq_zero, not_or]
        exact ⟨by norm_num, ha⟩
      have := V.smul_mem (-(4 : U) * A 0 0)⁻¹ hlin
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
  · have hne : (-(2 : U) * A 1 0) ≠ 0 := by
      simp only [ne_eq, mul_eq_zero, neg_eq_zero, not_or]
      exact ⟨by norm_num, hc⟩
    have := V.smul_mem (-(2 : U) * A 1 0)⁻¹ hquad
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this

/-- **The adjoint action on `sl₂` is irreducible.**  A nonzero subspace of traceless matrices stable
under conjugation by both unipotent lines is everything. -/
theorem sl2_of_adStable (V : Submodule U (Matrix (Fin 2) (Fin 2) U))
    (hupper : ∀ t : U, ∀ A ∈ V, upperConj t A ∈ V)
    (hlower : ∀ t : U, ∀ A ∈ V, lowerConj t A ∈ V)
    {A : Matrix (Fin 2) (Fin 2) U} (hA : A ∈ V) (hAne : A ≠ 0) (htr : A 1 1 = -A 0 0)
    {Z : Matrix (Fin 2) (Fin 2) U} (hZ : Z 1 1 = -Z 0 0) : Z ∈ V := by
  have he : sl2E U ∈ V := raising_mem_of_adStable V hupper hA hAne htr
  have h1 := hlower 1 _ he
  have hm1 := hlower (-1) _ he
  have hf : sl2F U ∈ V := by
    have hsum := V.add_mem (V.add_mem h1 hm1) (V.smul_mem (-(2 : U)) he)
    have heq : lowerConj 1 (sl2E U) + lowerConj (-1) (sl2E U) + (-(2 : U)) • sl2E U
        = (-(2 : U)) • sl2F U := by
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j
      all_goals
        simp [lowerConj, unipotentLower, sl2E, sl2F, Matrix.add_apply]
        try ring
    rw [heq] at hsum
    have := V.smul_mem (-(2 : U))⁻¹ hsum
    rwa [smul_smul, inv_mul_cancel₀ (by norm_num : (-(2 : U)) ≠ 0), one_smul] at this
  have hh : sl2H U ∈ V := by
    have hsub := V.add_mem h1 (V.smul_mem (-1 : U) hm1)
    have heq : lowerConj 1 (sl2E U) + (-1 : U) • lowerConj (-1) (sl2E U)
        = (-(2 : U)) • sl2H U := by
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j
      all_goals
        simp [lowerConj, unipotentLower, sl2E, sl2H, Matrix.add_apply]
        try ring
    rw [heq] at hsub
    have := V.smul_mem (-(2 : U))⁻¹ hsub
    rwa [smul_smul, inv_mul_cancel₀ (by norm_num : (-(2 : U)) ≠ 0), one_smul] at this
  have hZeq : Z = (Z 0 0) • sl2H U + (Z 0 1) • sl2E U + (Z 1 0) • sl2F U := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [sl2E, sl2F, sl2H, hZ, Matrix.add_apply]
  rw [hZeq]
  exact V.add_mem (V.add_mem (V.smul_mem _ hh) (V.smul_mem _ he)) (V.smul_mem _ hf)

end

end GaloisForLFunctions.HTGeometry
