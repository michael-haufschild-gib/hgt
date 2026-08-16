import GaloisForLFunctions.HTGeometry.LeftNormedBracketLayer

/-!
# Vertical curvature from horizontal controls

The second-order generator of a commutator loop is `-i[A,B]`, whose diagonal entries in the energy
eigenbasis are `-i ∑ₖ (A_{jk}B_{kj} - B_{jk}A_{kj})`.  Those entries can be nonzero even when both
controls have vanishing diagonal, so a purely horizontal loop can create vertical motion.

The witness is the pair `X = |p⟩⟨q| + |q⟩⟨p|`, `Y = -i|p⟩⟨q| + i|q⟩⟨p|`: both are Hermitian with zero
diagonal, and `-i[X,Y] = 2(|p⟩⟨p| - |q⟩⟨q|)`.
-/

open Finset Matrix

namespace GaloisForLFunctions.HTGeometry

section Curvature

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The product of two matrix units with matching inner index. -/
theorem single_mul_single_same (p q s : n) :
    (Matrix.single p q (1 : ℂ)) * (Matrix.single q s 1) = Matrix.single p s 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single q]
  · simp only [Matrix.single_apply]
    by_cases hpi : p = i <;> by_cases hsj : s = j <;> simp [hpi, hsj]
  · intro k _ hk
    simp only [Matrix.single_apply]
    rw [if_neg (fun hc => hk hc.2.symm), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ q) h

/-- The product of two matrix units with mismatched inner index vanishes. -/
theorem single_mul_single_ne {p q r s : n} (h : q ≠ r) :
    (Matrix.single p q (1 : ℂ)) * (Matrix.single r s 1) = 0 := by
  ext i j
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  simp only [Matrix.single_apply]
  by_cases h1 : p = i ∧ q = k
  · rw [if_pos h1, one_mul, if_neg]
    rintro ⟨hrk, -⟩
    exact h (h1.2.trans hrk.symm)
  · rw [if_neg h1, zero_mul]

/-! ## The horizontal witnesses -/

/-- The symmetric horizontal control. -/
def curvX (p q : n) : Matrix n n ℂ := Matrix.single p q 1 + Matrix.single q p 1

/-- The antisymmetric horizontal control. -/
def curvY (p q : n) : Matrix n n ℂ :=
  (-Complex.I) • Matrix.single p q 1 + Complex.I • Matrix.single q p 1

omit [Fintype n] in
theorem curvX_diag {p q : n} (hpq : p ≠ q) (i : n) : curvX p q i i = 0 := by
  simp only [curvX, Matrix.add_apply, Matrix.single_apply]
  rw [if_neg (by rintro ⟨h1, h2⟩; exact hpq (h1.trans h2.symm)),
    if_neg (by rintro ⟨h1, h2⟩; exact hpq (h2.trans h1.symm))]
  ring

omit [Fintype n] in
theorem curvY_diag {p q : n} (hpq : p ≠ q) (i : n) : curvY p q i i = 0 := by
  simp only [curvY, Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
  rw [if_neg (by rintro ⟨h1, h2⟩; exact hpq (h1.trans h2.symm)),
    if_neg (by rintro ⟨h1, h2⟩; exact hpq (h2.trans h1.symm))]
  ring

/-- **`(34)`/`(37)`: horizontal controls with nonzero vertical curvature.**  The commutator of the two
zero-diagonal witnesses is a nonzero multiple of the difference of two spectral projections. -/
theorem curv_commutator {p q : n} (hpq : p ≠ q) :
    (-Complex.I) • (curvX p q * curvY p q - curvY p q * curvX p q)
      = (2 : ℂ) • (Matrix.single p p (1 : ℂ) - Matrix.single q q 1) := by
  have hqp : q ≠ p := hpq.symm
  have hXY : curvX p q * curvY p q
      = Complex.I • Matrix.single p p (1 : ℂ) - Complex.I • Matrix.single q q 1 := by
    simp only [curvX, curvY, Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul,
      single_mul_single_same, single_mul_single_ne hpq, single_mul_single_ne hqp]
    module
  have hYX : curvY p q * curvX p q
      = (-Complex.I) • Matrix.single p p (1 : ℂ) + Complex.I • Matrix.single q q 1 := by
    simp only [curvX, curvY, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
      single_mul_single_same, single_mul_single_ne hpq, single_mul_single_ne hqp]
    module
  have expand : curvX p q * curvY p q - curvY p q * curvX p q
      = (2 * Complex.I) • Matrix.single p p (1 : ℂ)
        - (2 * Complex.I) • Matrix.single q q 1 := by
    rw [hXY, hYX]
    module
  have hc : (-Complex.I) * (2 * Complex.I) = 2 := by
    linear_combination (-2 : ℂ) * Complex.I_sq
  rw [expand, smul_sub, smul_smul, smul_smul, hc, smul_sub]

theorem curv_commutator_ne_zero {p q : n} (hpq : p ≠ q) :
    (-Complex.I) • (curvX p q * curvY p q - curvY p q * curvX p q) ≠ 0 := by
  rw [curv_commutator hpq]
  intro hzero
  have hentry := congrFun (congrFun hzero p) p
  simp [Ne.symm hpq] at hentry

omit [DecidableEq n] in
/-- **`(35)`: the diagonal entries of a commutator.** -/
theorem commutator_diag_apply (A B : Matrix n n ℂ) (j : n) :
    (A * B - B * A) j j = ∑ k, (A j k * B k j - B j k * A k j) := by
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib]


/-! ## The curvature values span the traceless diagonals -/

/-- **The anchored differences span.**  Every traceless diagonal matrix is a combination of the
differences `P_p - P_j`, which are exactly the curvature values of Proposition E. -/
theorem diagonal_eq_sum_anchored (p : n) (a : n → ℂ) (ha : ∑ i, a i = 0) :
    Matrix.diagonal a
      = ∑ j ∈ Finset.univ.erase p,
          (-(a j)) • (Matrix.single p p (1 : ℂ) - Matrix.single j j 1) := by
  ext i k
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.single_apply,
    Matrix.diagonal_apply, smul_eq_mul]
  by_cases hik : i = k
  · subst hik
    simp only [and_self, if_true]
    by_cases hip : i = p
    · subst hip
      have hsimp : ∀ j ∈ Finset.univ.erase i,
          -(a j) * ((if i = i then (1 : ℂ) else 0) - (if j = i then 1 else 0)) = -(a j) := by
        intro j hj
        have hji : j ≠ i := Finset.ne_of_mem_erase hj
        simp [hji]
      rw [Finset.sum_congr rfl hsimp]
      have hsplit : ∑ j, a j = a i + ∑ j ∈ Finset.univ.erase i, a j :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
      rw [hsplit] at ha
      rw [Finset.sum_neg_distrib]
      linear_combination ha
    · have hsimp : ∀ j ∈ Finset.univ.erase p,
          -(a j) * ((if p = i then (1 : ℂ) else 0) - (if j = i then 1 else 0))
            = if j = i then a i else 0 := by
        intro j _
        by_cases hji : j = i
        · subst hji
          simp [Ne.symm hip]
        · simp [hji, Ne.symm hip]
      rw [Finset.sum_congr rfl hsimp, Finset.sum_ite_eq' (Finset.univ.erase p) i (fun _ => a i),
        if_pos (Finset.mem_erase.mpr ⟨hip, Finset.mem_univ i⟩)]
  · rw [if_neg hik]
    refine (Finset.sum_eq_zero fun j _ => ?_).symm
    have h1 : ¬ (p = i ∧ p = k) := fun h => hik (h.1.symm.trans h.2)
    have h2 : ¬ (j = i ∧ j = k) := fun h => hik (h.1.symm.trans h.2)
    rw [if_neg h1, if_neg h2]
    ring


end Curvature

end GaloisForLFunctions.HTGeometry
