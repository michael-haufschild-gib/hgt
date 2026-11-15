import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import GaloisForLFunctions.HTGeometry.LinearAlgebra.BinarySelmerBorder

/-!
# Rank shift for binary tournament Laplacians

Complete an arbitrary orientation by its row sums over `𝔽₂`. On an odd number
of vertices, the constant vector splits off from the augmentation hyperplane.
Reciprocity identifies the shifted Laplacian with the transpose plus the
projection onto constants. Consequently adding identity raises rank by one.
-/

open Matrix Finset

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity
noncomputable section

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Independent upper-triangle entries determine an orientation of every pair. -/
def binaryTournamentEdge {n : ℕ} (o : Fin n → Fin n → ZMod 2) :
    Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j => if i = j then 0 else if i < j then o i j else 1 + o j i

/-- Adding the row sum on the diagonal makes every row sum zero in characteristic two. -/
def binaryTournamentLaplacian {n : ℕ} (o : Fin n → Fin n → ZMod 2) :
    Matrix (Fin n) (Fin n) (ZMod 2) :=
  diagonal (fun i => ∑ j, binaryTournamentEdge o i j) + binaryTournamentEdge o

theorem binaryTournamentLaplacian_one {n : ℕ} (o : Fin n → Fin n → ZMod 2) :
    binaryTournamentLaplacian o *ᵥ 1 = 0 := by
  rw [binaryTournamentLaplacian, add_mulVec]
  ext i
  simp [mulVec, dotProduct, diagonal, CharTwo.add_self_eq_zero]

/-- Quadratic reciprocity's binary matrix pattern is precisely tournament complementation. -/
theorem binaryTournamentLaplacian_reciprocity {n : ℕ} (o : Fin n → Fin n → ZMod 2) :
    binaryTournamentLaplacian o + (binaryTournamentLaplacian o)ᵀ =
      1 + vecMulVec (1 : Fin n → ZMod 2) 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.add_apply, transpose_apply, one_apply_eq, vecMulVec,
      Pi.one_apply, mul_one, of_apply, CharTwo.add_self_eq_zero]
  · have hji : j ≠ i := Ne.symm hij
    simp only [binaryTournamentLaplacian, Matrix.add_apply, transpose_apply,
      diagonal_apply_ne _ hij, diagonal_apply_ne _ hji, zero_add,
      one_apply_ne hij, vecMulVec, Pi.one_apply, mul_one, of_apply, binaryTournamentEdge,
      if_neg hij, if_neg hji]
    rcases lt_or_gt_of_ne hij with h | h
    · rw [if_pos h, if_neg (not_lt.mpr h.le)]
      calc o i j + (1 + o i j) = 1 + (o i j + o i j) := by abel
           _ = 1 := by rw [CharTwo.add_self_eq_zero, add_zero]
    · rw [if_neg (not_lt.mpr h.le), if_pos h]
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

section Splitting
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def augmentation (x : ι → ZMod 2) : ZMod 2 := ∑ i, x i

omit [DecidableEq ι] in
private theorem augmentation_add (x y : ι → ZMod 2) :
    augmentation (x + y) = augmentation x + augmentation y := sum_add_distrib

omit [DecidableEq ι] in
private theorem augmentation_const (hcard : (Fintype.card ι : ZMod 2) = 1)
    (t : ZMod 2) : augmentation (t • (1 : ι → ZMod 2)) = t := by
  simp only [augmentation, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one,
    sum_const, nsmul_eq_mul, card_univ, hcard, one_mul]

omit [Fintype ι] [DecidableEq ι] in
private theorem matrix_double (A : Matrix ι ι (ZMod 2)) : A + A = 0 := by
  ext i j
  exact CharTwo.add_self_eq_zero (A i j)

omit [Fintype ι] [DecidableEq ι] in
private theorem vector_double (x : ι → ZMod 2) : x + x = 0 := by
  ext i
  exact CharTwo.add_self_eq_zero (x i)

omit [Fintype ι] in
private theorem shift_eq_transpose_add_constants (A : Matrix ι ι (ZMod 2))
    (hrec : A + Aᵀ = 1 + vecMulVec (1 : ι → ZMod 2) 1) :
    A + 1 = Aᵀ + vecMulVec (1 : ι → ZMod 2) 1 := by
  calc A + 1 = (A + Aᵀ) + (Aᵀ + 1) := by
         rw [add_assoc A Aᵀ (Aᵀ + 1), ← add_assoc Aᵀ Aᵀ 1,
           matrix_double, zero_add]
       _ = (1 + vecMulVec (1 : ι → ZMod 2) 1) + (Aᵀ + 1) := by rw [hrec]
       _ = (Aᵀ + vecMulVec (1 : ι → ZMod 2) 1) + (1 + 1) := by abel
       _ = _ := by rw [matrix_double, add_zero]

private theorem shift_apply (A : Matrix ι ι (ZMod 2))
    (hrec : A + Aᵀ = 1 + vecMulVec (1 : ι → ZMod 2) 1) (x : ι → ZMod 2) :
    (A + 1) *ᵥ x = Aᵀ *ᵥ x + augmentation x • (1 : ι → ZMod 2) := by
  rw [shift_eq_transpose_add_constants A hrec, add_mulVec]
  congr 1
  ext i
  simp only [mulVec, dotProduct, vecMulVec, of_apply, Pi.one_apply, mul_one, one_mul,
    Pi.smul_apply, smul_eq_mul, augmentation]

private theorem transpose_one (A : Matrix ι ι (ZMod 2))
    (hrow : A *ᵥ 1 = 0)
    (hrec : A + Aᵀ = 1 + vecMulVec (1 : ι → ZMod 2) 1)
    (hcard : (Fintype.card ι : ZMod 2) = 1) : Aᵀ *ᵥ 1 = 0 := by
  have h := shift_apply A hrec 1
  have hc : augmentation (1 : ι → ZMod 2) = 1 := by
    simp only [augmentation, Pi.one_apply, sum_const, card_univ, nsmul_eq_mul,
      mul_one, hcard]
  rw [add_mulVec, hrow, zero_add, one_mulVec, hc, one_smul] at h
  exact add_right_cancel (h.symm.trans (zero_add (1 : ι → ZMod 2)).symm)

omit [DecidableEq ι] in
private theorem augmentation_mulVec (A : Matrix ι ι (ZMod 2))
    (hcol : Aᵀ *ᵥ 1 = 0) (x : ι → ZMod 2) : augmentation (A *ᵥ x) = 0 := by
  have hc (j : ι) : ∑ i, A i j = 0 := by
    have h := congrFun hcol j
    simpa only [mulVec, dotProduct, transpose_apply, Pi.one_apply, mul_one,
      Pi.zero_apply] using h
  simp only [augmentation, mulVec, dotProduct]
  rw [sum_comm]
  simp only [← sum_mul, hc, zero_mul, sum_const_zero]

private theorem shifted_kernel_augmentation (A : Matrix ι ι (ZMod 2))
    (hcol : Aᵀ *ᵥ 1 = 0) (x : ι → ZMod 2) (hx : (A + 1) *ᵥ x = 0) :
    augmentation x = 0 := by
  have h := congrArg augmentation hx
  rw [add_mulVec, one_mulVec, augmentation_add, augmentation_mulVec A hcol,
    zero_add] at h
  simpa only [augmentation, Pi.zero_apply, sum_const_zero] using h

omit [DecidableEq ι] in
private theorem augmentation_smul (t : ZMod 2) (x : ι → ZMod 2) :
    augmentation (t • x) = t * augmentation x := by
  simp only [augmentation, Pi.smul_apply, smul_eq_mul, mul_sum]

private def binaryKernelSplit (A : Matrix ι ι (ZMod 2))
    (hrow : A *ᵥ 1 = 0)
    (hrec : A + Aᵀ = 1 + vecMulVec (1 : ι → ZMod 2) 1)
    (hcard : (Fintype.card ι : ZMod 2) = 1) :
    LinearMap.ker Aᵀ.mulVecLin ≃ₗ[ZMod 2]
      LinearMap.ker (A + 1).mulVecLin × ZMod 2 := by
  have hcol := transpose_one A hrow hrec hcard
  have hc (x : ι → ZMod 2) (hx : Aᵀ *ᵥ x = 0) :
      (A + 1) *ᵥ (x + augmentation x • (1 : ι → ZMod 2)) = 0 := by
    rw [shift_apply A hrec, augmentation_add, augmentation_const hcard,
      CharTwo.add_self_eq_zero, zero_smul, add_zero, mulVec_add, mulVec_smul,
      hx, hcol, smul_zero, add_zero]
  have ht (x : ι → ZMod 2) (hx : (A + 1) *ᵥ x = 0) : Aᵀ *ᵥ x = 0 := by
    have h := shift_apply A hrec x
    rw [hx, shifted_kernel_augmentation A hcol x hx, zero_smul, add_zero] at h
    exact h.symm
  refine
    { toFun := fun x => (⟨x.val + augmentation x.val • 1, hc x.val x.property⟩,
          augmentation x.val)
      invFun := fun z => ⟨z.1.val + z.2 • 1, by
        change Aᵀ *ᵥ (z.1.val + z.2 • 1) = 0
        rw [mulVec_add, mulVec_smul, ht z.1.val z.1.property, hcol,
          smul_zero, add_zero]⟩
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_
      map_smul' := ?_ }
  · intro x y
    apply Prod.ext
    · apply Subtype.ext
      change (x.val + y.val) + augmentation (x.val + y.val) • 1 =
        (x.val + augmentation x.val • 1) + (y.val + augmentation y.val • 1)
      rw [augmentation_add, add_smul]
      abel
    · exact augmentation_add x.val y.val
  · intro t x
    apply Prod.ext
    · apply Subtype.ext
      change t • x.val + augmentation (t • x.val) • 1 =
        t • (x.val + augmentation x.val • 1)
      rw [augmentation_smul, smul_add, smul_smul]
    · exact augmentation_smul t x.val
  · intro x
    apply Subtype.ext
    change (x.val + augmentation x.val • 1) + augmentation x.val • 1 = x.val
    rw [add_assoc, vector_double, add_zero]
  · intro z
    have hz : augmentation z.1.val = 0 := shifted_kernel_augmentation A hcol _ z.1.property
    apply Prod.ext
    · apply Subtype.ext
      change (z.1.val + z.2 • 1) + augmentation (z.1.val + z.2 • 1) • 1 = z.1.val
      rw [augmentation_add, hz, zero_add, augmentation_const hcard,
        add_assoc, vector_double, add_zero]
    · change augmentation (z.1.val + z.2 • 1) = z.2
      rw [augmentation_add, hz, zero_add, augmentation_const hcard]

private theorem rank_shift_of_reciprocity (A : Matrix ι ι (ZMod 2))
    (hrow : A *ᵥ 1 = 0)
    (hrec : A + Aᵀ = 1 + vecMulVec (1 : ι → ZMod 2) 1)
    (hcard : (Fintype.card ι : ZMod 2) = 1) : (A + 1).rank = A.rank + 1 := by
  have hk := (binaryKernelSplit A hrow hrec hcard).finrank_eq
  rw [Module.finrank_prod, Module.finrank_self] at hk
  have hA := LinearMap.finrank_range_add_finrank_ker Aᵀ.mulVecLin
  have hB := LinearMap.finrank_range_add_finrank_ker (A + 1).mulVecLin
  change Aᵀ.rank + Module.finrank (ZMod 2) (LinearMap.ker Aᵀ.mulVecLin) = _ at hA
  change (A + 1).rank + Module.finrank (ZMod 2) (LinearMap.ker (A + 1).mulVecLin) = _ at hB
  rw [rank_transpose] at hA
  omega

end Splitting

private theorem oddBinaryCard (m : ℕ) :
    (Fintype.card (Fin (2 * m + 1)) : ZMod 2) = 1 := by
  have htwo : (2 : ZMod 2) = 0 := CharP.cast_eq_zero (ZMod 2) 2
  simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_one, htwo, zero_mul, zero_add]

/-- Every odd binary tournament Laplacian gains exactly one rank after adding identity. -/
theorem binaryTournamentLaplacian_rank_shift (m : ℕ)
    (o : Fin (2 * m + 1) → Fin (2 * m + 1) → ZMod 2) :
    (binaryTournamentLaplacian o + 1).rank = (binaryTournamentLaplacian o).rank + 1 := by
  apply rank_shift_of_reciprocity _ (binaryTournamentLaplacian_one o)
    (binaryTournamentLaplacian_reciprocity o)
  exact oddBinaryCard m

/-- Full rank after the shift is equivalent to maximal possible unshifted rank. -/
theorem binaryTournamentLaplacian_shift_full_rank_iff (m : ℕ)
    (o : Fin (2 * m + 1) → Fin (2 * m + 1) → ZMod 2) :
    (binaryTournamentLaplacian o + 1).rank = 2 * m + 1 ↔
      (binaryTournamentLaplacian o).rank = 2 * m := by
  rw [binaryTournamentLaplacian_rank_shift]
  omega

open GaloisForLFunctions.HTGeometry.LinearAlgebra

/-- Odd tournament reciprocity gives the existing Selmer shear with constant coefficient. -/
theorem binaryTournamentLaplacian_reciprocity_shear {n : ℕ}
    (o : Fin n → Fin n → ZMod 2) :
    binaryTournamentLaplacian o + (binaryTournamentLaplacian o)ᵀ =
      binarySelmerShear 1 := binaryTournamentLaplacian_reciprocity o

private theorem binarySelmerShear_one_apply {n : ℕ} (x : Fin n → ZMod 2) :
    binarySelmerShear 1 *ᵥ x = x + augmentation x • 1 := by
  simpa only [dotProduct, Pi.one_apply, one_mul, augmentation] using
    binarySelmerShear_mulVec (1 : Fin n → ZMod 2) x

/-- On odd dimension the Selmer shear is a projection, replacing the even-parity involution. -/
theorem binarySelmerShear_one_idempotent (m : ℕ) :
    (binarySelmerShear (1 : Fin (2 * m + 1) → ZMod 2)) ^ 2 = binarySelmerShear 1 := by
  have hd : (1 : Fin (2 * m + 1) → ZMod 2) ⬝ᵥ 1 = 1 := by
    simpa only [dotProduct, Pi.one_apply, one_mul, sum_const, card_univ,
      nsmul_eq_mul, mul_one] using oddBinaryCard m
  have hJ : (vecMulVec 1 1 : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) (ZMod 2)) *
      vecMulVec 1 1 = vecMulVec 1 1 := by
    rw [vecMulVec_mul_vecMulVec, hd, one_smul]
  simp only [pow_two, binarySelmerShear, mul_add, add_mul, one_mul, mul_one, hJ]
  rw [matrix_double, add_zero]

/-- Its kernel consists exactly of constants; no parity premise is left unresolved. -/
theorem binarySelmerShear_one_kernel (m : ℕ) (x : Fin (2 * m + 1) → ZMod 2) :
    binarySelmerShear 1 *ᵥ x = 0 ↔ ∃ t : ZMod 2, x = t • 1 := by
  rw [binarySelmerShear_one_apply]
  constructor
  · intro hx
    refine ⟨augmentation x, ?_⟩
    have h := congrArg (fun y => y + augmentation x • 1) hx
    simpa only [add_assoc, vector_double, add_zero, zero_add] using h
  · rintro ⟨t, rfl⟩
    rw [augmentation_const (oddBinaryCard m), vector_double]

#print axioms binaryTournamentLaplacian_rank_shift
#print axioms binaryTournamentLaplacian_shift_full_rank_iff
#print axioms binarySelmerShear_one_idempotent
#print axioms binarySelmerShear_one_kernel

end
end GaloisForLFunctions.ArithmeticCorrespondencePositivity
