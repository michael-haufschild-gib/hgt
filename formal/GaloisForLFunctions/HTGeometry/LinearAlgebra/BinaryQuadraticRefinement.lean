import GaloisForLFunctions.HTGeometry.LinearAlgebra.AlternatingMatrixRank
import GaloisForLFunctions.HTGeometry.MatrixRankSubadditive
import GaloisForLFunctions.HTGeometry.ChainRankStabilization
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.CharP.Two

/-!
# Canonical alternating correction over the binary field

For a symmetric matrix with diagonal vector `d`, adding `d dᵀ` produces an
alternating matrix. This preserves the original kernel and rounds the rank down
to the nearest even integer. The correction commutes with arbitrary linear pullback.
-/

namespace GaloisForLFunctions.HTGeometry.LinearAlgebra
open Matrix Module
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- In characteristic two over the prime field, the quadratic evaluation of a
symmetric matrix is the linear functional represented by its diagonal. -/
theorem binary_symmetric_quadratic (M : Matrix ι ι (ZMod 2)) (hM : M.IsSymm)
    (v : ι → ZMod 2) : v ⬝ᵥ (M *ᵥ v) = (fun i => M i i) ⬝ᵥ v := by
  have hcross (x y : ι → ZMod 2) : x ⬝ᵥ (M *ᵥ y) = y ⬝ᵥ (M *ᵥ x) := by
    conv_lhs => rw [← hM]
    rw [mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec]
  let q : (ι → ZMod 2) →+ ZMod 2 :=
    { toFun := fun x => x ⬝ᵥ (M *ᵥ x)
      map_zero' := by simp
      map_add' := by
        intro x y
        rw [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, hcross x y]
        calc
          (x ⬝ᵥ (M *ᵥ x) + y ⬝ᵥ (M *ᵥ x)) +
              (y ⬝ᵥ (M *ᵥ x) + y ⬝ᵥ (M *ᵥ y)) =
              (x ⬝ᵥ (M *ᵥ x) + y ⬝ᵥ (M *ᵥ y)) +
                (y ⬝ᵥ (M *ᵥ x) + y ⬝ᵥ (M *ᵥ x)) := by abel
          _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero] }
  have hs (i : ι) (a : ZMod 2) : q (Pi.single i a) = M i i * a := by
    change (Pi.single i a) ⬝ᵥ (M *ᵥ Pi.single i a) = _
    simp [dotProduct, mulVec, Pi.single_apply]
    calc
      a * (M i i * a) = M i i * a ^ 2 := by ring
      _ = _ := by rw [ZMod.pow_card]
  have hv : ∑ i, Pi.single i (v i) = v := by
    ext i
    simp [Pi.single_apply]
  change q v = _
  rw [← hv, map_sum]
  change ∑ i, q (Pi.single i (v i)) = _
  simp only [hs]
  rw [hv]
  rfl

/-- The canonical alternating correction of a binary symmetric matrix. -/
def binaryAlternatingRepair (M : Matrix ι ι (ZMod 2)) : Matrix ι ι (ZMod 2) :=
  M + vecMulVec (fun i => M i i) (fun i => M i i)

theorem isAlternatingMatrix_binaryAlternatingRepair (M : Matrix ι ι (ZMod 2))
    (hM : M.IsSymm) : IsAlternatingMatrix (binaryAlternatingRepair M) := by
  intro v
  rw [binaryAlternatingRepair, add_mulVec, dotProduct_add, binary_symmetric_quadratic M hM,
    vecMulVec_mulVec, dotProduct_smul]
  change (fun i => M i i) ⬝ᵥ v +
    (v ⬝ᵥ fun i => M i i) * ((fun i => M i i) ⬝ᵥ v) = 0
  rw [dotProduct_comm v, ← sq, ZMod.pow_card, CharTwo.add_self_eq_zero]

/-- The original kernel is preserved by the canonical correction. -/
theorem ker_le_binaryAlternatingRepair (M : Matrix ι ι (ZMod 2)) (hM : M.IsSymm) :
    M.mulVecLin.ker ≤ (binaryAlternatingRepair M).mulVecLin.ker := by
  intro v hv
  have hd : (fun i => M i i) ⬝ᵥ v = 0 := by
    rw [← binary_symmetric_quadratic M hM, show M *ᵥ v = 0 from hv, dotProduct_zero]
  change binaryAlternatingRepair M *ᵥ v = 0
  rw [binaryAlternatingRepair, add_mulVec, show M *ᵥ v = 0 from hv,
    vecMulVec_mulVec, hd]
  ext i
  change 0 + M i i * 0 = 0
  rw [mul_zero, add_zero]

#print axioms binary_symmetric_quadratic
#print axioms isAlternatingMatrix_binaryAlternatingRepair
#print axioms ker_le_binaryAlternatingRepair
end GaloisForLFunctions.HTGeometry.LinearAlgebra

namespace GaloisForLFunctions.HTGeometry.LinearAlgebra
open Matrix Module
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Canonical correction removes exactly the odd unit of rank. -/
theorem rank_binaryAlternatingRepair (M : Matrix ι ι (ZMod 2)) (hM : M.IsSymm) :
    (binaryAlternatingRepair M).rank = M.rank - M.rank % 2 := by
  have hk := Submodule.finrank_mono (ker_le_binaryAlternatingRepair M hM)
  have hMdim := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have hRdim := LinearMap.finrank_range_add_finrank_ker (binaryAlternatingRepair M).mulVecLin
  change M.rank + _ = _ at hMdim
  change (binaryAlternatingRepair M).rank + _ = _ at hRdim
  have hle : (binaryAlternatingRepair M).rank ≤ M.rank := by omega
  let d : ι → ZMod 2 := fun i => M i i
  have hundo : binaryAlternatingRepair M + vecMulVec d d = M := by
    have hd : vecMulVec d d + vecMulVec d d = (0 : Matrix ι ι (ZMod 2)) := by
      ext i j
      exact CharTwo.add_self_eq_zero _
    change (M + vecMulVec d d) + vecMulVec d d = M
    rw [add_assoc, hd, add_zero]
  have hbound := rank_add_le_rank_add_rank (binaryAlternatingRepair M) (vecMulVec d d)
  rw [hundo] at hbound
  have houter := rank_vecMulVec_le d d
  obtain ⟨r, hr⟩ := (isAlternatingMatrix_binaryAlternatingRepair M hM).even_rank
  omega

/-- The nullity increases by one exactly when the original rank is odd. -/
theorem nullity_binaryAlternatingRepair (M : Matrix ι ι (ZMod 2)) (hM : M.IsSymm) :
    finrank (ZMod 2) (binaryAlternatingRepair M).mulVecLin.ker =
      finrank (ZMod 2) M.mulVecLin.ker + M.rank % 2 := by
  have hMdim := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have hRdim := LinearMap.finrank_range_add_finrank_ker (binaryAlternatingRepair M).mulVecLin
  change M.rank + _ = _ at hMdim
  change (binaryAlternatingRepair M).rank + _ = _ at hRdim
  rw [rank_binaryAlternatingRepair M hM] at hRdim
  have hmod := Nat.mod_le M.rank 2
  omega

/-- Identity matrices exhibit the parity correction in every dimension. -/
theorem rank_binaryAlternatingRepair_one :
    (binaryAlternatingRepair (1 : Matrix ι ι (ZMod 2))).rank =
      Fintype.card ι - Fintype.card ι % 2 := by
  rw [rank_binaryAlternatingRepair _ (by exact Matrix.isSymm_one), rank_one]

#print axioms rank_binaryAlternatingRepair
#print axioms nullity_binaryAlternatingRepair
#print axioms rank_binaryAlternatingRepair_one
end GaloisForLFunctions.HTGeometry.LinearAlgebra

namespace GaloisForLFunctions.HTGeometry.LinearAlgebra
open Matrix Module
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The rank-one diagonal repair has rank zero or one, with no exceptional isotropic case. -/
theorem rank_binary_outer (d : ι → ZMod 2) :
    (vecMulVec d d).rank = if d = 0 then 0 else 1 := by
  classical
  by_cases hd : d = 0
  · subst d
    rw [if_pos rfl]
    change (0 : Matrix ι ι (ZMod 2)).rank = 0
    exact rank_zero
  · rw [if_neg hd]
    have hle := rank_vecMulVec_le d d
    have hne : vecMulVec d d ≠ (0 : Matrix ι ι (ZMod 2)) := by
      intro h
      apply hd
      funext i
      change d i = 0
      have hi := congrArg (fun M : Matrix ι ι (ZMod 2) => M i i) h
      change d i * d i = 0 at hi
      simpa only [← sq, ZMod.pow_card] using hi
    have hnrank := mt (DiffOp.rank_eq_zero_iff (vecMulVec d d)).mp hne
    omega

/-- Alternating matrices have zero diagonal. -/
theorem IsAlternatingMatrix.diagonal_zero {M : Matrix ι ι (ZMod 2)}
    (hM : IsAlternatingMatrix M) : (fun i => M i i) = 0 := by
  funext i
  have h := hM (Pi.single i 1)
  simpa [dotProduct, mulVec, Pi.single_apply] using h

omit [Fintype ι] [DecidableEq ι] in
/-- The canonical correction kills the diagonal for every binary matrix. -/
theorem binaryAlternatingRepair_diagonal (M : Matrix ι ι (ZMod 2)) :
    (fun i => binaryAlternatingRepair M i i) = 0 := by
  funext i
  change M i i + M i i * M i i = 0
  rw [← sq, ZMod.pow_card, CharTwo.add_self_eq_zero]

omit [Fintype ι] [DecidableEq ι] in
/-- Canonical correction is idempotent, even without symmetry. -/
theorem binaryAlternatingRepair_idempotent (M : Matrix ι ι (ZMod 2)) :
    binaryAlternatingRepair (binaryAlternatingRepair M) = binaryAlternatingRepair M := by
  rw [binaryAlternatingRepair, binaryAlternatingRepair_diagonal]
  simp [vecMulVec]
  rfl

/-- The correction vanishes exactly when the original symmetric matrix is alternating. -/
theorem binaryAlternatingRepair_eq_self_iff (M : Matrix ι ι (ZMod 2)) (hM : M.IsSymm) :
    binaryAlternatingRepair M = M ↔ IsAlternatingMatrix M := by
  constructor
  · intro h
    rw [← h]
    exact isAlternatingMatrix_binaryAlternatingRepair M hM
  · intro h
    rw [binaryAlternatingRepair, h.diagonal_zero]
    simp [vecMulVec]
    rfl

#print axioms rank_binary_outer
#print axioms binaryAlternatingRepair_idempotent
#print axioms binaryAlternatingRepair_eq_self_iff
end GaloisForLFunctions.HTGeometry.LinearAlgebra

namespace GaloisForLFunctions.HTGeometry.LinearAlgebra
open Matrix
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The diagonal obstruction transforms as a covector under arbitrary linear pullback. -/
theorem binaryDiagonal_congruence (M : Matrix ι ι (ZMod 2)) (hM : M.IsSymm)
    (S : Matrix ι κ (ZMod 2)) :
    (fun i => (Sᵀ * M * S) i i) = Sᵀ *ᵥ (fun i => M i i) := by
  have hc (v : κ → ZMod 2) :
      v ⬝ᵥ ((Sᵀ * M * S) *ᵥ v) = (S *ᵥ v) ⬝ᵥ (M *ᵥ (S *ᵥ v)) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, mulVec_transpose,
      dotProduct_comm, ← dotProduct_mulVec, dotProduct_comm]
  have hf (v : κ → ZMod 2) :
      (fun i => M i i) ⬝ᵥ (S *ᵥ v) = (Sᵀ *ᵥ fun i => M i i) ⬝ᵥ v := by
    rw [dotProduct_mulVec, ← mulVec_transpose]
  funext i
  have h := (hc (Pi.single i 1)).trans
    ((binary_symmetric_quadratic M hM (S *ᵥ Pi.single i 1)).trans (hf (Pi.single i 1)))
  simpa [dotProduct, mulVec, Pi.single_apply] using h

/-- Canonical alternating correction commutes with every linear pullback. -/
theorem binaryAlternatingRepair_congruence (M : Matrix ι ι (ZMod 2)) (hM : M.IsSymm)
    (S : Matrix ι κ (ZMod 2)) :
    binaryAlternatingRepair (Sᵀ * M * S) = Sᵀ * binaryAlternatingRepair M * S := by
  rw [binaryAlternatingRepair, binaryDiagonal_congruence M hM S,
    binaryAlternatingRepair, Matrix.mul_add, Matrix.add_mul, mul_vecMulVec, vecMulVec_mul,
    ← mulVec_transpose]

#print axioms binaryDiagonal_congruence
#print axioms binaryAlternatingRepair_congruence
end GaloisForLFunctions.HTGeometry.LinearAlgebra

namespace GaloisForLFunctions.HTGeometry.LinearAlgebra
open Matrix Module
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem binary_det_ne_zero_iff_nullity_zero (M : Matrix ι ι (ZMod 2)) :
    M.det ≠ 0 ↔ finrank (ZMod 2) M.mulVecLin.ker = 0 := by
  rw [Submodule.finrank_eq_zero, LinearMap.ker_eq_bot]
  change M.det ≠ 0 ↔ Function.Injective M.mulVec
  rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

/-- Nonsingularity survives exactly in even dimension. -/
theorem binaryAlternatingRepair_det_ne_zero_iff (M : Matrix ι ι (ZMod 2)) (hM : M.IsSymm) :
    (binaryAlternatingRepair M).det ≠ 0 ↔ M.det ≠ 0 ∧ Fintype.card ι % 2 = 0 := by
  rw [binary_det_ne_zero_iff_nullity_zero, binary_det_ne_zero_iff_nullity_zero]
  have hn := nullity_binaryAlternatingRepair M hM
  have hr := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  change M.rank + _ = _ at hr
  simp only [Module.finrank_fintype_fun_eq_card] at hr
  omega

/-- Correction preserves the determinant in even dimension and kills it in odd dimension. -/
theorem det_binaryAlternatingRepair (M : Matrix ι ι (ZMod 2)) (hM : M.IsSymm) :
    (binaryAlternatingRepair M).det = if Fintype.card ι % 2 = 0 then M.det else 0 := by
  have hi := binaryAlternatingRepair_det_ne_zero_iff M hM
  by_cases he : Fintype.card ι % 2 = 0
  · rw [if_pos he]
    by_cases hs : M.det = 0
    · have hc : (binaryAlternatingRepair M).det = 0 := by
        by_contra hc
        exact (hi.mp hc).1 hs
      rw [hc, hs]
    · have hc := hi.mpr ⟨hs, he⟩
      have hone {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
        simpa using ZMod.pow_card_sub_one_eq_one hx
      exact (hone hc).trans (hone hs).symm
  · rw [if_neg he]
    by_contra h
    exact he (hi.mp h).2

#print axioms binaryAlternatingRepair_det_ne_zero_iff
#print axioms det_binaryAlternatingRepair
end GaloisForLFunctions.HTGeometry.LinearAlgebra
