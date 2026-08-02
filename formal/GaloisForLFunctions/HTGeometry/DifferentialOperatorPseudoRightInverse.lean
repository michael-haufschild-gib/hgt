import GaloisForLFunctions.HTGeometry.DifferentialOperatorOreField
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# The pseudodifferential right inverse

A matrix over `K[∂;δ]` whose rows are left independent has a right inverse over the skew field of
rational pseudodifferential operators:

`P · Q = I`.

The row map `v ↦ v · P` is a map of left vector spaces over that skew field, injective because the
rows stay independent after clearing denominators.  An injective map of vector spaces over a
division ring has a left inverse, and every map between finite coordinate spaces is right
multiplication by a matrix, whose entries are the images of the standard vectors.
-/

open scoped Differential
open nonZeroDivisors

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]
variable {ι ι' : Type*} [Fintype ι] [Fintype ι']

/-- The row map of a matrix, as a map of left vector spaces over the skew field. -/
def pseudoVecMulSkewLin (P : ι' → ι → DiffOp K) :
    (ι' → PseudoDiffOp K) →ₗ[PseudoDiffOp K] (ι → PseudoDiffOp K) where
  toFun := pseudoVecMul P
  map_add' v w := by
    funext j
    show ∑ i, (v i + w i) * toPseudoMatrix P i j
      = (∑ i, v i * toPseudoMatrix P i j) + ∑ i, w i * toPseudoMatrix P i j
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => add_mul (v i) (w i) (toPseudoMatrix P i j)
  map_smul' r v := by
    funext j
    show ∑ i, (r * v i) * toPseudoMatrix P i j = r * ∑ i, v i * toPseudoMatrix P i j
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_assoc r (v i) (toPseudoMatrix P i j)

omit [Fintype ι] in
@[simp] theorem pseudoVecMulSkewLin_apply (P : ι' → ι → DiffOp K) (v : ι' → PseudoDiffOp K) :
    pseudoVecMulSkewLin P v = pseudoVecMul P v := rfl

omit [Fintype ι] in
/-- The row map sends a standard vector to the corresponding row. -/
theorem pseudoVecMul_single [DecidableEq ι'] (P : ι' → ι → DiffOp K) (a : ι') (j : ι) :
    pseudoVecMul P (Pi.single a (1 : PseudoDiffOp K)) j = toPseudoMatrix P a j := by
  show ∑ i, (Pi.single a (1 : PseudoDiffOp K) : ι' → PseudoDiffOp K) i * toPseudoMatrix P i j
      = toPseudoMatrix P a j
  rw [Finset.sum_eq_single a]
  · rw [Pi.single_apply, if_pos rfl, one_mul]
  · intro i _ hia
    rw [Pi.single_apply, if_neg hia, zero_mul]
  · intro hcon
    exact absurd (Finset.mem_univ a) hcon

omit [Fintype ι'] in
/-- Every linear map between finite coordinate spaces over the skew field is right multiplication
by the matrix of the images of the standard vectors. -/
theorem apply_eq_sum_single [DecidableEq ι]
    (g : (ι → PseudoDiffOp K) →ₗ[PseudoDiffOp K] (ι' → PseudoDiffOp K))
    (w : ι → PseudoDiffOp K) (b : ι') :
    g w b = ∑ j, w j * g (Pi.single j (1 : PseudoDiffOp K)) b := by
  have hw : ∑ j, w j • Pi.single j (1 : PseudoDiffOp K) = w := by
    refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) (Finset.univ_sum_single w)
    funext i
    rw [Pi.smul_apply, Pi.single_apply, Pi.single_apply, smul_eq_mul]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos hij, mul_one]
    · rw [if_neg hij, if_neg hij, mul_zero]
  calc g w b = g (∑ j, w j • Pi.single j (1 : PseudoDiffOp K)) b := by rw [hw]
    _ = ∑ j, w j * g (Pi.single j (1 : PseudoDiffOp K)) b := by
        rw [map_sum, Finset.sum_apply]
        exact Finset.sum_congr rfl fun j _ => by rw [map_smul]; rfl

/-- Right multiplication of a row vector by a matrix over the skew field. -/
def skewVecMul (Q : ι → ι' → PseudoDiffOp K) (w : ι → PseudoDiffOp K) : ι' → PseudoDiffOp K :=
  fun b => ∑ j, w j * Q j b

/-- **Inversion of the row map.**  A matrix whose rows are left independent over the operator ring
has a matrix over the skew field which recovers a coefficient vector from its row combination and
which is a right inverse of the matrix. -/
theorem exists_pseudo_inverse [DecidableEq ι] [DecidableEq ι'] (P : ι' → ι → DiffOp K)
    (hP : RowIndep P) :
    ∃ Q : ι → ι' → PseudoDiffOp K,
      (∀ v : ι' → PseudoDiffOp K, skewVecMul Q (pseudoVecMul P v) = v) ∧
        ∀ a b : ι', ∑ j, toPseudoMatrix P a j * Q j b = if a = b then 1 else 0 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (pseudoVecMulSkewLin P)
    (LinearMap.ker_eq_bot.mpr (pseudoVecMul_injective P hP))
  have hgf : ∀ v : ι' → PseudoDiffOp K, g (pseudoVecMul P v) = v := by
    intro v
    have hh := LinearMap.congr_fun hg v
    simpa using hh
  refine ⟨fun j b => g (Pi.single j (1 : PseudoDiffOp K)) b, fun v => ?_, fun a b => ?_⟩
  · funext b
    show ∑ j, pseudoVecMul P v j * g (Pi.single j (1 : PseudoDiffOp K)) b = v b
    rw [← apply_eq_sum_single g (pseudoVecMul P v) b, hgf v]
  · have hs : ∑ j, toPseudoMatrix P a j * g (Pi.single j (1 : PseudoDiffOp K)) b
        = ∑ j, pseudoVecMul P (Pi.single a (1 : PseudoDiffOp K)) j
            * g (Pi.single j (1 : PseudoDiffOp K)) b :=
      Finset.sum_congr rfl fun j _ => by rw [pseudoVecMul_single]
    rw [hs, ← apply_eq_sum_single g (pseudoVecMul P (Pi.single a (1 : PseudoDiffOp K))) b,
      hgf (Pi.single a (1 : PseudoDiffOp K)), Pi.single_apply]
    by_cases hab : a = b
    · rw [if_pos hab.symm, if_pos hab]
    · rw [if_neg fun h => hab h.symm, if_neg hab]

/-- **The pseudodifferential right inverse.**  A matrix whose rows are left independent over the
operator ring has a right inverse over the skew field of rational pseudodifferential operators. -/
theorem exists_pseudo_right_inverse [DecidableEq ι] [DecidableEq ι'] (P : ι' → ι → DiffOp K)
    (hP : RowIndep P) :
    ∃ Q : ι → ι' → PseudoDiffOp K,
      ∀ a b : ι', ∑ j, toPseudoMatrix P a j * Q j b = if a = b then 1 else 0 := by
  obtain ⟨Q, -, hQ⟩ := exists_pseudo_inverse P hP
  exact ⟨Q, hQ⟩

end

end DiffOp

end GaloisForLFunctions.HTGeometry
