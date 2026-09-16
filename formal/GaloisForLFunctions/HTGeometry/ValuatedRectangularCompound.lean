import GaloisForLFunctions.HTGeometry.MatrixCompound
import Mathlib.RingTheory.Valuation.Basic

/-!
# Valuated rectangular compound matrices

Rectangular compound matrices give the subset-indexed Cauchy--Binet formula without factorial
multiplicities. Applying a nonarchimedean valuation proves the integral-column-combination rule:
right multiplication by coefficients of value at most one cannot increase the largest valued
minor. This is the multiplicative, order-dual form of the second rule in the k-server paper's
minor-valuation lemma.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix Module

section RectangularCompound

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
  [Fintype κ] [DecidableEq κ] [LinearOrder κ]
  {R : Type*} [CommRing R]

/-- The `k`-th compound of a rectangular matrix. -/
noncomputable def rectangularCompound (k : ℕ) (A : Matrix ι κ R) :
    Matrix (Set.powersetCard ι k) (Set.powersetCard κ k) R :=
  LinearMap.toMatrix ((Pi.basisFun R κ).exteriorPower k) ((Pi.basisFun R ι).exteriorPower k)
    (exteriorPower.map k (Matrix.toLin (Pi.basisFun R κ) (Pi.basisFun R ι) A))

omit [DecidableEq ι] [LinearOrder ι] [LinearOrder κ] in
theorem basisFun_coord_toLin_rectangular (A : Matrix ι κ R) (i : ι) (j : κ) :
    (Pi.basisFun R ι).coord i
      (Matrix.toLin (Pi.basisFun R κ) (Pi.basisFun R ι) A ((Pi.basisFun R κ) j)) = A i j := by
  have h := LinearMap.toMatrix_apply (Pi.basisFun R κ) (Pi.basisFun R ι)
    (Matrix.toLin (Pi.basisFun R κ) (Pi.basisFun R ι) A) i j
  rw [LinearMap.toMatrix_toLin] at h
  exact h.symm

omit [DecidableEq ι] in
/-- The entries of a rectangular compound are the corresponding minors. -/
theorem rectangularCompound_apply (k : ℕ) (A : Matrix ι κ R)
    (s : Set.powersetCard ι k) (t : Set.powersetCard κ k) :
    rectangularCompound k A s t =
      (Matrix.of fun i j => A (subsetEnum s j) (subsetEnum t i)).det := by
  classical
  rw [rectangularCompound, LinearMap.toMatrix_apply, exteriorPower.basis_apply,
    exteriorPower.map_apply_ιMulti_family, exteriorPower.basis_repr_apply,
    show exteriorPower.ιMulti_family R k
      (⇑(Matrix.toLin (Pi.basisFun R κ) (Pi.basisFun R ι) A) ∘ ⇑(Pi.basisFun R κ)) t
      = exteriorPower.ιMulti R k
        (fun i => Matrix.toLin (Pi.basisFun R κ) (Pi.basisFun R ι) A
          ((Pi.basisFun R κ) (subsetEnum t i))) from rfl,
    exteriorPower.ιMultiDual_apply_ιMulti]
  congr 1
  ext i j
  exact basisFun_coord_toLin_rectangular A _ _

variable {τ : Type*} [Fintype τ] [DecidableEq τ] [LinearOrder τ]

omit [DecidableEq ι] in
/-- **Rectangular Cauchy--Binet.** Taking compounds commutes with matrix multiplication. -/
theorem rectangularCompound_mul (k : ℕ) (A : Matrix ι κ R) (B : Matrix κ τ R) :
    rectangularCompound k (A * B) = rectangularCompound k A * rectangularCompound k B := by
  rw [rectangularCompound, rectangularCompound, rectangularCompound,
    Matrix.toLin_mul (Pi.basisFun R τ) (Pi.basisFun R κ) (Pi.basisFun R ι),
    exteriorPower.map_comp, LinearMap.toMatrix_comp _ ((Pi.basisFun R κ).exteriorPower k)]

end RectangularCompound

section ValuatedRectangularCompound

variable {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

/-- The valuation of a block-triangular determinant factors through its diagonal blocks.
The block-diagonal rule is the specialization with `B = 0`. -/
theorem valuation_det_fromBlocks_zero₂₁
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (val : Valuation K Γ) (A : Matrix ι ι K) (B : Matrix ι κ K)
    (D : Matrix κ κ K) :
    val (Matrix.fromBlocks A B 0 D).det = val A.det * val D.det := by
  rw [Matrix.det_fromBlocks_zero₂₁, Valuation.map_mul]

/-- A determinant of entries in the valuation ring also lies in the valuation ring. -/
theorem valuation_det_le_one_of_entries {ι : Type*} [Fintype ι] [DecidableEq ι]
    (val : Valuation K Γ) (A : Matrix ι ι K) (hA : ∀ i j, val (A i j) ≤ 1) :
    val A.det ≤ 1 := by
  classical
  rw [Matrix.det_apply']
  refine Valuation.map_sum_le val fun σ _ => ?_
  rw [Valuation.map_mul, map_prod]
  have hsign : val (((Equiv.Perm.sign σ : ℤ) : K)) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> simp
  rw [hsign, one_mul]
  exact Finset.prod_le_one
    (fun i _ => show (0 : Γ) ≤ val (A (σ i) i) from zero_le)
    fun i _ => hA (σ i) i

/-- Every compound entry of a valuation-integral matrix is valuation-integral. -/
theorem valuation_rectangularCompound_le_one_of_entries
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    [Fintype κ] [DecidableEq κ] [LinearOrder κ]
    (val : Valuation K Γ) (k : ℕ) (A : Matrix ι κ K)
    (hA : ∀ i j, val (A i j) ≤ 1)
    (s : Set.powersetCard ι k) (t : Set.powersetCard κ k) :
    val (rectangularCompound k A s t) ≤ 1 := by
  rw [rectangularCompound_apply]
  apply valuation_det_le_one_of_entries
  intro i j
  exact hA _ _

/-- Largest multiplicative valuation among all `k × k` minors. -/
noncomputable def maximalCompoundValue
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [LinearOrder ι] [DecidableEq κ] [LinearOrder κ]
    (val : Valuation K Γ) (k : ℕ) (A : Matrix ι κ K) : Γ :=
  Finset.univ.sup fun s => Finset.univ.sup fun t => val (rectangularCompound k A s t)

/-- **Integral column combinations cannot improve the maximal minor value.** This is the
multiplicative, order-dual form of `μ(A B) ≥ μ(A)` from the paper. -/
theorem maximalCompoundValue_mul_right_le
    {ι κ τ : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    [Fintype κ] [DecidableEq κ] [LinearOrder κ]
    [Fintype τ] [DecidableEq τ] [LinearOrder τ]
    (val : Valuation K Γ) (k : ℕ) (A : Matrix ι κ K) (B : Matrix κ τ K)
    (hB : ∀ i j, val (B i j) ≤ 1) :
    maximalCompoundValue val k (A * B) ≤ maximalCompoundValue val k A := by
  unfold maximalCompoundValue
  refine Finset.sup_le fun s _ => Finset.sup_le fun t _ => ?_
  rw [rectangularCompound_mul, Matrix.mul_apply]
  refine Valuation.map_sum_le val fun u _ => ?_
  rw [Valuation.map_mul]
  calc
    val (rectangularCompound k A s u) * val (rectangularCompound k B u t)
        ≤ val (rectangularCompound k A s u) * 1 :=
      mul_le_mul' le_rfl
        (valuation_rectangularCompound_le_one_of_entries val k B hB u t)
    _ = val (rectangularCompound k A s u) := mul_one _
    _ ≤ Finset.univ.sup fun s => Finset.univ.sup fun t =>
        val (rectangularCompound k A s t) :=
      Finset.le_sup_of_le (Finset.mem_univ s)
        (Finset.le_sup_of_le (Finset.mem_univ u) le_rfl)

end ValuatedRectangularCompound

end GaloisForLFunctions.HTGeometry
