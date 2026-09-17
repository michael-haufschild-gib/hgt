import GaloisForLFunctions.HTGeometry.SymmetricSquareDeterminantGeneral
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Full arbitrary-rank symmetric-square determinant

This module constructs the symmetric-square matrix on the unordered-pair basis, proves it is a
multiplicative representation, and computes its determinant on every invertible matrix over a
field. The transvection case is handled structurally: blocks are indexed by multiplicity of the
changed coordinate, making the matrix block triangular with identity diagonal blocks.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

noncomputable section

variable {ι R : Type*} [DecidableEq ι] [CommRing R]

/-- Coordinates of the commutative product of two linear forms. -/
def symmetricPairCoordinates (x y : ι → R) : Sym2 ι → R :=
  Sym2.lift ⟨fun i j => if i = j then x i * y i else x i * y j + x j * y i, by
    intro i j
    by_cases h : i = j
    · subst j
      simp
    · simp [h, Ne.symm h, add_comm]⟩

@[simp] theorem symmetricPairCoordinates_mk (x y : ι → R) (i j : ι) :
    symmetricPairCoordinates x y s(i, j) =
      if i = j then x i * y i else x i * y j + x j * y i := rfl

theorem symmetricPairCoordinates_comm (x y : ι → R) :
    symmetricPairCoordinates x y = symmetricPairCoordinates y x := by
  ext p
  induction p with
  | _ i j =>
      by_cases h : i = j
      · subst j
        simp [symmetricPairCoordinates, mul_comm]
      · simp [symmetricPairCoordinates, h, mul_comm, add_comm]

/-- Polarized coefficient coordinates; unlike `symmetricPairCoordinates`, the diagonal receives
both ordered contributions. -/
def polarPairCoordinates (x y : ι → R) : Sym2 ι → R :=
  Sym2.lift ⟨fun i j => x i * y j + x j * y i, by
    intro i j
    change x i * y j + x j * y i = x j * y i + x i * y j
    exact add_comm _ _⟩

omit [DecidableEq ι] in
@[simp] theorem polarPairCoordinates_mk (x y : ι → R) (i j : ι) :
    polarPairCoordinates x y s(i, j) = x i * y j + x j * y i := rfl

omit [DecidableEq ι] in
private theorem sum_const_mul (s : Finset ι) (c : R) (f : ι → R) :
    ∑ i ∈ s, c * f i = c * ∑ i ∈ s, f i := by
  rw [Finset.mul_sum]

omit [DecidableEq ι] in
private theorem sum_sum_mul (s : Finset ι) (f g : ι → R) :
    ∑ j ∈ s, ∑ i ∈ s, f i * g j =
      (∑ i ∈ s, f i) * ∑ j ∈ s, g j := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_mul]

section PairSums

private theorem sum_sym2PairProduct_mul_symmetricPairCoordinates
    (s : Finset ι) (a x y : ι → R) :
    ∑ p ∈ s.sym2, sym2PairProduct a p * symmetricPairCoordinates x y p =
      (∑ i ∈ s, a i * x i) * ∑ i ∈ s, a i * y i := by
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sym2_insert]
      have hdisj : Disjoint ((insert i s).image fun j => s(i, j)) s.sym2 := by
        rw [Finset.disjoint_left]
        intro p hpImage hpOld
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hpImage
        exact hi (Finset.mk_mem_sym2_iff.mp hpOld).1
      rw [Finset.sum_union hdisj, Finset.sum_image]
      · rw [Finset.sum_insert hi, Finset.sum_insert hi, Finset.sum_insert hi, ih]
        have hne (j : ι) (hj : j ∈ s) : i ≠ j := fun h => hi (h ▸ hj)
        simp [sym2PairProduct_mk, symmetricPairCoordinates_mk,
          Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_congr rfl (fun j hj => if_neg (hne j hj))]
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
        have hcrossX :
            (∑ j ∈ s, a i * a j * (x i * y j)) =
              a i * x i * ∑ j ∈ s, a j * y j := by
          calc
            _ = ∑ j ∈ s, (a i * x i) * (a j * y j) := by
              apply Finset.sum_congr rfl
              intro j _
              ring
            _ = _ := sum_const_mul s (a i * x i) (fun j => a j * y j)
        have hcrossY :
            (∑ j ∈ s, a i * a j * (x j * y i)) =
              a i * y i * ∑ j ∈ s, a j * x j := by
          calc
            _ = ∑ j ∈ s, (a i * y i) * (a j * x j) := by
              apply Finset.sum_congr rfl
              intro j _
              ring
            _ = _ := sum_const_mul s (a i * y i) (fun j => a j * x j)
        have hold :
            (∑ j ∈ s, ∑ k ∈ s, a k * x k * (a j * y j)) =
              (∑ k ∈ s, a k * x k) * ∑ j ∈ s, a j * y j := by
          exact sum_sum_mul s (fun k => a k * x k) (fun j => a j * y j)
        rw [hcrossX, hcrossY, hold]
        ring
      · intro j hj k hk hjk
        exact Sym2.mkEmbedding i |>.injective hjk

private theorem sum_polarPairCoordinates_mul_symmetricPairCoordinates
    (s : Finset ι) (a b x y : ι → R) :
    ∑ p ∈ s.sym2, polarPairCoordinates a b p * symmetricPairCoordinates x y p =
      (∑ i ∈ s, a i * x i) * (∑ i ∈ s, b i * y i) +
        (∑ i ∈ s, b i * x i) * ∑ i ∈ s, a i * y i := by
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sym2_insert]
      have hdisj : Disjoint ((insert i s).image fun j => s(i, j)) s.sym2 := by
        rw [Finset.disjoint_left]
        intro p hpImage hpOld
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hpImage
        exact hi (Finset.mk_mem_sym2_iff.mp hpOld).1
      rw [Finset.sum_union hdisj, Finset.sum_image]
      · rw [Finset.sum_insert hi, Finset.sum_insert hi, Finset.sum_insert hi,
          Finset.sum_insert hi, Finset.sum_insert hi, ih]
        have hne (j : ι) (hj : j ∈ s) : i ≠ j := fun h => hi (h ▸ hj)
        simp [polarPairCoordinates_mk, symmetricPairCoordinates_mk,
          Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_congr rfl (fun j hj => if_neg (hne j hj))]
        simp_rw [add_mul, mul_add]
        simp only [Finset.sum_add_distrib]
        have haxby :
            (∑ j ∈ s, a i * b j * (x i * y j)) =
              a i * x i * ∑ j ∈ s, b j * y j := by
          calc
            _ = ∑ j ∈ s, (a i * x i) * (b j * y j) := by
              apply Finset.sum_congr rfl
              intro j _
              ring
            _ = _ := sum_const_mul s (a i * x i) (fun j => b j * y j)
        have haybx :
            (∑ j ∈ s, a i * b j * (x j * y i)) =
              a i * y i * ∑ j ∈ s, b j * x j := by
          calc
            _ = ∑ j ∈ s, (a i * y i) * (b j * x j) := by
              apply Finset.sum_congr rfl
              intro j _
              ring
            _ = _ := sum_const_mul s (a i * y i) (fun j => b j * x j)
        have hbxay :
            (∑ j ∈ s, a j * b i * (x i * y j)) =
              b i * x i * ∑ j ∈ s, a j * y j := by
          calc
            _ = ∑ j ∈ s, (b i * x i) * (a j * y j) := by
              apply Finset.sum_congr rfl
              intro j _
              ring
            _ = _ := sum_const_mul s (b i * x i) (fun j => a j * y j)
        have hbyax :
            (∑ j ∈ s, a j * b i * (x j * y i)) =
              b i * y i * ∑ j ∈ s, a j * x j := by
          calc
            _ = ∑ j ∈ s, (b i * y i) * (a j * x j) := by
              apply Finset.sum_congr rfl
              intro j _
              ring
            _ = _ := sum_const_mul s (b i * y i) (fun j => a j * x j)
        have holdAB :
            (∑ j ∈ s, ∑ k ∈ s, a k * x k * (b j * y j)) =
              (∑ k ∈ s, a k * x k) * ∑ j ∈ s, b j * y j := by
          exact sum_sum_mul s (fun k => a k * x k) (fun j => b j * y j)
        have holdBA :
            (∑ j ∈ s, ∑ k ∈ s, b k * x k * (a j * y j)) =
              (∑ k ∈ s, b k * x k) * ∑ j ∈ s, a j * y j := by
          exact sum_sum_mul s (fun k => b k * x k) (fun j => a j * y j)
        rw [haxby, haybx, hbxay, hbyax, holdAB, holdBA]
        ring
      · intro j hj k hk hjk
        exact Sym2.mkEmbedding i |>.injective hjk

end PairSums

/-- Concrete matrix of the symmetric-square representation in the unordered-pair basis. -/
def symmetricSquareMatrixGeneral (A : Matrix ι ι R) :
    Matrix (Sym2 ι) (Sym2 ι) R := fun p =>
  Sym2.lift ⟨fun i j =>
    symmetricPairCoordinates (fun r => A r i) (fun r => A r j) p, by
      intro i j
      exact congrFun
        (symmetricPairCoordinates_comm (fun r => A r i) (fun r => A r j)) p⟩

@[simp] theorem symmetricSquareMatrixGeneral_apply_mk
    (A : Matrix ι ι R) (p : Sym2 ι) (i j : ι) :
    symmetricSquareMatrixGeneral A p s(i, j) =
      symmetricPairCoordinates (fun r => A r i) (fun r => A r j) p := rfl

theorem symmetricSquareMatrixGeneral_apply_diag
    (A : Matrix ι ι R) (r : ι) (q : Sym2 ι) :
    symmetricSquareMatrixGeneral A s(r, r) q =
      sym2PairProduct (fun j => A r j) q := by
  induction q with
  | _ i j =>
      simp [symmetricSquareMatrixGeneral, symmetricPairCoordinates,
        sym2PairProduct, mul_comm]

theorem symmetricSquareMatrixGeneral_apply_offDiag
    (A : Matrix ι ι R) {r s : ι} (hrs : r ≠ s) (q : Sym2 ι) :
    symmetricSquareMatrixGeneral A s(r, s) q =
      polarPairCoordinates (fun j => A r j) (fun j => A s j) q := by
  induction q with
  | _ i j =>
      simp [symmetricSquareMatrixGeneral, symmetricPairCoordinates,
        polarPairCoordinates, hrs, mul_comm]

section Finite

variable [Fintype ι]

/-- Symmetric products intertwine arbitrary-rank matrix-vector multiplication. -/
theorem symmetricPairCoordinates_mulVec
    (A : Matrix ι ι R) (x y : ι → R) :
    symmetricPairCoordinates (A.mulVec x) (A.mulVec y) =
      (symmetricSquareMatrixGeneral A).mulVec (symmetricPairCoordinates x y) := by
  ext p
  induction p with
  | _ r s =>
      by_cases hrs : r = s
      · subst s
        simpa [Matrix.mulVec, dotProduct,
          symmetricSquareMatrixGeneral_apply_diag] using
          (sum_sym2PairProduct_mul_symmetricPairCoordinates
            (Finset.univ : Finset ι) (fun j => A r j) x y).symm
      · simpa [Matrix.mulVec, dotProduct, hrs,
          symmetricSquareMatrixGeneral_apply_offDiag] using
          (sum_polarPairCoordinates_mul_symmetricPairCoordinates
            (Finset.univ : Finset ι) (fun j => A r j) (fun j => A s j) x y).symm

/-- The arbitrary-rank symmetric-square construction preserves multiplication. -/
theorem symmetricSquareMatrixGeneral_mul (A B : Matrix ι ι R) :
    symmetricSquareMatrixGeneral (A * B) =
      symmetricSquareMatrixGeneral A * symmetricSquareMatrixGeneral B := by
  ext p q
  induction q with
  | _ i j =>
      change symmetricPairCoordinates
          (A.mulVec fun r => B r i) (A.mulVec fun r => B r j) p =
        (symmetricSquareMatrixGeneral A).mulVec
          (symmetricPairCoordinates (fun r => B r i) (fun r => B r j)) p
      exact congrFun
        (symmetricPairCoordinates_mulVec A (fun r => B r i) (fun r => B r j)) p

end Finite

/-- Multiplicity of an index in an unordered pair. -/
def sym2Multiplicity (j : ι) : Sym2 ι → ℕ :=
  Sym2.lift ⟨fun r s => (if r = j then 1 else 0) + (if s = j then 1 else 0), by
    intro r s
    simp [add_comm]⟩

@[simp] theorem sym2Multiplicity_mk (j r s : ι) :
    sym2Multiplicity j s(r, s) =
      (if r = j then 1 else 0) + (if s = j then 1 else 0) := rfl

theorem symmetricSquareMatrixGeneral_transvection_apply_self
    {i j : ι} (hij : i ≠ j) (c : R) (p : Sym2 ι) :
    symmetricSquareMatrixGeneral (Matrix.transvection i j c) p p = 1 := by
  induction p with
  | _ r s =>
      simp [symmetricSquareMatrixGeneral, symmetricPairCoordinates,
        Matrix.transvection, Matrix.single]
      split_ifs <;> simp_all [Matrix.one_apply]

theorem symmetricPairCoordinates_single (u v : ι) :
    symmetricPairCoordinates (Pi.single u (1 : R)) (Pi.single v 1) =
      Pi.single s(u, v) 1 := by
  ext p
  induction p with
  | _ r s =>
      by_cases hrs : r = s <;> by_cases hru : r = u <;> by_cases hrv : r = v <;>
        by_cases hsu : s = u <;> by_cases hsv : s = v <;>
        simp [symmetricPairCoordinates, Pi.single_apply,
          hrs, hru, hrv, hsu, hsv] at * <;> aesop

theorem symmetricPairCoordinates_add_left (x x' y : ι → R) :
    symmetricPairCoordinates (x + x') y =
      symmetricPairCoordinates x y + symmetricPairCoordinates x' y := by
  ext p
  induction p with
  | _ r s =>
      by_cases hrs : r = s <;>
        simp [symmetricPairCoordinates, hrs, Pi.add_apply] <;> ring

theorem symmetricPairCoordinates_add_right (x y y' : ι → R) :
    symmetricPairCoordinates x (y + y') =
      symmetricPairCoordinates x y + symmetricPairCoordinates x y' := by
  rw [symmetricPairCoordinates_comm, symmetricPairCoordinates_add_left]
  congr 1 <;> apply symmetricPairCoordinates_comm

theorem symmetricPairCoordinates_smul_left (c : R) (x y : ι → R) :
    symmetricPairCoordinates (c • x) y = c • symmetricPairCoordinates x y := by
  ext p
  induction p with
  | _ r s =>
      by_cases hrs : r = s <;>
        simp [symmetricPairCoordinates, hrs, Pi.smul_apply, smul_eq_mul] <;> ring

theorem symmetricPairCoordinates_smul_right (c : R) (x y : ι → R) :
    symmetricPairCoordinates x (c • y) = c • symmetricPairCoordinates x y := by
  rw [symmetricPairCoordinates_comm, symmetricPairCoordinates_smul_left]
  exact congrArg (c • ·) (symmetricPairCoordinates_comm y x)

private theorem transvection_column_ne
    {i j u : ι} (hu : u ≠ j) (c : R) :
    (fun r => Matrix.transvection i j c r u) = Pi.single u 1 := by
  have hju : j ≠ u := Ne.symm hu
  ext r
  by_cases hru : r = u
  · subst r
    simp [Matrix.transvection, Matrix.single, hju]
  · simp [Matrix.transvection, Matrix.single, hju, hru]

private theorem transvection_column_same
    {i j : ι} (hij : i ≠ j) (c : R) :
    (fun r => Matrix.transvection i j c r j) =
      Pi.single j 1 + c • Pi.single i 1 := by
  ext r
  by_cases hrj : r = j
  · subst r
    simp [Matrix.transvection, Matrix.single, hij]
  · by_cases hri : r = i
    · subst r
      simp [Matrix.transvection, Matrix.single, hij]
    · simp [Matrix.transvection, Matrix.single, hrj, hri]
      intro hir
      exact (hri hir.symm).elim

theorem symmetricSquareMatrixGeneral_transvection_column_of_ne
    {i j u v : ι} (hu : u ≠ j) (hv : v ≠ j) (c : R) :
    (fun p => symmetricSquareMatrixGeneral (Matrix.transvection i j c) p s(u, v)) =
      Pi.single s(u, v) 1 := by
  change symmetricPairCoordinates
      (fun r => Matrix.transvection i j c r u)
      (fun r => Matrix.transvection i j c r v) = _
  rw [transvection_column_ne hu, transvection_column_ne hv,
    symmetricPairCoordinates_single]

theorem symmetricSquareMatrixGeneral_transvection_column_left
    {i j v : ι} (hij : i ≠ j) (hv : v ≠ j) (c : R) :
    (fun p => symmetricSquareMatrixGeneral (Matrix.transvection i j c) p s(j, v)) =
      Pi.single s(j, v) 1 + c • Pi.single s(i, v) 1 := by
  change symmetricPairCoordinates
      (fun r => Matrix.transvection i j c r j)
      (fun r => Matrix.transvection i j c r v) = _
  rw [transvection_column_same hij, transvection_column_ne hv,
    symmetricPairCoordinates_add_left, symmetricPairCoordinates_smul_left,
    symmetricPairCoordinates_single, symmetricPairCoordinates_single]

theorem symmetricSquareMatrixGeneral_transvection_column_diag
    {i j : ι} (hij : i ≠ j) (c : R) :
    (fun p => symmetricSquareMatrixGeneral (Matrix.transvection i j c) p s(j, j)) =
      Pi.single s(j, j) 1 + (2 * c) • Pi.single s(i, j) 1 +
        c ^ 2 • Pi.single s(i, i) 1 := by
  change symmetricPairCoordinates
      (fun r => Matrix.transvection i j c r j)
      (fun r => Matrix.transvection i j c r j) = _
  rw [transvection_column_same hij]
  simp only [symmetricPairCoordinates_add_left, symmetricPairCoordinates_add_right,
    symmetricPairCoordinates_smul_left, symmetricPairCoordinates_smul_right,
    symmetricPairCoordinates_single]
  ext p
  simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Sym2.eq_swap (a := j) (b := i)]
  ring

theorem sym2Multiplicity_le_two (j : ι) (p : Sym2 ι) :
    sym2Multiplicity j p ≤ 2 := by
  induction p with
  | _ r s =>
      by_cases hr : r = j <;> by_cases hs : s = j <;>
        simp [sym2Multiplicity, hr, hs]

theorem sym2Multiplicity_eq_two_iff (j : ι) (p : Sym2 ι) :
    sym2Multiplicity j p = 2 ↔ p = s(j, j) := by
  induction p with
  | _ r s =>
      by_cases hr : r = j <;> by_cases hs : s = j <;>
        simp [sym2Multiplicity, hr, hs] at *

theorem symmetricSquareMatrixGeneral_transvection_eq_zero_of_count
    {i j : ι} (hij : i ≠ j) (c : R) {p q : Sym2 ι}
    (hpq : p ≠ q) (hcount : sym2Multiplicity j q ≤ sym2Multiplicity j p) :
    symmetricSquareMatrixGeneral (Matrix.transvection i j c) p q = 0 := by
  induction q with
  | _ u v =>
      by_cases hu : u = j
      · subst u
        by_cases hv : v = j
        · subst v
          have hpCount : sym2Multiplicity j p = 2 := by
            apply le_antisymm (sym2Multiplicity_le_two j p)
            simpa [sym2Multiplicity] using hcount
          exact False.elim (hpq ((sym2Multiplicity_eq_two_iff j p).mp hpCount))
        · have hpMain : p ≠ s(j, v) := hpq
          have hpLower : p ≠ s(i, v) := by
            intro hp
            subst p
            simp [sym2Multiplicity, hij, hv] at hcount
          have hcol := congrFun
            (symmetricSquareMatrixGeneral_transvection_column_left hij hv c) p
          rw [hcol]
          simp [hpMain, hpLower]
      · by_cases hv : v = j
        · subst v
          have hpMain : p ≠ s(j, u) := by
            intro hp
            apply hpq
            rw [hp, Sym2.eq_swap]
          have hpLower : p ≠ s(i, u) := by
            intro hp
            subst p
            simp [sym2Multiplicity, hij, hu] at hcount
          have hcol := congrFun
            (symmetricSquareMatrixGeneral_transvection_column_left hij hu c) p
          rw [show s(u, j) = s(j, u) from Sym2.eq_swap, hcol]
          simp [hpMain, hpLower]
        · have hcol := congrFun
            (symmetricSquareMatrixGeneral_transvection_column_of_ne (i := i) hu hv c) p
          rw [hcol]
          simp [hpq]

variable [Fintype ι]

theorem det_symmetricSquareMatrixGeneral_transvection
    {i j : ι} (hij : i ≠ j) (c : R) :
    (symmetricSquareMatrixGeneral (Matrix.transvection i j c)).det = 1 := by
  let M := symmetricSquareMatrixGeneral (Matrix.transvection i j c)
  have htri : M.BlockTriangular (sym2Multiplicity j) := by
    intro p q hqp
    apply symmetricSquareMatrixGeneral_transvection_eq_zero_of_count hij c
    · intro hpq
      subst q
      exact (lt_irrefl _ hqp)
    · exact Nat.le_of_lt hqp
  have hblock (k : ℕ) : M.toSquareBlock (sym2Multiplicity j) k = 1 := by
    ext p q
    by_cases hpq : (p : Sym2 ι) = q
    · have hpq' : p = q := Subtype.ext hpq
      subst q
      simp [M, Matrix.toSquareBlock_def,
        symmetricSquareMatrixGeneral_transvection_apply_self hij c]
    · have hcount : sym2Multiplicity j (q : Sym2 ι) ≤
          sym2Multiplicity j (p : Sym2 ι) := by
        rw [q.property, p.property]
      have hzero := symmetricSquareMatrixGeneral_transvection_eq_zero_of_count
        hij c hpq hcount
      have hpq' : p ≠ q := fun h => hpq (congrArg Subtype.val h)
      simp [M, Matrix.toSquareBlock_def, hzero, hpq']
  rw [htri.det]
  simp [hblock]

omit [Fintype ι] in
@[simp] theorem symmetricSquareMatrixGeneral_diagonal (d : ι → R) :
    symmetricSquareMatrixGeneral (Matrix.diagonal d) = diagonalSymmetricSquare d := by
  ext p q
  induction p with
  | _ r s =>
    induction q with
    | _ i j =>
      simp only [symmetricSquareMatrixGeneral_apply_mk,
        symmetricPairCoordinates_mk, Matrix.diagonal_apply,
        diagonalSymmetricSquare, Matrix.diagonal_apply, sym2PairProduct_mk]
      by_cases hrs : r = s <;> by_cases hij : i = j <;>
        by_cases hri : r = i <;> by_cases hrj : r = j <;>
        by_cases hsi : s = i <;> by_cases hsj : s = j <;>
        simp [hrs, hij, hri, hrj, hsi, hsj, mul_comm] <;> aesop

theorem det_symmetricSquareMatrixGeneral_diagonal (d : ι → R) :
    (symmetricSquareMatrixGeneral (Matrix.diagonal d)).det =
      (Matrix.diagonal d).det ^ (Fintype.card ι + 1) := by
  rw [symmetricSquareMatrixGeneral_diagonal, det_diagonalSymmetricSquare,
    Matrix.det_diagonal]

section Field

variable {F : Type*} [Field F]

/-- Determinant character of the symmetric-square representation in arbitrary finite rank. -/
theorem det_symmetricSquareMatrixGeneral (A : Matrix ι ι F) (hA : A.det ≠ 0) :
    (symmetricSquareMatrixGeneral A).det = A.det ^ (Fintype.card ι + 1) := by
  apply Matrix.diagonal_transvection_induction_of_det_ne_zero
    (P := fun M : Matrix ι ι F =>
      (symmetricSquareMatrixGeneral M).det = M.det ^ (Fintype.card ι + 1)) A hA
  · intro d _hd
    exact det_symmetricSquareMatrixGeneral_diagonal d
  · intro t
    cases t with
    | mk i j hij c =>
        change (symmetricSquareMatrixGeneral (Matrix.transvection i j c)).det =
          (Matrix.transvection i j c).det ^ (Fintype.card ι + 1)
        rw [det_symmetricSquareMatrixGeneral_transvection hij c,
          Matrix.det_transvection_of_ne i j hij, one_pow]
  · intro B C _hB _hC ihB ihC
    rw [symmetricSquareMatrixGeneral_mul, Matrix.det_mul, Matrix.det_mul,
      ihB, ihC, mul_pow]

/-- An invertible matrix has an invertible symmetric-square matrix. -/
theorem det_symmetricSquareMatrixGeneral_ne_zero
    (A : Matrix ι ι F) (hA : A.det ≠ 0) :
    (symmetricSquareMatrixGeneral A).det ≠ 0 := by
  rw [det_symmetricSquareMatrixGeneral A hA]
  exact pow_ne_zero _ hA

/-- Columns of the symmetric-square representation of an invertible matrix are linearly
independent. -/
theorem linearIndependent_cols_symmetricSquareMatrixGeneral
    (A : Matrix ι ι F) (hA : A.det ≠ 0) :
    LinearIndependent F (symmetricSquareMatrixGeneral A).col := by
  apply Matrix.linearIndependent_cols_of_det_ne_zero
  exact det_symmetricSquareMatrixGeneral_ne_zero A hA

/-- Rows of the symmetric-square representation of an invertible matrix are linearly
independent. -/
theorem linearIndependent_rows_symmetricSquareMatrixGeneral
    (A : Matrix ι ι F) (hA : A.det ≠ 0) :
    LinearIndependent F (symmetricSquareMatrixGeneral A) := by
  apply Matrix.linearIndependent_rows_of_det_ne_zero
  exact det_symmetricSquareMatrixGeneral_ne_zero A hA

end Field

end

end GaloisForLFunctions.HTGeometry
