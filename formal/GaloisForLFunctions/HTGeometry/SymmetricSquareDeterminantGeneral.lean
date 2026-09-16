import Mathlib.Algebra.BigOperators.Sym
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Arbitrary-rank diagonal symmetric-square determinant

Each coordinate of the diagonal symmetric-square action is indexed by an unordered pair and is the
product of the two corresponding diagonal entries. Every original coordinate occurs twice in its
square and once with every other coordinate, hence exactly `rank + 1` times in the determinant.
This formalizes the counting core of the symmetric-square determinant lemma in arbitrary finite
dimension.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

variable {ι R : Type*} [DecidableEq ι] [CommMonoid R]

/-- Product of the two diagonal weights indexed by an unordered pair. -/
def sym2PairProduct (d : ι → R) : Sym2 ι → R :=
  Sym2.lift ⟨fun i j => d i * d j, fun i j => mul_comm (d i) (d j)⟩

omit [DecidableEq ι] in
@[simp] theorem sym2PairProduct_mk (d : ι → R) (i j : ι) :
    sym2PairProduct d s(i, j) = d i * d j := rfl

/-- Product over all unordered pairs: every factor occurs `|s| + 1` times. -/
theorem prod_sym2PairProduct (s : Finset ι) (d : ι → R) :
    ∏ p ∈ s.sym2, sym2PairProduct d p = (∏ i ∈ s, d i) ^ (s.card + 1) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sym2_insert]
      have hdisj : Disjoint ((insert a s).image fun b => s(a, b)) s.sym2 := by
        rw [Finset.disjoint_left]
        intro p hpImage hpOld
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hpImage
        have haOld : a ∈ s := (Finset.mk_mem_sym2_iff.mp hpOld).1
        exact ha haOld
      rw [Finset.prod_union hdisj, Finset.prod_image]
      · simp only [sym2PairProduct_mk, Finset.prod_mul_distrib, Finset.prod_const,
          Finset.card_insert_of_notMem ha, ih, Finset.prod_insert ha]
        simp [pow_succ', mul_pow]
        ac_rfl
      · intro b hb c hc hbc
        exact Sym2.mkEmbedding a |>.injective hbc

section Diagonal

variable {S : Type*} [CommRing S] [Fintype ι]

/-- Symmetric-square action of a diagonal matrix in the unordered-pair basis. -/
noncomputable def diagonalSymmetricSquare (d : ι → S) : Matrix (Sym2 ι) (Sym2 ι) S :=
  Matrix.diagonal (sym2PairProduct d)

/-- Arbitrary-rank diagonal case of `det(Sym² A) = det(A)^(rank+1)`. -/
theorem det_diagonalSymmetricSquare (d : ι → S) :
    (diagonalSymmetricSquare d).det = (∏ i, d i) ^ (Fintype.card ι + 1) := by
  rw [diagonalSymmetricSquare, Matrix.det_diagonal]
  simpa using prod_sym2PairProduct (Finset.univ : Finset ι) d

end Diagonal

end GaloisForLFunctions.HTGeometry
