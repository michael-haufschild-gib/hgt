import GaloisForLFunctions.HTGeometry.SymmetricSquareDeterminantFull
import Mathlib.Algebra.CharP.Two

/-!
# The quadratic exact sequence in characteristic two

For a finite index set, the symmetric square is `Sym2 ι → R` and the tensor square is
`Matrix ι ι R`. Diagonal inclusion, symmetrization, and multiplication give the exact sequence
`0 → R^ι → Sym²(R^ι) → R^ι ⊗ R^ι → Sym²(R^ι) → 0` in characteristic two.
The first term carries the Frobenius-twisted action. These are the coordinate maps in
Scavia, *The lifting problem for Galois representations of global fields*, §3.1.
-/

noncomputable section

namespace GaloisForLFunctions.RepresentationLifting

open HTGeometry

variable {ι R : Type*} [DecidableEq ι] [CommRing R]

/-- Inclusion of the pure-square coefficients in the symmetric square. -/
def squareDiagonal : (ι → R) →ₗ[R] (Sym2 ι → R) where
  toFun x := Sym2.lift ⟨fun i j => if i = j then x i else 0, by
    intro i j
    by_cases h : i = j
    · subst j; rfl
    · simp only [h, Ne.symm h, ↓reduceIte]⟩
  map_add' x y := by
    ext p
    induction p with
    | _ i j => by_cases h : i = j <;> simp [h]
  map_smul' a x := by
    ext p
    induction p with
    | _ i j => by_cases h : i = j <;> simp [h]

@[simp] theorem squareDiagonal_mk (x : ι → R) (i j : ι) :
    squareDiagonal x s(i, j) = if i = j then x i else 0 := rfl

/-- The map `uv ↦ u ⊗ v + v ⊗ u`, with its zero diagonal in characteristic two. -/
def tensorNorm : (Sym2 ι → R) →ₗ[R] Matrix ι ι R where
  toFun q i j := if i = j then 0 else q s(i, j)
  map_add' q r := by
    ext i j
    by_cases h : i = j <;> simp [h]
  map_smul' a q := by
    ext i j
    by_cases h : i = j <;> simp [h]

@[simp] theorem tensorNorm_apply (q : Sym2 ι → R) (i j : ι) :
    tensorNorm q i j = if i = j then 0 else q s(i, j) := rfl

/-- Multiplication from the tensor square to the symmetric square. -/
def tensorProjection : Matrix ι ι R →ₗ[R] (Sym2 ι → R) where
  toFun T := Sym2.lift ⟨fun i j => if i = j then T i i else T i j + T j i, by
    intro i j
    by_cases h : i = j
    · subst j; rfl
    · simp only [h, Ne.symm h, ↓reduceIte, add_comm]⟩
  map_add' T U := by
    ext p
    induction p with
    | _ i j => by_cases h : i = j <;> simp [h, add_add_add_comm]
  map_smul' a T := by
    ext p
    induction p with
    | _ i j => by_cases h : i = j <;> simp [h, mul_add]

@[simp] theorem tensorProjection_mk (T : Matrix ι ι R) (i j : ι) :
    tensorProjection T s(i, j) = if i = j then T i i else T i j + T j i := rfl

/-- Pure squares are an embedded copy of the original coordinate module. -/
theorem squareDiagonal_injective : Function.Injective (squareDiagonal (ι := ι) (R := R)) := by
  intro x y h
  funext i
  simpa only [squareDiagonal_mk, ↓reduceIte] using congrFun h s(i, i)

/-- Symmetrization loses exactly the pure-square coefficients. -/
theorem range_squareDiagonal :
    LinearMap.range (squareDiagonal (ι := ι) (R := R)) = LinearMap.ker tensorNorm := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    change tensorNorm (squareDiagonal x) = 0
    ext i j
    by_cases h : i = j <;> simp [h]
  · intro h
    have hq : tensorNorm q = 0 := h
    refine ⟨fun i => q s(i, i), ?_⟩
    ext p
    induction p with
    | _ i j =>
        by_cases hij : i = j
        · subst j; simp
        · have hz := congrFun (congrFun hq i) j
          simpa only [tensorNorm_apply, squareDiagonal_mk, hij, ↓reduceIte,
            Matrix.zero_apply] using hz.symm

/-- Choosing the upper triangle gives a preimage of every symmetric tensor. -/
theorem tensorProjection_surjective [LinearOrder ι] :
    Function.Surjective (tensorProjection (ι := ι) (R := R)) := by
  intro q
  refine ⟨fun i j => if i ≤ j then q s(i, j) else 0, ?_⟩
  ext p
  induction p with
  | _ i j =>
      by_cases hij : i = j
      · subst j; simp
      · rcases lt_or_gt_of_ne hij with h | h
        · simp [hij, le_of_lt h, not_le_of_gt h]
        · simp [hij, le_of_lt h, not_le_of_gt h, Sym2.eq_swap]

section CharacteristicTwo

variable [CharP R 2]

/-- Tensor multiplication kills precisely the symmetric tensors with zero diagonal. -/
theorem range_tensorNorm :
    LinearMap.range (tensorNorm (ι := ι) (R := R)) = LinearMap.ker tensorProjection := by
  ext T
  constructor
  · rintro ⟨q, rfl⟩
    change tensorProjection (tensorNorm q) = 0
    ext p
    induction p with
    | _ i j =>
        by_cases hij : i = j
        · subst j; simp
        · simp [hij, Ne.symm hij, Sym2.eq_swap, CharTwo.add_self_eq_zero]
  · intro h
    have hT : tensorProjection T = 0 := h
    have hdiag (i : ι) : T i i = 0 := by
      simpa only [tensorProjection_mk, ↓reduceIte, Pi.zero_apply] using congrFun hT s(i, i)
    have hsymm (i j : ι) : T i j = T j i := by
      by_cases hij : i = j
      · subst j; rfl
      · have hz : T i j + T j i = 0 := by
          simpa only [tensorProjection_mk, hij, ↓reduceIte, Pi.zero_apply] using
            congrFun hT s(i, j)
        calc
          T i j = T i j + (T j i + T j i) := by rw [CharTwo.add_self_eq_zero, add_zero]
          _ = T j i := by rw [← add_assoc, hz, zero_add]
    refine ⟨Sym2.lift ⟨fun i j => T i j, hsymm⟩, ?_⟩
    ext i j
    by_cases hij : i = j
    · subst j; simp [hdiag]
    · simp [hij]

/-- The four-term quadratic sequence is exact, including its two end maps. -/
theorem quadraticSequence_exact [LinearOrder ι] :
    Function.Injective (squareDiagonal (ι := ι) (R := R)) ∧
      LinearMap.range squareDiagonal = LinearMap.ker (tensorNorm (ι := ι) (R := R)) ∧
      LinearMap.range tensorNorm = LinearMap.ker (tensorProjection (ι := ι) (R := R)) ∧
      Function.Surjective (tensorProjection (ι := ι) (R := R)) :=
  ⟨squareDiagonal_injective, range_squareDiagonal, range_tensorNorm,
    tensorProjection_surjective⟩

/-- Squaring a vector has only diagonal coefficients; these coefficients are Frobenius squares. -/
theorem symmetricPairCoordinates_self (x : ι → R) :
    symmetricPairCoordinates x x = squareDiagonal (fun i => x i ^ 2) := by
  ext p
  induction p with
  | _ i j =>
      by_cases hij : i = j
      · subst j; simp [pow_two]
      · simp [hij, mul_comm, CharTwo.add_self_eq_zero]

/-- The existing symmetric-square action transports pure squares by entrywise Frobenius. -/
theorem symmetricSquare_frobenius_vectors [Fintype ι]
    (A : Matrix ι ι R) (x : ι → R) :
    (symmetricSquareMatrixGeneral A).mulVec (squareDiagonal (fun i => x i ^ 2)) =
      squareDiagonal (fun i => (A.mulVec x i) ^ 2) := by
  rw [← symmetricPairCoordinates_self, ← symmetricPairCoordinates_mulVec,
    symmetricPairCoordinates_self]

end CharacteristicTwo

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.quadraticSequence_exact
#print axioms GaloisForLFunctions.RepresentationLifting.symmetricSquare_frobenius_vectors
