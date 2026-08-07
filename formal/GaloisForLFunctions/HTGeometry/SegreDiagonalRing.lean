import GaloisForLFunctions.HTGeometry.BiprojectiveGradedPiece
import Mathlib.Algebra.MonoidAlgebra.Grading
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finsupp.Multiset

/-!
# The standard graded coordinate ring of the Segre variety

The Cox ring of `P^m x P^n` contains irrelevant coordinate-axis components, so it is not the
correct ring in which to treat `m + n` equations of bidegree `(1, 1)` as a global regular
sequence.  The diagonal subring is the homogeneous coordinate ring of the Segre embedding.  Its
monomials are exactly the biprojective monomials whose two block degrees agree.

This module constructs that ring as a monoid algebra, equips it with its natural standard grading,
and identifies every degree-`d` piece with the `(d, d)` Cox-ring piece.  In particular

```text
dim_K Segre(m,n)_d = choose(d+m,m) * choose(d+n,n).
```
-/

namespace GaloisForLFunctions.HTGeometry

/-- Exponent vectors whose total exponents in the two biprojective blocks agree. -/
noncomputable def segreExponentSubmonoid (m n : ℕ) : AddSubmonoid (BiprojVar m n →₀ ℕ) where
  carrier := {e | (Finsupp.weight biprojectiveWeight e).1 =
    (Finsupp.weight biprojectiveWeight e).2}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simpa using congrArg₂ (fun x y : ℕ => x + y) ha hb

/-- Common block degree of a balanced exponent vector. -/
noncomputable def segreExponentDegree (m n : ℕ) : segreExponentSubmonoid m n →+ ℕ where
  toFun e := (Finsupp.weight biprojectiveWeight e.1).1
  map_zero' := by simp
  map_add' a b := by simp

/-- Standard graded homogeneous coordinate ring of the Segre embedding of `P^m x P^n`. -/
noncomputable abbrev SegreDiagonalRing (K : Type*) [Semiring K] (m n : ℕ) :=
  AddMonoidAlgebra K (segreExponentSubmonoid m n)

/-- Inclusion of the Segre diagonal ring into the biprojective Cox ring. -/
noncomputable def segreToBiprojective (K : Type*) [CommSemiring K] (m n : ℕ) :
    SegreDiagonalRing K m n →ₐ[K] MvPolynomial (BiprojVar m n) K :=
  AddMonoidAlgebra.mapDomainAlgHom K K (AddSubmonoid.subtype (segreExponentSubmonoid m n))

/-- The diagonal monoid-algebra presentation has no extra relations: its map into the Cox ring is
injective. -/
theorem segreToBiprojective_injective (K : Type*) [CommSemiring K] (m n : ℕ) :
    Function.Injective (segreToBiprojective K m n) :=
  AddMonoidAlgebra.mapDomain_injective Subtype.val_injective

/-- Exponent of the degree-one Segre coordinate indexed by a pair of projective coordinates. -/
noncomputable def segrePairExponent (m n : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreExponentSubmonoid m n :=
  ⟨Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr j) 1, by
    change ((Finsupp.weight biprojectiveWeight)
        (Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr j) 1)).1 = _
    rw [map_add, Finsupp.weight_single, Finsupp.weight_single]
    rfl⟩

@[simp] theorem segreExponentDegree_pair (m n : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreExponentDegree m n (segrePairExponent m n i j) = 1 := by
  change ((Finsupp.weight biprojectiveWeight)
    (Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr j) 1)).1 = 1
  rw [map_add, Finsupp.weight_single, Finsupp.weight_single]
  rfl

/-- Marginal-sum map from matrices of exponents on coordinate pairs to biprojective exponents. -/
noncomputable def segrePairMarginal (m n : ℕ) :
    (Fin (m + 1) × Fin (n + 1) →₀ ℕ) →+ (BiprojVar m n →₀ ℕ) where
  toFun z := Finsupp.sumFinsuppEquivProdFinsupp.symm
    (Finsupp.mapDomain Prod.fst z, Finsupp.mapDomain Prod.snd z)
  map_zero' := by ext x <;> cases x <;> simp
  map_add' a b := by
    ext x
    cases x with
    | inl i => exact DFunLike.congr_fun
        ((Finsupp.mapDomain.addMonoidHom Prod.fst).map_add a b) i
    | inr j => exact DFunLike.congr_fun
        ((Finsupp.mapDomain.addMonoidHom Prod.snd).map_add a b) j

@[simp] theorem segrePairMarginal_single (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) (c : ℕ) :
    segrePairMarginal m n (Finsupp.single (i, j) c) =
      Finsupp.single (Sum.inl i) c + Finsupp.single (Sum.inr j) c := by
  ext x
  cases x <;> simp [segrePairMarginal]

/-- Degree-`d` part of the standard graded Segre coordinate ring. -/
noncomputable abbrev SegreDiagonalPiece (K : Type*) [Field K] (m n d : ℕ) :=
  AddMonoidAlgebra.gradeBy K (segreExponentDegree m n) d

/-- Balanced exponents of common degree `d` are exactly biprojective exponents of bidegree
`(d, d)`. -/
noncomputable def segreExponentDegreeEquiv (m n d : ℕ) :
    {e : segreExponentSubmonoid m n // segreExponentDegree m n e = d} ≃
      {e : BiprojVar m n →₀ ℕ // Finsupp.weight biprojectiveWeight e = (d, d)} where
  toFun e := ⟨e.1.1, by
    apply Prod.ext
    · exact e.2
    · exact e.1.2.symm.trans e.2⟩
  invFun e := ⟨⟨e.1, by
    change (Finsupp.weight biprojectiveWeight e.1).1 =
      (Finsupp.weight biprojectiveWeight e.1).2
    rw [e.2]⟩, by
      exact congrArg Prod.fst e.2⟩
  left_inv e := by ext; rfl
  right_inv e := by ext; rfl

/-- Monomial basis of a Segre graded piece, indexed by its balanced exponent vectors. -/
noncomputable def segreDiagonalMonomialBasisRaw (K : Type*) [Field K] (m n d : ℕ) :
    Module.Basis
      {e : segreExponentSubmonoid m n // segreExponentDegree m n e = d} K
      (SegreDiagonalPiece K m n d) where
  repr := AddMonoidAlgebra.supportedEquivFinsupp _

/-- Canonical linear identification of a Segre degree-`d` piece with the Cox-ring bidegree
`(d, d)` piece. -/
noncomputable def segreDiagonalPieceEquivBiprojectivePiece
    (K : Type*) [Field K] (m n d : ℕ) :
    SegreDiagonalPiece K m n d ≃ₗ[K] BiprojectivePiece K m n d d :=
  (segreDiagonalMonomialBasisRaw K m n d).equiv
    (biprojectiveMonomialBasisRaw K m n d d) (segreExponentDegreeEquiv m n d)

/-- Monomial basis indexed by the two weak compositions of the common degree. -/
noncomputable def segreDiagonalMonomialBasis (K : Type*) [Field K] (m n d : ℕ) :
    Module.Basis
      ((Finset.univ : Finset (Fin (m + 1))).finsuppAntidiag d ×
       (Finset.univ : Finset (Fin (n + 1))).finsuppAntidiag d) K
      (SegreDiagonalPiece K m n d) :=
  (segreDiagonalMonomialBasisRaw K m n d).reindex
    ((segreExponentDegreeEquiv m n d).trans (biprojExponentEquiv m n d d))

/-- **Hilbert function of the Segre coordinate ring.** -/
theorem finrank_segreDiagonalPiece (K : Type*) [Field K] (m n d : ℕ) :
    Module.finrank K (SegreDiagonalPiece K m n d) =
      (d + m).choose m * (d + n).choose n := by
  rw [Module.finrank_eq_card_basis (segreDiagonalMonomialBasis K m n d),
    Fintype.card_prod, Fintype.card_coe, Fintype.card_coe,
    Finset.card_finsuppAntidiag_nat_eq_choose,
    Finset.card_finsuppAntidiag_nat_eq_choose]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [show m + 1 + d - 1 = d + m by omega,
    show n + 1 + d - 1 = d + n by omega,
    Nat.choose_symm_add, Nat.choose_symm_add]

end GaloisForLFunctions.HTGeometry
