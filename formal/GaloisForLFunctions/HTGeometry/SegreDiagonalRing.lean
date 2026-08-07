import GaloisForLFunctions.HTGeometry.BiprojectiveGradedPiece
import Mathlib.Algebra.MonoidAlgebra.Grading
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finsupp.Multiset
import Mathlib.RingTheory.FiniteType

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
  map_zero' := by ext x; cases x <;> simp
  map_add' a b := by
    ext x
    cases x with
    | inl i =>
        exact congrArg (fun z : Fin (m + 1) →₀ ℕ => z i)
          ((Finsupp.mapDomain.addMonoidHom Prod.fst).map_add a b)
    | inr j =>
        exact congrArg (fun z : Fin (n + 1) →₀ ℕ => z j)
          ((Finsupp.mapDomain.addMonoidHom Prod.snd).map_add a b)

@[simp] theorem segrePairMarginal_single (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) (c : ℕ) :
    segrePairMarginal m n (Finsupp.single (i, j) c) =
      Finsupp.single (Sum.inl i) c + Finsupp.single (Sum.inr j) c := by
  ext x
  cases x <;> simp [segrePairMarginal]

/-- Two multisets of equal cardinality can be paired without changing either marginal. -/
theorem exists_multiset_pairing {I J : Type*} (a : Multiset I) (b : Multiset J)
    (h : a.card = b.card) :
    ∃ s : Multiset (I × J), s.map Prod.fst = a ∧ s.map Prod.snd = b := by
  induction a using Multiset.induction_on generalizing b with
  | empty =>
      have hb : b = 0 := Multiset.card_eq_zero.mp h.symm
      exact ⟨0, by simp [hb]⟩
  | @cons i a ih =>
      have hb : b ≠ 0 := by
        intro hb
        simp [hb] at h
      obtain ⟨j, hj⟩ := Multiset.exists_mem_of_ne_zero hb
      obtain ⟨b, rfl⟩ := Multiset.exists_cons_of_mem hj
      have hab : a.card = b.card := by simpa using h
      obtain ⟨s, hs₁, hs₂⟩ := ih b hab
      exact ⟨(i, j) ::ₘ s, by simp [hs₁, hs₂]⟩

/-- Pushing forward a multiset's multiplicity vector is the multiplicity vector of its image. -/
theorem mapDomain_toFinsupp {I J : Type*} [DecidableEq I] [DecidableEq J]
    (f : I → J) (s : Multiset I) :
    Finsupp.mapDomain f (Multiset.toFinsupp s) = Multiset.toFinsupp (s.map f) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      rw [show Multiset.toFinsupp (a ::ₘ s) =
        Finsupp.single a 1 + Multiset.toFinsupp s by
          rw [← Multiset.toFinsupp_singleton, ← Multiset.toFinsupp_add]
          rfl]
      rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, ih]
      rw [← Multiset.toFinsupp_singleton, ← Multiset.toFinsupp_add, Multiset.map_cons]
      rfl

/-- Every balanced exponent vector is a marginal sum of degree-one pair exponents. -/
theorem exists_segrePairMarginal_eq (m n : ℕ) (e : segreExponentSubmonoid m n) :
    ∃ z : Fin (m + 1) × Fin (n + 1) →₀ ℕ, segrePairMarginal m n z = e.1 := by
  classical
  let lr := Finsupp.sumFinsuppEquivProdFinsupp e.1
  have hsum : lr.1.sum (fun _ c => c) = lr.2.sum (fun _ c => c) := by
    have h := e.2
    change (Finsupp.weight biprojectiveWeight e.1).1 =
      (Finsupp.weight biprojectiveWeight e.1).2 at h
    rw [weight_biprojectiveWeight] at h
    simpa [lr] using h
  have hcard : (Finsupp.toMultiset lr.1).card = (Finsupp.toMultiset lr.2).card := by
    rw [Finsupp.card_toMultiset, Finsupp.card_toMultiset]
    exact hsum
  obtain ⟨s, hs₁, hs₂⟩ := exists_multiset_pairing
    (Finsupp.toMultiset lr.1) (Finsupp.toMultiset lr.2) hcard
  refine ⟨Multiset.toFinsupp s, ?_⟩
  apply Finsupp.sumFinsuppEquivProdFinsupp.injective
  change Finsupp.sumFinsuppEquivProdFinsupp
      (Finsupp.sumFinsuppEquivProdFinsupp.symm
        (Finsupp.mapDomain Prod.fst (Multiset.toFinsupp s),
         Finsupp.mapDomain Prod.snd (Multiset.toFinsupp s))) = lr
  rw [Finsupp.sumFinsuppEquivProdFinsupp.apply_symm_apply]
  apply Prod.ext
  · change Finsupp.mapDomain Prod.fst (Multiset.toFinsupp s) = lr.1
    rw [mapDomain_toFinsupp, hs₁, Finsupp.toMultiset_toFinsupp]
  · change Finsupp.mapDomain Prod.snd (Multiset.toFinsupp s) = lr.2
    rw [mapDomain_toFinsupp, hs₂, Finsupp.toMultiset_toFinsupp]

/-- Pair marginals as a map onto the balanced exponent monoid. -/
noncomputable def segrePairMarginalBalanced (m n : ℕ) :
    (Fin (m + 1) × Fin (n + 1) →₀ ℕ) →+ segreExponentSubmonoid m n where
  toFun z := ⟨segrePairMarginal m n z, by
    change ((Finsupp.weight biprojectiveWeight) (segrePairMarginal m n z)).1 = _
    rw [weight_biprojectiveWeight]
    rw [show Finsupp.sumFinsuppEquivProdFinsupp (segrePairMarginal m n z) =
        (Finsupp.mapDomain Prod.fst z, Finsupp.mapDomain Prod.snd z) by
      exact Finsupp.sumFinsuppEquivProdFinsupp.apply_symm_apply _]
    exact (Finsupp.sum_mapDomain_index_addMonoidHom
      (s := z) (f := Prod.fst) (fun _ => AddMonoidHom.id ℕ)).trans
      (Finsupp.sum_mapDomain_index_addMonoidHom
        (s := z) (f := Prod.snd) (fun _ => AddMonoidHom.id ℕ)).symm⟩
  map_zero' := by
    apply Subtype.ext
    exact (segrePairMarginal m n).map_zero
  map_add' a b := by
    apply Subtype.ext
    exact (segrePairMarginal m n).map_add a b

/-- Balanced marginal map is onto. -/
theorem segrePairMarginalBalanced_surjective (m n : ℕ) :
    Function.Surjective (segrePairMarginalBalanced m n) := by
  intro e
  obtain ⟨z, hz⟩ := exists_segrePairMarginal_eq m n e
  exact ⟨z, Subtype.ext hz⟩

/-- Polynomial presentation by the degree-one Segre coordinates. -/
noncomputable def segreDiagonalPresentation (K : Type*) [CommSemiring K] (m n : ℕ) :
    MvPolynomial (Fin (m + 1) × Fin (n + 1)) K →ₐ[K] SegreDiagonalRing K m n :=
  AddMonoidAlgebra.mapDomainAlgHom K K (segrePairMarginalBalanced m n)

/-- The degree-one polynomial presentation is surjective. -/
theorem segreDiagonalPresentation_surjective (K : Type*) [CommSemiring K] (m n : ℕ) :
    Function.Surjective (segreDiagonalPresentation K m n) :=
  by
    intro y
    obtain ⟨x, hx⟩ := Finsupp.mapDomain_surjective (M := K)
      (segrePairMarginalBalanced_surjective m n) y.coeff
    refine ⟨AddMonoidAlgebra.ofCoeff x, ?_⟩
    apply AddMonoidAlgebra.coeff_injective
    simpa [segreDiagonalPresentation, AddMonoidAlgebra.mapDomain] using hx

noncomputable instance segreDiagonalRing_finiteType (K : Type*) [CommSemiring K] (m n : ℕ) :
    Algebra.FiniteType K (SegreDiagonalRing K m n) :=
  Algebra.FiniteType.of_surjective (segreDiagonalPresentation K m n)
    (segreDiagonalPresentation_surjective K m n)

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
