import GaloisForLFunctions.HTGeometry.FiniteFamilyBlockHypersurfaceDimension

/-!
# Decidable criteria for the nonconstancy interface

The disjoint-block independence and hypersurface-dimension theorems are stated for families of
nonconstant complex multivariate polynomials.  Nonconstancy is here characterized by total degree,
which turns the interface into a checkable criterion and produces unconditional instances of the
block independence and iterated dimension-drop laws for the coordinate family `X (f b)`.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

/-- Constancy is exactly vanishing total degree. -/
theorem isConstantMvPolynomial_iff_totalDegree_eq_zero
    {σ : Type*} (P : MvPolynomial σ ℂ) :
    IsConstantMvPolynomial P ↔ P.totalDegree = 0 := by
  constructor
  · rintro ⟨a, rfl⟩
    simp
  · intro h
    exact ⟨coeff 0 P, (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h).symm⟩

/-- Scalars are the constant polynomials. -/
theorem isConstantMvPolynomial_C {σ : Type*} (a : ℂ) :
    IsConstantMvPolynomial (C a : MvPolynomial σ ℂ) :=
  ⟨a, rfl⟩

/-- Positive total degree is nonconstancy. -/
theorem not_isConstantMvPolynomial_of_totalDegree_ne_zero
    {σ : Type*} {P : MvPolynomial σ ℂ} (h : P.totalDegree ≠ 0) :
    ¬ IsConstantMvPolynomial P := by
  rw [isConstantMvPolynomial_iff_totalDegree_eq_zero]
  exact h

/-- A nonzero coefficient at a nonzero exponent is nonconstancy. -/
theorem not_isConstantMvPolynomial_of_coeff_ne_zero
    {σ : Type*} {P : MvPolynomial σ ℂ} {d : σ →₀ ℕ} (hd : d ≠ 0)
    (h : coeff d P ≠ 0) : ¬ IsConstantMvPolynomial P := by
  classical
  rintro ⟨a, rfl⟩
  apply h
  rw [MvPolynomial.coeff_C]
  simp [Ne.symm hd]

/-- Every coordinate is nonconstant. -/
theorem not_isConstantMvPolynomial_X {σ : Type*} (i : σ) :
    ¬ IsConstantMvPolynomial (X i : MvPolynomial σ ℂ) := by
  apply not_isConstantMvPolynomial_of_totalDegree_ne_zero
  rw [MvPolynomial.totalDegree_X]
  exact one_ne_zero

/-- **Coordinate block independence.**  Placing one coordinate in each disjoint variable block
yields an algebraically independent family, with no nonconstancy premise. -/
theorem rowBlockPolynomial_X_algebraicIndependent
    {row σ : Type*} (f : row → σ) :
    AlgebraicIndependent ℂ
      (fun b => rowBlockPolynomial b (X (f b) : MvPolynomial σ ℂ)) :=
  rowBlockPolynomial_algebraicIndependent _ fun b => not_isConstantMvPolynomial_X (f b)

/-- **Unconditional iterated dimension drop.**  A finite coordinate family in independent variable
blocks cuts iterated Krull dimension by at least the cardinality of the family. -/
theorem finiteFamilyBlockHypersurfaceRing_X_krullDim_add_card_le
    {row σ : Type} [Fintype row] [Finite σ] [LinearOrder σ] [WellFoundedGT σ]
    (f : row → σ) :
    ringKrullDim
        (finiteFamilyBlockHypersurfaceRing
          (fun b => (X (f b) : MvPolynomial σ ℂ))) +
        Fintype.card row ≤
      Fintype.card row * Nat.card σ :=
  finiteFamilyBlockHypersurfaceRing_krullDim_add_card_le _
    fun b => not_isConstantMvPolynomial_X (f b)

end

end GaloisForLFunctions.HTGeometry
