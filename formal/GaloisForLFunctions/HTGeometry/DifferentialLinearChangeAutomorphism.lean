import GaloisForLFunctions.HTGeometry.DifferentialIndependentLinearForms
import GaloisForLFunctions.HTGeometry.DifferentialPolynomial

/-!
# Jetwise linear differential automorphisms

An invertible constant matrix acts on every formal jet order by the same matrix.  The inverse
matrix produces an actual algebra automorphism of the full differential polynomial ring, and the
automorphism commutes with the jet-shift derivation.  This is the formal symmetry behind the
projective geometry of a differentially free carrier family.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open Matrix MvPolynomial GaloisForLFunctions

noncomputable section

/-- Substitute the same constant matrix into every formal jet order. -/
def differentialJetLinearChangeAlgHom
    {C n : Type*} [CommRing C] [Fintype n] (M : Matrix n n C) :
    DifferentialPolynomial n C →ₐ[C] DifferentialPolynomial n C :=
  MvPolynomial.bind₁ (jetwiseMatrixLinearPolynomial M)

@[simp]
theorem differentialJetLinearChangeAlgHom_X
    {C n : Type*} [CommRing C] [Fintype n]
    (M : Matrix n n C) (i : n) (r : ℕ) :
    differentialJetLinearChangeAlgHom M (MvPolynomial.X (i, r)) =
      jetwiseMatrixLinearPolynomial M (i, r) := by
  simp [differentialJetLinearChangeAlgHom]

/-- Two-sided inverse matrices induce inverse algebra substitutions on all formal jets. -/
def differentialJetLinearChangeAlgEquiv
    {C n : Type*} [CommRing C] [Fintype n] [DecidableEq n]
    (M N : Matrix n n C) (hMN : M * N = 1) (hNM : N * M = 1) :
    DifferentialPolynomial n C ≃ₐ[C] DifferentialPolynomial n C := by
  let f := differentialJetLinearChangeAlgHom M
  let g := differentialJetLinearChangeAlgHom N
  exact AlgEquiv.ofAlgHom f g (by
    apply MvPolynomial.algHom_ext
    intro p
    rcases p with ⟨i, r⟩
    simpa [f, g, differentialJetLinearChangeAlgHom] using
      bind_jetwiseMatrixLinearPolynomial N M hNM (i, r)) (by
    apply MvPolynomial.algHom_ext
    intro p
    rcases p with ⟨i, r⟩
    simpa [f, g, differentialJetLinearChangeAlgHom] using
      bind_jetwiseMatrixLinearPolynomial M N hMN (i, r))

@[simp]
theorem differentialJetLinearChangeAlgEquiv_X
    {C n : Type*} [CommRing C] [Fintype n] [DecidableEq n]
    (M N : Matrix n n C) (hMN : M * N = 1) (hNM : N * M = 1)
    (i : n) (r : ℕ) :
    differentialJetLinearChangeAlgEquiv M N hMN hNM (MvPolynomial.X (i, r)) =
      jetwiseMatrixLinearPolynomial M (i, r) := by
  exact differentialJetLinearChangeAlgHom_X M i r

/-- The order-zero linear form whose iterated derivatives produce the jetwise substitution. -/
def differentialLinearJetSource
    {C n : Type*} [CommRing C] [Fintype n] (M : Matrix n n C) (i : n) :
    DifferentialPolynomial n C :=
  matrixLinearForms M (fun j => MvPolynomial.X (j, 0)) i

theorem differentialLinearJetSource_jet
    {C n : Type*} [CommRing C] [Fintype n]
    (M : Matrix n n C) (i : n) (r : ℕ) :
    differentialJet r (differentialLinearJetSource M i) =
      jetwiseMatrixLinearPolynomial M (i, r) := by
  rw [differentialLinearJetSource,
    differentialJet_matrixLinearForms (fun c : C => by simp) M]
  simp [matrixLinearForms, jetwiseMatrixLinearPolynomial,
    differentialJet_differentialPolynomial_X]

/-- The jetwise matrix substitution is evaluation at its order-zero linear source family. -/
theorem differentialJetLinearChangeAlgHom_eq_eval
    {C n : Type*} [CommRing C] [Fintype n] (M : Matrix n n C) :
    differentialJetLinearChangeAlgHom M =
      differentialPolynomialEval (differentialLinearJetSource M) := by
  ext p
  rcases p with ⟨i, r⟩
  rw [differentialJetLinearChangeAlgHom_X, differentialPolynomialEval_X,
    differentialLinearJetSource_jet]

/-- Jetwise constant linear substitution commutes with the differential-polynomial derivation. -/
theorem differentialJetLinearChangeAlgHom_derivation
    {C n : Type*} [CommRing C] [Fintype n] (M : Matrix n n C)
    (P : DifferentialPolynomial n C) :
    differentialJetLinearChangeAlgHom M (differentialPolynomialDerivation n C P) =
      differentialPolynomialDerivation n C (differentialJetLinearChangeAlgHom M P) := by
  rw [differentialJetLinearChangeAlgHom_eq_eval]
  exact differentialPolynomialEval_derivation
    (differentialLinearJetSource M) (fun c => by simp) P

/-- The invertible jetwise substitution is a differential algebra automorphism. -/
theorem differentialJetLinearChangeAlgEquiv_derivation
    {C n : Type*} [CommRing C] [Fintype n] [DecidableEq n]
    (M N : Matrix n n C) (hMN : M * N = 1) (hNM : N * M = 1)
    (P : DifferentialPolynomial n C) :
    differentialJetLinearChangeAlgEquiv M N hMN hNM
        (differentialPolynomialDerivation n C P) =
      differentialPolynomialDerivation n C
        (differentialJetLinearChangeAlgEquiv M N hMN hNM P) :=
  differentialJetLinearChangeAlgHom_derivation M P

end

end GaloisForLFunctions.HTGeometry
