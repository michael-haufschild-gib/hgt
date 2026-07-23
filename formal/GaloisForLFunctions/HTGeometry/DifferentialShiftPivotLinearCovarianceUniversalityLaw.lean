import GaloisForLFunctions.HTGeometry.DifferentialLinearChangeAutomorphism
import GaloisForLFunctions.HTGeometry.DifferentialShiftPivotRelationIdeal

/-!
# Linear covariance of complete shifted-pivot relation ideals

An invertible constant matrix acts on every jet order.  Evaluation after this formal jet
automorphism is exactly evaluation on the linearly recombined analytic family.  Consequently the
complete differential-relation ideal transforms contravariantly, and every complete shifted-pivot
presentation remains complete in arbitrary invertible linear jet coordinates.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open Matrix MvPolynomial GaloisForLFunctions

noncomputable section

/-- Evaluating after a formal jetwise linear change equals evaluating on the corresponding
linearly recombined source family. -/
theorem differentialPolynomialEval_linearChange
    {F K n : Type*} [CommRing F] [CommRing K] [Algebra F K]
    [Differential K] [Fintype n]
    (hconst : ∀ c : F, (algebraMap F K c)′ = 0)
    (M : Matrix n n F) (x : n → K) (P : DifferentialPolynomial n F) :
    differentialPolynomialEval (C := F) x
        (differentialJetLinearChangeAlgHom M P) =
      differentialPolynomialEval (C := F) (matrixLinearForms M x) P := by
  let left := (differentialPolynomialEval (C := F) x).comp
    (differentialJetLinearChangeAlgHom M)
  let right := differentialPolynomialEval (C := F) (matrixLinearForms M x)
  have heq : left = right := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, r⟩
    simp only [left, right, AlgHom.coe_comp, Function.comp_apply,
      differentialJetLinearChangeAlgHom_X, differentialPolynomialEval_X]
    rw [differentialJet_matrixLinearForms hconst]
    simpa [differentialPolynomialEval] using
      (aeval_jetwiseMatrixLinearPolynomial M
        (fun p : n × ℕ => differentialJet p.2 (x p.1)) (i, r))
  exact AlgHom.congr_fun heq P

/-- **Universal relation-ideal covariance.**  A polynomial is a relation of the linearly changed
family exactly when its image under the corresponding jet automorphism is a relation of the
original family. -/
theorem mem_differentialRelationIdeal_linearChange_iff
    {F K n : Type*} [CommRing F] [CommRing K] [Algebra F K]
    [Differential K] [Fintype n] [DecidableEq n]
    (hconst : ∀ c : F, (algebraMap F K c)′ = 0)
    (M N : Matrix n n F) (hMN : M * N = 1) (hNM : N * M = 1)
    (x : n → K) (P : DifferentialPolynomial n F) :
    P ∈ differentialRelationIdeal (matrixLinearForms M x) ↔
      differentialJetLinearChangeAlgEquiv M N hMN hNM P ∈
        differentialRelationIdeal x := by
  rw [mem_differentialRelationIdeal_iff, mem_differentialRelationIdeal_iff]
  change differentialPolynomialEval (C := F) (matrixLinearForms M x) P = 0 ↔
    differentialPolynomialEval (C := F) x
      (differentialJetLinearChangeAlgHom M P) = 0
  rw [differentialPolynomialEval_linearChange hconst M x P]

/-- **Shifted-pivot covariance law.**  The displayed shifted-pivot ideal remains the complete
relation ideal after any invertible linear change of all pivot and dependent coordinates; the
formal inverse image is computed by the universal jet automorphism. -/
theorem mem_linearChangedDifferentialRelationIdeal_iff_shiftPivot
    {F K B R : Type*} [Field F] [Field K] [Algebra F K] [Differential K]
    [Fintype B] [Fintype R] [DecidableEq B] [DecidableEq R]
    (hconst : ∀ c : F, (algebraMap F K c)′ = 0)
    (x : B → K) (y : R → K)
    (base : R → B) (offset : R → ℕ) (c : R → ℕ → F)
    (hx : DifferentialIndependent F x)
    (hrel : ∀ r n, differentialJet n (y r) =
      algebraMap F K (c r n) * differentialJet (n + offset r) (x (base r)))
    (M N : Matrix (B ⊕ R) (B ⊕ R) F)
    (hMN : M * N = 1) (hNM : N * M = 1)
    (P : DifferentialPolynomial (B ⊕ R) F) :
    P ∈ differentialRelationIdeal (matrixLinearForms M (Sum.elim x y)) ↔
      differentialJetLinearChangeAlgEquiv M N hMN hNM P ∈
        differentialShiftPivotRelationIdeal base offset c := by
  rw [mem_differentialRelationIdeal_linearChange_iff
    hconst M N hMN hNM (Sum.elim x y) P,
    differentialRelationIdeal_sumElim_eq_shiftPivot x y base offset c hx hrel]

end

end GaloisForLFunctions.HTGeometry
