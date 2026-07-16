import GaloisForLFunctions.HTGeometry.MvPolynomialJacobianFDeriv

namespace GaloisForLFunctions.HTGeometry

open Set

noncomputable section

def complexMvPolynomialFamilyZeroLocus {n m : ℕ}
    (P : Fin m → MvPolynomial (Fin n) ℂ) : Set (Fin n → ℂ) :=
  {x | complexMvPolynomialFamilyEval P x = 0}

/-- The common zero locus away from the algebraic maximal-Jacobian-minor defect. -/
def complexMvPolynomialFamilyMaximalMinorRegularLocus {n m : ℕ}
    (P : Fin m → MvPolynomial (Fin n) ℂ) : Set (Fin n → ℂ) :=
  complexMvPolynomialFamilyZeroLocus P ∩
    (complexMvPolynomialFamilyJacobianRankDefect P)ᶜ

/-- The analytic derivative definition of the regular locus equals the maximal-minor locus. -/
theorem complexMvPolynomialFamilyRegularZeroLocus_eq_maximalMinorRegularLocus
    {n m : ℕ} (P : Fin m → MvPolynomial (Fin n) ℂ) :
    complexMvPolynomialFamilyRegularZeroLocus P =
      complexMvPolynomialFamilyMaximalMinorRegularLocus P := by
  ext x
  simp only [complexMvPolynomialFamilyRegularZeroLocus,
    complexMvPolynomialFamilyMaximalMinorRegularLocus,
    complexMvPolynomialFamilyZeroLocus, Set.mem_setOf_eq, Set.mem_inter_iff,
    Set.mem_compl_iff]
  rw [surjective_fderiv_complexMvPolynomialFamilyEval_real_iff_notMem_rankDefect]

theorem isClosed_complexMvPolynomialFamilyJacobianRankDefect
    {n m : ℕ} (P : Fin m → MvPolynomial (Fin n) ℂ) :
    IsClosed (complexMvPolynomialFamilyJacobianRankDefect P) := by
  rw [show complexMvPolynomialFamilyJacobianRankDefect P =
      ⋂ cols : Fin m → Fin n,
        {x | MvPolynomial.eval x
          (complexMvPolynomialFamilyJacobianMinor P cols) = 0} by
    ext x
    simp [complexMvPolynomialFamilyJacobianRankDefect]]
  apply isClosed_iInter
  intro cols
  exact isClosed_singleton.preimage
    (contDiff_mvPolynomial_eval_complex_real
      (complexMvPolynomialFamilyJacobianMinor P cols)).continuous

/-- The maximal-minor locus is a real regular level set of complex codimension `m`. -/
theorem complexMvPolynomialFamilyMaximalMinorRegularLocus_isLocalRegularLevelSet
    {n m : ℕ} (P : Fin m → MvPolynomial (Fin n) ℂ) :
    IsLocalRegularLevelSetOfCodimAtLeast
      (complexMvPolynomialFamilyMaximalMinorRegularLocus P) (2 * m) := by
  let F : (Fin n → ℂ) → (Fin m → ℂ) := complexMvPolynomialFamilyEval P
  let O : Set (Fin n → ℂ) :=
    (complexMvPolynomialFamilyJacobianRankDefect P)ᶜ
  have hF : ContDiff ℝ ⊤ F := contDiff_complexMvPolynomialFamilyEval_real P
  have hO : IsOpen O :=
    (isClosed_complexMvPolynomialFamilyJacobianRankDefect P).isOpen_compl
  have hsurj : ∀ x, F x = 0 → x ∈ O →
      Function.Surjective (fderiv ℝ F x) := by
    intro x _ hx
    exact surjective_fderiv_complexMvPolynomialFamilyEval_real_of_notMem_rankDefect P x hx
  have hcodim : 2 * m ≤ Module.finrank ℝ (Fin m → ℂ) := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, Nat.mul_comm]
  have hreg :=
    isLocalRegularLevelSetOfCodimAtLeast_zeroSet_inter_isOpen_finiteDimensional
      F hcodim hF hO hsurj
  simpa [complexMvPolynomialFamilyMaximalMinorRegularLocus,
    complexMvPolynomialFamilyZeroLocus, F, O] using hreg

theorem isComplexAffineAlgebraic_complexMvPolynomialFamilyZeroLocus
    {n m : ℕ} (P : Fin m → MvPolynomial (Fin n) ℂ) :
    IsComplexAffineAlgebraic (complexMvPolynomialFamilyZeroLocus P) := by
  simpa [complexMvPolynomialFamilyZeroLocus, complexMvPolynomialFamilyEval,
    funext_iff] using isComplexAffineAlgebraic_zeroLocus_family P

/-- Removing the regular maximal-minor locus leaves an algebraic singular remainder. -/
theorem isComplexAffineAlgebraic_complexMvPolynomialFamilySingularRemainder
    {n m : ℕ} (P : Fin m → MvPolynomial (Fin n) ℂ) :
    IsComplexAffineAlgebraic
      (complexMvPolynomialFamilyZeroLocus P \
        complexMvPolynomialFamilyMaximalMinorRegularLocus P) := by
  have hzero := isComplexAffineAlgebraic_complexMvPolynomialFamilyZeroLocus P
  have hdefect :=
    isComplexAffineAlgebraic_complexMvPolynomialFamilyJacobianRankDefect P
  have hinter := hzero.inter hdefect
  convert hinter using 1
  ext x
  simp [complexMvPolynomialFamilyMaximalMinorRegularLocus]

/-- A nonempty maximal-minor locus supplies one unconditional Noetherian regular peel. -/
theorem complexMvPolynomialFamily_exists_regularPeel
    {n m : ℕ} (P : Fin m → MvPolynomial (Fin n) ℂ)
    (hne : (complexMvPolynomialFamilyMaximalMinorRegularLocus P).Nonempty) :
    ∃ R : Set (Fin n → ℂ), R.Nonempty ∧
      R ⊆ complexMvPolynomialFamilyZeroLocus P ∧
      IsLocalRegularLevelSetOfCodimAtLeast R (2 * m) ∧
      IsComplexAffineAlgebraic
        (complexMvPolynomialFamilyZeroLocus P \ R) := by
  exact ⟨complexMvPolynomialFamilyMaximalMinorRegularLocus P, hne,
    inter_subset_left,
    complexMvPolynomialFamilyMaximalMinorRegularLocus_isLocalRegularLevelSet P,
    isComplexAffineAlgebraic_complexMvPolynomialFamilySingularRemainder P⟩

end

end GaloisForLFunctions.HTGeometry
