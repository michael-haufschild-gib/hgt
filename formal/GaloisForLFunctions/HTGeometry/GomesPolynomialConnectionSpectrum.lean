import GaloisForLFunctions.HTGeometry.GomesPolynomialFirstOrderInverse
import Mathlib.Algebra.Algebra.Spectrum.Basic

/-!
# Algebraic spectrum versus polynomial eigenstate reconstruction

The scalar polynomial connection experiment distinguishes two observations sharply.
A nonconstant coefficient admits no polynomial eigenvectors, yet every real shift fails
to be invertible on polynomials. Its algebraic spectrum is therefore the entire real
line. Constant coefficients instead have a singleton spectrum detected by constants.
These statements concern the full algebra of polynomial linear endomorphisms.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- A spectral shift is the negative first-order operator with an added constant coefficient. -/
theorem gomesPolynomialFirstOrderLinearMap_spectral_shift (A : ℝ[X]) (r : ℝ) :
    algebraMap ℝ (Module.End ℝ ℝ[X]) r - gomesPolynomialFirstOrderLinearMap A =
      -(gomesPolynomialFirstOrderLinearMap (A + C r)) := by
  apply LinearMap.ext
  intro B
  simp [gomesPolynomialFirstOrderLinearMap, gomesPolynomialFirstOrderOperator,
    Algebra.algebraMap_eq_smul_one, smul_eq_C_mul]
  ring

/-- A first-order polynomial connection is a unit exactly for a nonzero constant coefficient. -/
theorem gomesPolynomialFirstOrderLinearMap_isUnit_iff (A : ℝ[X]) :
    IsUnit (gomesPolynomialFirstOrderLinearMap A) ↔ A ≠ 0 ∧ A.derivative = 0 := by
  rw [Module.End.isUnit_iff]
  exact gomesPolynomialFirstOrderOperator_bijective_iff A

/-- Every real spectral obstruction is either a zero constant shift or a nonconstant coefficient. -/
theorem gomesPolynomialFirstOrderLinearMap_mem_spectrum_iff (A : ℝ[X]) (r : ℝ) :
    r ∈ spectrum ℝ (gomesPolynomialFirstOrderLinearMap A) ↔
      A + C r = 0 ∨ A.derivative ≠ 0 := by
  rw [spectrum.mem_iff, gomesPolynomialFirstOrderLinearMap_spectral_shift]
  have hn := @IsUnit.neg_iff (Module.End ℝ ℝ[X]) _ _
    (gomesPolynomialFirstOrderLinearMap (A + C r))
  rw [hn, gomesPolynomialFirstOrderLinearMap_isUnit_iff]
  simp only [derivative_add, derivative_C, add_zero, not_and_or, not_not]

/-- Constant coefficients have the expected singleton real algebraic spectrum. -/
theorem gomesPolynomialFirstOrderLinearMap_constant_spectrum (a : ℝ) :
    spectrum ℝ (gomesPolynomialFirstOrderLinearMap (C a)) = {-a} := by
  ext r
  rw [gomesPolynomialFirstOrderLinearMap_mem_spectrum_iff]
  simp only [derivative_C, ne_eq, not_true_eq_false, or_false, ← map_add, C_eq_zero,
    Set.mem_singleton_iff]
  exact add_eq_zero_iff_eq_neg'

/-- Nonconstant coefficients have the entire real line as their algebraic spectrum. -/
theorem gomesPolynomialFirstOrderLinearMap_nonconstant_spectrum
    (A : {A : ℝ[X] // A.derivative ≠ 0}) :
    spectrum ℝ (gomesPolynomialFirstOrderLinearMap A.val) = Set.univ := by
  ext r
  constructor
  · intro _; exact Set.mem_univ r
  · intro _
    exact (gomesPolynomialFirstOrderLinearMap_mem_spectrum_iff A.val r).mpr (Or.inr A.property)

/-- Real polynomial eigenvalues of the first-order connection. -/
def gomesPolynomialFirstOrderEigenvalues (A : ℝ[X]) : Set ℝ :=
  {r | ∃ B : ℝ[X], B ≠ 0 ∧ gomesPolynomialFirstOrderOperator A B = r • B}

/-- A nonzero polynomial eigenvector exists exactly when the shifted coefficient vanishes. -/
theorem gomesPolynomialFirstOrderEigenvalues_mem_iff (A : ℝ[X]) (r : ℝ) :
    r ∈ gomesPolynomialFirstOrderEigenvalues A ↔ A + C r = 0 := by
  constructor
  · rintro ⟨B, hb, he⟩
    have hz : gomesPolynomialFirstOrderOperator (A + C r) B =
        gomesPolynomialFirstOrderOperator (A + C r) 0 := by
      simp only [gomesPolynomialFirstOrderOperator, derivative_zero, mul_zero, sub_zero,
        add_mul, smul_eq_C_mul] at he ⊢
      linear_combination he
    by_contra ha
    exact hb ((gomesPolynomialFirstOrderOperator_injective_iff _).mpr ha hz)
  · intro h
    refine ⟨1, one_ne_zero, ?_⟩
    have he : A = -C r := eq_neg_of_add_eq_zero_left h
    simp [gomesPolynomialFirstOrderOperator, he, smul_eq_C_mul]

/-- Constant coefficients have exactly one real polynomial eigenvalue. -/
theorem gomesPolynomialFirstOrderEigenvalues_constant (a : ℝ) :
    gomesPolynomialFirstOrderEigenvalues (C a) = {-a} := by
  ext r
  rw [gomesPolynomialFirstOrderEigenvalues_mem_iff]
  simp only [← map_add, C_eq_zero, Set.mem_singleton_iff]
  exact add_eq_zero_iff_eq_neg'

/-- Every nonconstant coefficient has empty polynomial point spectrum. -/
theorem gomesPolynomialFirstOrderEigenvalues_nonconstant
    (A : {A : ℝ[X] // A.derivative ≠ 0}) :
    gomesPolynomialFirstOrderEigenvalues A.val = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro r h
  have he := (gomesPolynomialFirstOrderEigenvalues_mem_iff A.val r).mp h
  have hd := congrArg Polynomial.derivative he
  apply A.property
  simpa only [derivative_add, derivative_C, add_zero, derivative_zero] using hd

/-- Polynomial eigenstate data agrees with the algebraic spectrum exactly for constant coefficients. -/
theorem gomesPolynomialFirstOrderEigenvalues_spectrum_eq_iff (A : ℝ[X]) :
    gomesPolynomialFirstOrderEigenvalues A = spectrum ℝ (gomesPolynomialFirstOrderLinearMap A) ↔
      A.derivative = 0 := by
  constructor
  · intro h
    by_contra hd
    have he := gomesPolynomialFirstOrderEigenvalues_nonconstant ⟨A, hd⟩
    have hs := gomesPolynomialFirstOrderLinearMap_nonconstant_spectrum ⟨A, hd⟩
    rw [he, hs] at h
    exact Set.notMem_empty 0 (h.symm ▸ Set.mem_univ 0)
  · intro hd
    rw [eq_C_of_derivative_eq_zero hd, gomesPolynomialFirstOrderEigenvalues_constant,
      gomesPolynomialFirstOrderLinearMap_constant_spectrum]

end GaloisForLFunctions.HTGeometry
