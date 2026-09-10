import GaloisForLFunctions.HTGeometry.GomesPolynomialConnectionClassification

/-!
# Coefficient information lost under abstract linear conjugacy

The reconstruction experiment prompted by arXiv:2607.24901 section 4 distinguishes
an operator from its presentation. Every constant perturbation of a nonconstant
coefficient is conjugate to the original, despite the distinct coefficient data.
The statement concerns real linear maps of polynomials, not geometric gauge maps.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- Adding a constant keeps a nonconstant coefficient within its degree sector. -/
def gomesPolynomialConnectionShiftedCoefficient
    (A : GomesNonconstantPolynomialCoefficient) (r : ℝ) : GomesNonconstantPolynomialCoefficient :=
  ⟨A.val + C r, by simpa only [derivative_add, derivative_C, add_zero] using A.property⟩

/-- Every constant perturbation in the nonconstant sector has an invertible intertwiner. -/
theorem gomesPolynomialConnection_nonconstant_shift_conjugate
    (A : GomesNonconstantPolynomialCoefficient) (r : ℝ) :
    Nonempty (GomesPolynomialConnectionIntertwiner A.val (A.val + C r)) := by
  apply (gomesPolynomialConnection_nonconstant_intertwiner_iff A
    (gomesPolynomialConnectionShiftedCoefficient A r)).mpr
  exact natDegree_add_C.symm

/-- Across all coefficients, a shift is conjugate exactly when it is zero or the coefficient is nonconstant. -/
theorem gomesPolynomialConnection_shift_conjugate_iff (A : ℝ[X]) (r : ℝ) :
    Nonempty (GomesPolynomialConnectionIntertwiner A (A + C r)) ↔
      r = 0 ∨ A.derivative ≠ 0 := by
  by_cases ha : A.derivative = 0
  · simp only [ha, ne_eq, not_true_eq_false, or_false]
    have hca := eq_C_of_derivative_eq_zero ha
    rw [hca, ← map_add, gomesPolynomialConnection_constant_intertwiner_iff]
    constructor
    · intro h; linarith
    · rintro rfl; exact (add_zero _).symm
  · exact iff_of_true (gomesPolynomialConnection_nonconstant_shift_conjugate ⟨A, ha⟩ r)
      (Or.inr ha)

/-- Constant shifts provide distinct coefficient presentations indexed by every real number. -/
theorem gomesPolynomialConnection_shift_coefficients_injective (A : ℝ[X]) :
    Function.Injective (fun r : ℝ => A + C r) := by
  intro r s h
  exact C_injective (add_left_cancel h)

/-- Every pair in the nonconstant constant-shift family is linearly conjugate. -/
theorem gomesPolynomialConnection_shift_family_conjugate
    (A : GomesNonconstantPolynomialCoefficient) (r s : ℝ) :
    Nonempty (GomesPolynomialConnectionIntertwiner (A.val + C r) (A.val + C s)) := by
  apply (gomesPolynomialConnection_nonconstant_intertwiner_iff
    (gomesPolynomialConnectionShiftedCoefficient A r)
    (gomesPolynomialConnectionShiftedCoefficient A s)).mpr
  simp only [gomesPolynomialConnectionShiftedCoefficient, natDegree_add_C]

/-- Every nonzero constant perturbation witnesses distinct coefficients with conjugate operators. -/
theorem gomesPolynomialConnection_nonconstant_reconstruction_failure
    (A : GomesNonconstantPolynomialCoefficient) (r : {r : ℝ // r ≠ 0}) :
    A.val + C r.val ≠ A.val ∧
      Nonempty (GomesPolynomialConnectionIntertwiner A.val (A.val + C r.val)) := by
  refine ⟨?_, gomesPolynomialConnection_nonconstant_shift_conjugate A r.val⟩
  intro h
  apply r.property
  apply gomesPolynomialConnection_shift_coefficients_injective A.val
  simpa only [map_zero, add_zero] using h

end GaloisForLFunctions.HTGeometry
