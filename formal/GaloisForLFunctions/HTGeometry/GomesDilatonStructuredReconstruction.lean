import GaloisForLFunctions.HTGeometry.GomesPolynomialStructuredConjugacy
import GaloisForLFunctions.HTGeometry.GomesDilatonPolynomialConjugacy

/-!
# Coordinate structure restores the actual dilaton connection data

For the corpus half-logarithmic derivative H'/2, structured polynomial conjugacy
has exactly the same fibers as equality of the actual Schwartz supercharge.
A nonzero linear perturbation of a non-affine profile separates this from arbitrary
polynomial linear conjugacy, which forgets the perturbation.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- Structured polynomial dilaton conjugacy retains precisely the profile derivative. -/
theorem gomesDilatonPolynomialConnection_structured_derivative_iff (H K : ℝ[X]) :
    Nonempty (GomesPolynomialStructuredIntertwiner
      (gomesDilatonConnectionPolynomial H) (gomesDilatonConnectionPolynomial K)) ↔
        H.derivative = K.derivative := by
  rw [gomesPolynomialConnection_structured_intertwiner_iff,
    gomesDilatonConnectionPolynomial_eq_iff]

/-- The retained polynomial coordinate structure recovers equality of the actual Schwartz connection. -/
theorem gomesDilatonPolynomialConnection_structured_supercharge_iff (H K : ℝ[X]) :
    Nonempty (GomesPolynomialStructuredIntertwiner
      (gomesDilatonConnectionPolynomial H) (gomesDilatonConnectionPolynomial K)) ↔
        dilatonSuperchargeCLM H = dilatonSuperchargeCLM K := by
  rw [gomesDilatonPolynomialConnection_structured_derivative_iff, gomesDilatonConnection_eq_iff]

/-- The only profile freedom under structured polynomial conjugacy is a constant shift. -/
theorem gomesDilatonPolynomialConnection_structured_profile_fibers (H K : ℝ[X]) :
    Nonempty (GomesPolynomialStructuredIntertwiner
      (gomesDilatonConnectionPolynomial H) (gomesDilatonConnectionPolynomial K)) ↔
        ∃ c : ℝ, H = K + C c := by
  rw [gomesDilatonPolynomialConnection_structured_supercharge_iff,
    gomesDilatonConnection_constant_iff]

/-- A linear log-profile perturbation adds exactly the prescribed connection constant. -/
theorem gomesDilatonConnectionPolynomial_linear_perturbation (H : ℝ[X]) (r : ℝ) :
    gomesDilatonConnectionPolynomial (H + C (2 * r) * X) =
      gomesDilatonConnectionPolynomial H + C r := by
  unfold gomesDilatonConnectionPolynomial
  rw [derivative_add, derivative_C_mul_X, mul_add, ← map_mul]
  congr 1
  congr 1
  ring

/-- Nonzero linear perturbations exhibit the exact abstract/structured reconstruction gap. -/
theorem gomesDilatonPolynomialConnection_linear_perturbation_boundary
    (H : {H : ℝ[X] // H.derivative.derivative ≠ 0}) (r : {r : ℝ // r ≠ 0}) :
    Nonempty (GomesPolynomialConnectionIntertwiner (gomesDilatonConnectionPolynomial H.val)
        (gomesDilatonConnectionPolynomial (H.val + C (2 * r.val) * X))) ∧
      ¬ Nonempty (GomesPolynomialStructuredIntertwiner (gomesDilatonConnectionPolynomial H.val)
        (gomesDilatonConnectionPolynomial (H.val + C (2 * r.val) * X))) := by
  rw [gomesDilatonConnectionPolynomial_linear_perturbation]
  let A : GomesNonconstantPolynomialCoefficient :=
    ⟨gomesDilatonConnectionPolynomial H.val,
      mt (gomesDilatonConnectionPolynomial_derivative_zero_iff H.val).mp H.property⟩
  exact gomesPolynomialConnection_shift_structure_boundary A r

/-- The actual Schwartz supercharges distinguish every nonzero perturbation in this family. -/
theorem gomesDilatonSupercharge_linear_perturbation_distinct
    (H : {H : ℝ[X] // H.derivative.derivative ≠ 0}) (r : {r : ℝ // r ≠ 0}) :
    dilatonSuperchargeCLM H.val ≠ dilatonSuperchargeCLM (H.val + C (2 * r.val) * X) := by
  intro h
  apply (gomesDilatonPolynomialConnection_linear_perturbation_boundary H r).2
  exact (gomesDilatonPolynomialConnection_structured_supercharge_iff _ _).mpr h

end GaloisForLFunctions.HTGeometry
