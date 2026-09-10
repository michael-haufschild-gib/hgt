import GaloisForLFunctions.HTGeometry.GomesPolynomialCommutantReconstruction
import GaloisForLFunctions.HTGeometry.GomesDilatonStructuredReconstruction
import GaloisForLFunctions.HTGeometry.GomesDilatonCommutatorObservations

/-!
# Dilaton profiles reconstructed from polynomial connection symmetries

For the corpus dilaton connection coefficient `H'/2`, the full concrete polynomial
symmetry algebra retains `H''`. Its profile ambiguity is exactly affine addition.
Anchoring the slope recovers the actual Schwartz supercharge; anchoring both slope
and value recovers the entire polynomial profile.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- The full real-linear polynomial symmetry algebra of a dilaton connection. -/
def gomesDilatonPolynomialCommutant (H : ℝ[X]) : Subalgebra ℝ (Module.End ℝ ℝ[X]) :=
  gomesPolynomialConnectionCommutantAlgebra (gomesDilatonConnectionPolynomial H)

/-- Differentiation commutes with forming the half-logarithmic connection coefficient. -/
theorem gomesDilatonConnectionPolynomial_derivative (H : ℝ[X]) :
    (gomesDilatonConnectionPolynomial H).derivative =
      gomesDilatonConnectionPolynomial H.derivative := by
  simp only [gomesDilatonConnectionPolynomial, derivative_C_mul]

/-- The full polynomial symmetry algebra recovers exactly the second profile derivative. -/
theorem gomesDilatonPolynomialCommutant_eq_iff (H K : ℝ[X]) :
    gomesDilatonPolynomialCommutant H = gomesDilatonPolynomialCommutant K ↔
      H.derivative.derivative = K.derivative.derivative := by
  rw [gomesDilatonPolynomialCommutant, gomesDilatonPolynomialCommutant,
    gomesPolynomialConnectionCommutant_eq_iff, gomesDilatonConnectionPolynomial_derivative,
    gomesDilatonConnectionPolynomial_derivative, gomesDilatonConnectionPolynomial_eq_iff]

/-- Full polynomial symmetry data and the existing commutator record have exactly the same fibers. -/
theorem gomesDilatonPolynomialCommutant_record_iff (H K : ℝ[X]) :
    gomesDilatonPolynomialCommutant H = gomesDilatonPolynomialCommutant K ↔
      gomesDilatonCommutatorRecord H = gomesDilatonCommutatorRecord K := by
  rw [gomesDilatonPolynomialCommutant_eq_iff, gomesDilatonCommutatorRecord_apply,
    gomesDilatonCommutatorRecord_apply, neg_inj]

/-- The exact profile ambiguity of the polynomial symmetry algebra is an arbitrary affine addition. -/
theorem gomesDilatonPolynomialCommutant_profile_fibers (H K : ℝ[X]) :
    gomesDilatonPolynomialCommutant H = gomesDilatonPolynomialCommutant K ↔
      ∃ a b : ℝ, H = K + C a * X + C b := by
  rw [gomesDilatonPolynomialCommutant_record_iff, gomesDilatonCommutatorRecord_eq_iff]

/-- Equality of polynomial symmetry algebras is equivalent to equality of actual Schwartz commutators. -/
theorem gomesDilatonPolynomialCommutant_schwartz_commutator_iff (H K : ℝ[X]) :
    gomesDilatonPolynomialCommutant H = gomesDilatonPolynomialCommutant K ↔
      gomesDilatonCommutatorCLM H = gomesDilatonCommutatorCLM K := by
  rw [gomesDilatonPolynomialCommutant_record_iff, gomesDilatonCommutatorCLM_eq_iff]

/-- One existing Gaussian probe carries exactly the profile information in the entire polynomial symmetry algebra. -/
theorem gomesDilatonPolynomialCommutant_gaussian_probe_iff (H K : ℝ[X]) :
    gomesDilatonPolynomialCommutant H = gomesDilatonPolynomialCommutant K ↔
      gomesDilatonGaussianProbe H = gomesDilatonGaussianProbe K := by
  rw [gomesDilatonPolynomialCommutant_record_iff, gomesDilatonGaussianProbe_eq_iff]

/-- Every affine profile perturbation leaves all polynomial connection symmetries unchanged. -/
theorem gomesDilatonPolynomialCommutant_affine_invariance (H : ℝ[X]) (a b : ℝ) :
    gomesDilatonPolynomialCommutant (H + C a * X + C b) = gomesDilatonPolynomialCommutant H :=
  (gomesDilatonPolynomialCommutant_profile_fibers _ _).mpr ⟨a, b, rfl⟩

/-- Anchoring the first derivative removes the slope ambiguity and recovers the actual supercharge. -/
theorem gomesDilatonPolynomialCommutant_anchored_supercharge_iff (H K : ℝ[X]) :
    (gomesDilatonPolynomialCommutant H = gomesDilatonPolynomialCommutant K ∧
      H.derivative.coeff 0 = K.derivative.coeff 0) ↔
        dilatonSuperchargeCLM H = dilatonSuperchargeCLM K := by
  rw [gomesDilatonPolynomialCommutant_eq_iff, gomesDilatonConnection_eq_iff]
  constructor
  · rintro ⟨h, h0⟩
    apply (gomesPolynomialConnectionCommutant_anchored_iff H.derivative K.derivative).mp
    exact ⟨(gomesPolynomialConnectionCommutant_eq_iff _ _).mpr h, h0⟩
  · intro h
    exact ⟨congrArg Polynomial.derivative h, congrArg (fun P : ℝ[X] => P.coeff 0) h⟩

/-- Two scalar anchors turn full polynomial symmetry data into exact profile reconstruction. -/
theorem gomesDilatonPolynomialCommutant_anchored_profile_iff (H K : ℝ[X]) :
    (gomesDilatonPolynomialCommutant H = gomesDilatonPolynomialCommutant K ∧
      H.derivative.coeff 0 = K.derivative.coeff 0 ∧ H.coeff 0 = K.coeff 0) ↔ H = K := by
  constructor
  · rintro ⟨h, h1, h0⟩
    have hs := (gomesDilatonPolynomialCommutant_anchored_supercharge_iff H K).mp ⟨h, h1⟩
    have hd := (gomesDilatonConnection_eq_iff H K).mp hs
    exact (gomesPolynomialConnectionCommutant_anchored_iff H K).mp
      ⟨(gomesPolynomialConnectionCommutant_eq_iff H K).mpr hd, h0⟩
  · rintro rfl
    exact ⟨rfl, rfl, rfl⟩

end GaloisForLFunctions.HTGeometry
