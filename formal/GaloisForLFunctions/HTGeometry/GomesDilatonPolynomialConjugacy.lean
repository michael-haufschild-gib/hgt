import GaloisForLFunctions.HTGeometry.GomesPolynomialConnectionClassification
import GaloisForLFunctions.HTGeometry.GomesDilatonPolynomialPotential

/-!
# Linear conjugacy of polynomial dilaton connections

Apply the scalar connection normal form to the corpus's half-logarithmic derivative
A = H'/2. Non-affine profiles retain only their degree under arbitrary real linear
changes of polynomial coordinates. Affine profiles retain their slope. This is an
algebraic classification, without asserting conjugacy of the Schwartz Hamiltonians.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- Multiplication by one half preserves the profile derivative's degree. -/
theorem gomesDilatonConnectionPolynomial_natDegree (H : ℝ[X]) :
    (gomesDilatonConnectionPolynomial H).natDegree = H.derivative.natDegree := by
  unfold gomesDilatonConnectionPolynomial
  exact natDegree_C_mul (div_ne_zero one_ne_zero two_ne_zero)

/-- The dilaton connection degree is exactly the profile degree minus one. -/
theorem gomesDilatonConnectionPolynomial_degree_from_profile (H : ℝ[X]) :
    (gomesDilatonConnectionPolynomial H).natDegree = H.natDegree - 1 := by
  rw [gomesDilatonConnectionPolynomial_natDegree, natDegree_derivative]

/-- Complete algebraic conjugacy classification in terms of profile derivatives. -/
theorem gomesDilatonPolynomialConnection_intertwiner_iff (H K : ℝ[X]) :
    Nonempty (GomesPolynomialConnectionIntertwiner
      (gomesDilatonConnectionPolynomial H) (gomesDilatonConnectionPolynomial K)) ↔
        H.derivative = K.derivative ∨
          (H.derivative.derivative ≠ 0 ∧ K.derivative.derivative ≠ 0 ∧
            H.derivative.natDegree = K.derivative.natDegree) := by
  simp only [gomesPolynomialConnection_intertwiner_iff, gomesDilatonConnectionPolynomial_eq_iff, ne_eq,
    gomesDilatonConnectionPolynomial_derivative_zero_iff,
    gomesDilatonConnectionPolynomial_derivative_zero_iff,
    gomesDilatonConnectionPolynomial_natDegree, gomesDilatonConnectionPolynomial_natDegree]

/-- A non-affine profile has positive degree, as required to cancel the derivative degree shift. -/
theorem gomesDilatonNonaffineProfile_degree_pos
    (H : {H : ℝ[X] // H.derivative.derivative ≠ 0}) : 0 < H.val.natDegree := by
  apply Nat.pos_of_ne_zero
  apply derivative_ne_zero.mp
  intro h
  exact H.property (by rw [h, derivative_zero])

/-- Among non-affine profiles, profile degree alone completely classifies polynomial connection conjugacy. -/
theorem gomesDilatonPolynomialConnection_nonaffine_intertwiner_iff
    (H K : {H : ℝ[X] // H.derivative.derivative ≠ 0}) :
    Nonempty (GomesPolynomialConnectionIntertwiner
      (gomesDilatonConnectionPolynomial H.val) (gomesDilatonConnectionPolynomial K.val)) ↔
        H.val.natDegree = K.val.natDegree := by
  let A : GomesNonconstantPolynomialCoefficient :=
    ⟨gomesDilatonConnectionPolynomial H.val,
      mt (gomesDilatonConnectionPolynomial_derivative_zero_iff H.val).mp H.property⟩
  let B : GomesNonconstantPolynomialCoefficient :=
    ⟨gomesDilatonConnectionPolynomial K.val,
      mt (gomesDilatonConnectionPolynomial_derivative_zero_iff K.val).mp K.property⟩
  rw [gomesPolynomialConnection_nonconstant_intertwiner_iff A B]
  change (gomesDilatonConnectionPolynomial H.val).natDegree =
    (gomesDilatonConnectionPolynomial K.val).natDegree ↔ _
  rw [gomesDilatonConnectionPolynomial_degree_from_profile,
    gomesDilatonConnectionPolynomial_degree_from_profile]
  have hh := gomesDilatonNonaffineProfile_degree_pos H
  have hk := gomesDilatonNonaffineProfile_degree_pos K
  constructor
  · intro he
    have hH := Nat.sub_add_cancel hh
    have hK := Nat.sub_add_cancel hk
    linarith
  · intro he; rw [he]

/-- The exact number of polynomial output obstructions is the profile degree minus one. -/
theorem gomesDilatonPolynomialConnection_cokernel_finrank (H : ℝ[X]) :
    Module.finrank ℝ (GomesPolynomialConnectionCokernel (gomesDilatonConnectionPolynomial H)) =
      H.natDegree - 1 := by
  rw [gomesPolynomialConnectionCokernel_finrank_all,
    gomesDilatonConnectionPolynomial_degree_from_profile]

/-- Affine profile connections are conjugate exactly when their slopes agree. -/
theorem gomesDilatonPolynomialConnection_affine_intertwiner_iff (a b c d : ℝ) :
    Nonempty (GomesPolynomialConnectionIntertwiner
      (gomesDilatonConnectionPolynomial (C a * X + C b))
      (gomesDilatonConnectionPolynomial (C c * X + C d))) ↔ a = c := by
  rw [gomesDilatonPolynomialConnection_intertwiner_iff]
  simp

end GaloisForLFunctions.HTGeometry
