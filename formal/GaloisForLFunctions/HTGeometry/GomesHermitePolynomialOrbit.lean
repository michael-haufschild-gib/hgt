import GaloisForLFunctions.HTGeometry.GomesPolynomialStructuredConjugacy
import GaloisForLFunctions.HTGeometry.HermitePolynomialSpan

/-!
# Hermite creation as a polynomial connection orbit model

Reuse the corpus Hermite degree theorem to construct its exact basis. Creation
shifts this basis by one. The connection orbit basis then transports every
coefficient-degree-one connection to the existing Hermite creation operation.
-/

noncomputable section
open Polynomial Real

namespace GaloisForLFunctions.HTGeometry

/-- Scalar relating the corpus Hermite creation step to a first-order connection. -/
def gomesHermiteConnectionScale : ℝ := -(1 / (2 * π))

/-- The creation normalization is nonzero. -/
theorem gomesHermiteConnectionScale_ne_zero : gomesHermiteConnectionScale ≠ 0 :=
  neg_ne_zero.mpr (div_ne_zero one_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero))

/-- The creation normalization has the opposite derivative sign. -/
theorem gomesHermiteConnectionScale_negative : gomesHermiteConnectionScale < 0 :=
  neg_lt_zero.mpr (div_pos zero_lt_one (mul_pos zero_lt_two Real.pi_pos))

/-- The actual degree-one connection whose scalar multiple is Hermite creation. -/
def gomesHermiteConnectionCoefficient : GomesNonconstantPolynomialCoefficient :=
  ⟨C (2 * (2 * π)) * X, by
    rw [derivative_ne_zero,
      natDegree_C_mul_X _ (mul_ne_zero two_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero))]
    exact one_ne_zero⟩

/-- The Hermite connection has one polynomial orbit chain. -/
theorem gomesHermiteConnectionCoefficient_degree : gomesHermiteConnectionCoefficient.val.natDegree = 1 :=
  natDegree_C_mul_X _ (mul_ne_zero two_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero))

/-- The existing Hermite step, bundled as a real-linear map using its connection formula. -/
def gomesHermiteStepLinearMap : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  gomesHermiteConnectionScale •
    gomesPolynomialFirstOrderLinearMap gomesHermiteConnectionCoefficient.val

/-- The bundled operator agrees with the corpus's actual Hermite creation polynomial. -/
theorem gomesHermiteStepLinearMap_apply (P : ℝ[X]) : gomesHermiteStepLinearMap P = hermiteStep P := by
  change (-(1 / (2 * π))) • (P.derivative - (C (2 * (2 * π)) * X) * P) = hermiteStep P
  rw [smul_eq_C_mul]
  unfold hermiteStep
  apply Polynomial.funext
  intro x
  simp only [eval_mul, eval_sub, eval_C, eval_X, eval_ofNat]
  field_simp [Real.pi_ne_zero]
  ring

/-- The corpus Hermite family as its already-proved degree-indexed polynomial sequence. -/
def gomesHermitePolynomialSequence : Polynomial.Sequence ℝ where
  elems' := hermitePoly
  degree_eq' := hermitePoly_degree

/-- The complete Hermite basis, using the existing degree and leading coefficient theorems. -/
def gomesHermitePolynomialBasis : Module.Basis ℕ ℝ ℝ[X] :=
  gomesHermitePolynomialSequence.basis fun n => by
    change IsUnit (hermitePoly n).leadingCoeff
    rw [hermitePoly_leadingCoeff]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero n two_ne_zero)

/-- The newly bundled basis consists of the actual corpus Hermite polynomials. -/
theorem gomesHermitePolynomialBasis_apply (n : ℕ) : gomesHermitePolynomialBasis n = hermitePoly n :=
  gomesHermitePolynomialSequence.basis_eq_self _ n

/-- Creation is exactly the forward shift in the Hermite basis. -/
theorem gomesHermiteStepLinearMap_basis_shift (n : ℕ) :
    gomesHermiteStepLinearMap (gomesHermitePolynomialBasis n) = gomesHermitePolynomialBasis (n + 1) := by
  rw [gomesHermitePolynomialBasis_apply, gomesHermiteStepLinearMap_apply,
    gomesHermitePolynomialBasis_apply]
  exact (hermitePoly_succ n).symm

/-- Transport a nonconstant connection's orbit coordinates to the Hermite basis. -/
def gomesPolynomialConnectionHermiteTransport (A : GomesNonconstantPolynomialCoefficient) :
    ℝ[X] ≃ₗ[ℝ] ℝ[X] :=
  (gomesPolynomialConnectionOrbitBasis A).equiv gomesHermitePolynomialBasis (Equiv.refl ℕ)

/-- Transport keeps the natural orbit index. -/
theorem gomesPolynomialConnectionHermiteTransport_basis
    (A : GomesNonconstantPolynomialCoefficient) (n : ℕ) :
    gomesPolynomialConnectionHermiteTransport A (gomesPolynomialConnectionOrbitBasis A n) =
      gomesHermitePolynomialBasis n :=
  (gomesPolynomialConnectionOrbitBasis A).equiv_apply n gomesHermitePolynomialBasis (Equiv.refl ℕ)

/-- The canonical orbit transport intertwines with creation exactly for one-chain connections. -/
theorem gomesPolynomialConnectionHermiteTransport_intertwines_iff
    (A : GomesNonconstantPolynomialCoefficient) :
    (gomesPolynomialConnectionHermiteTransport A).toLinearMap.comp
        (gomesPolynomialFirstOrderLinearMap A.val) =
      gomesHermiteStepLinearMap.comp (gomesPolynomialConnectionHermiteTransport A).toLinearMap ↔
        A.val.natDegree = 1 := by
  constructor
  · intro h
    have he := congrArg (fun f : ℝ[X] →ₗ[ℝ] ℝ[X] =>
      f (gomesPolynomialConnectionOrbitBasis A 0)) h
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      gomesPolynomialConnectionOrbitBasis_shift, gomesPolynomialConnectionHermiteTransport_basis,
      gomesHermiteStepLinearMap_basis_shift, zero_add] at he
    exact gomesHermitePolynomialBasis.injective he
  · intro h
    apply (gomesPolynomialConnectionOrbitBasis A).ext
    intro n
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      gomesPolynomialConnectionOrbitBasis_shift, gomesPolynomialConnectionHermiteTransport_basis,
      gomesHermiteStepLinearMap_basis_shift, h]

/-- Every degree-one coefficient connection admits the existing Hermite creation operator as a normal form. -/
theorem gomesPolynomialConnection_Hermite_normal_form (A : {A : ℝ[X] // A.natDegree = 1}) :
    ∃ E : ℝ[X] ≃ₗ[ℝ] ℝ[X], E.toLinearMap.comp (gomesPolynomialFirstOrderLinearMap A.val) =
      gomesHermiteStepLinearMap.comp E.toLinearMap := by
  let B : GomesNonconstantPolynomialCoefficient :=
    ⟨A.val, by rw [derivative_ne_zero, A.property]; exact one_ne_zero⟩
  exact ⟨gomesPolynomialConnectionHermiteTransport B,
    (gomesPolynomialConnectionHermiteTransport_intertwines_iff B).mpr A.property⟩

end GaloisForLFunctions.HTGeometry
