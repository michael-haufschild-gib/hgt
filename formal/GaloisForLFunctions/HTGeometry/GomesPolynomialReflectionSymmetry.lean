import GaloisForLFunctions.HTGeometry.GomesFormalExponentialTranslation
import GaloisForLFunctions.HTGeometry.GomesPolynomialDerivativePowerCommutant

/-!
# All affine polynomial reflections as actual second-derivative symmetries

Reflection P(X) ↦ P(c-X) is defined for every center parameter, including zero.
It anticommutes with the first derivative and commutes with its square. Its
factorization into parity and actual translation will determine its formal matrix.
-/

noncomputable section
open Polynomial
namespace GaloisForLFunctions.HTGeometry
variable (K : Type*) [Field K] [CharZero K]

/-- Actual substitution by c-X as a polynomial endomorphism. -/
def gomesPolynomialReflectionEnd (c : K) : Module.End K K[X] :=
  (Polynomial.aeval (C c - X : K[X])).toLinearMap

omit [CharZero K] in
/-- The reflection endomorphism is literal polynomial substitution. -/
theorem gomesPolynomialReflectionEnd_apply (c : K) (P : K[X]) :
    gomesPolynomialReflectionEnd K c P = P.comp (C c - X) := rfl

omit [CharZero K] in
/-- Every affine reflection anticommutes with actual polynomial differentiation. -/
theorem gomesPolynomialReflectionEnd_derivative (c : K) :
    (Polynomial.derivative : Module.End K K[X]) * gomesPolynomialReflectionEnd K c =
      -(gomesPolynomialReflectionEnd K c * Polynomial.derivative) := by
  apply LinearMap.ext
  intro P
  change (P.comp (C c - X)).derivative = -P.derivative.comp (C c - X)
  rw [Polynomial.derivative_comp]
  simp

omit [CharZero K] in
/-- Every affine reflection is an involution on all polynomials. -/
theorem gomesPolynomialReflectionEnd_sq (c : K) :
    gomesPolynomialReflectionEnd K c ^ (2 : ℕ) = 1 := by
  apply LinearMap.ext
  intro P
  rw [pow_two, Module.End.mul_apply]
  change (P.comp (C c - X)).comp (C c - X) = P
  rw [Polynomial.comp_assoc]
  simp

omit [CharZero K] in
/-- Every center gives an actual symmetry of the second derivative. -/
theorem gomesPolynomialReflectionEnd_mem (c : K) :
    gomesPolynomialReflectionEnd K c ∈ gomesPolynomialDerivativePowerCommutantAlgebra K 2 := by
  rw [gomesPolynomialDerivativePowerCommutantAlgebra, gomesCentralizerSingleton_mem_iff]
  apply LinearMap.ext
  intro P
  rw [pow_two, Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply]
  have h (Q : K[X]) : (gomesPolynomialReflectionEnd K c Q).derivative =
      -gomesPolynomialReflectionEnd K c Q.derivative :=
    congrArg (fun L : Module.End K K[X] => L Q) (gomesPolynomialReflectionEnd_derivative K c)
  rw [h, map_neg, h, neg_neg]

/-- Affine reflection inside the full second-derivative commutant. -/
def gomesPolynomialReflectionSymmetry (c : K) : GomesPolynomialDerivativePowerCommutant K 2 :=
  ⟨gomesPolynomialReflectionEnd K c, gomesPolynomialReflectionEnd_mem K c⟩

omit [CharZero K] in
/-- Every affine reflection is parity after actual polynomial translation. -/
theorem gomesPolynomialReflectionEnd_eq_parity_taylor (c : K) :
    gomesPolynomialReflectionEnd K c = gomesPolynomialReflectionEnd K 0 * Polynomial.taylor c := by
  apply LinearMap.ext
  intro P
  rw [Module.End.mul_apply, gomesPolynomialReflectionEnd_apply, Polynomial.taylor_apply,
    gomesPolynomialReflectionEnd_apply, Polynomial.comp_assoc]
  simp [sub_eq_add_neg, add_comm]

/-- Parity acts diagonally on every divided monomial. -/
theorem gomesPolynomialReflectionEnd_zero_basis (n : ℕ) :
    gomesPolynomialReflectionEnd K 0 (gomesDividedMonomialBasis K n) =
      (-1 : K) ^ n • gomesDividedMonomialBasis K n := by
  rw [gomesDividedMonomialBasis_apply]
  change (Polynomial.aeval (C (0 : K) - X : K[X])) (((n.factorial : K)⁻¹) • (X : K[X]) ^ n) = _
  rw [map_smul, map_pow, Polynomial.aeval_X]
  have hx : (C (0 : K) - X : K[X]) = (-1 : K) • X := by simp
  rw [hx, _root_.smul_pow, smul_comm]

end GaloisForLFunctions.HTGeometry
