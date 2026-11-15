import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.RationalFunctionFiniteConstants
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerBranchIrreducibility

/-!
# Literal constant extension of Kummer function fields

Tensoring the root-adjoined presentation commutes with finite extension
of constants. The rational base tensor is a field, and the same simple
branch point keeps the mapped radical polynomial Eisenstein. Thus the
literal scalar tensor is exactly the fixed equation over the new constants.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
open scoped TensorProduct
variable (K E : Type*) [Field K] [Field E] [Algebra K E]

/-- Extending coefficients preserves the exact Kummer branch polynomial. -/
theorem kummerBranch_constant_map (c : Kˣ) (b R : ℕ) :
    (kummerBranch c b R).map (algebraMap K E) =
      kummerBranch (Units.map (algebraMap K E).toMonoidHom c) b R := by
  simp only [kummerBranch, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_one]
  rfl

/-- The radical polynomial maps to the same equation over the enlarged rational function field. -/
theorem kummerBranchFieldPolynomial_constant_map [FiniteDimensional K E] (c : Kˣ) (b R n : ℕ) :
    (kummerBranchFieldPolynomial c b R n).map (rationalConstantInclusion K E).toRingHom =
      kummerBranchFieldPolynomial (Units.map (algebraMap K E).toMonoidHom c) b R n := by
  change (X ^ (n + 1) - C (algebraMap K[X] (FractionRing K[X]) (kummerBranch c b R))).map
    (rationalConstantInclusion K E).toRingHom = _
  rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  change X ^ (n + 1) - C (rationalConstantInclusion K E
    (algebraMap K[X] (FractionRing K[X]) (kummerBranch c b R))) = _
  rw [rationalConstantInclusion_polynomial, kummerBranch_constant_map]
  rfl

/-- The actual scalar tensor product of a Kummer function field is the same fixed-degree Kummer field over the enlarged constants. -/
def kummerConstantTensorEquiv [FiniteDimensional K E] (c : Kˣ) (b R n : ℕ) :
    (E ⊗[K] KummerBranchField c b R n) ≃ₐ[E]
      KummerBranchField (Units.map (algebraMap K E).toMonoidHom c) b R n := by
  let f := kummerBranchFieldPolynomial c b R n
  let q : Polynomial (E ⊗[K] FractionRing K[X]) :=
    f.map Algebra.TensorProduct.includeRight.toRingHom
  let fE := kummerBranchFieldPolynomial (Units.map (algebraMap K E).toMonoidHom c) b R n
  have hq : q.map (rationalConstantTensorEquiv K E).toRingHom = fE := by
    rw [show q = f.map Algebra.TensorProduct.includeRight.toRingHom from rfl, Polynomial.map_map]
    change f.map (rationalConstantInclusion K E).toRingHom = fE
    exact kummerBranchFieldPolynomial_constant_map K E c b R n
  exact (AdjoinRoot.tensorAlgEquiv f q rfl).trans
    (AdjoinRoot.mapAlgEquiv (rationalConstantTensorEquiv K E) q fE (Associated.of_eq hq))

/-- Every finite constant extension of the Kummer function field remains an integral domain. -/
theorem kummerConstantTensor_isDomain [FiniteDimensional K E] (c : Kˣ) (b R n : ℕ) :
    IsDomain (E ⊗[K] KummerBranchField c b R n) :=
  (kummerConstantTensorEquiv K E c b R n).toMulEquiv.isDomain

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
