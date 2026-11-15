import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerIntegralMonomials
import Mathlib.LinearAlgebra.Basis.SMul


/-!
# A rational basis of integral radical monomials

Rescaling the radical power basis by branch-factor denominators gives
a basis over the rational-function field whose vectors belong to the
integral closure of the polynomial ring.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable {K : Type*} [Field K] (c : Kˣ) (b R n : ℕ)

/-- The defining radical polynomial has exactly the covering degree. -/
theorem kummerBranchFieldPolynomial_natDegree :
    (kummerBranchFieldPolynomial c b R n).natDegree = n + 1 := by
  rw [kummerBranchFieldPolynomial, natDegree_X_pow_sub_C]

private def branchFactorUnit : (FractionRing K[X])ˣ :=
  Units.mk0 (algebraMap K[X] (FractionRing K[X]) (1 - X ^ (b + 1)))
    (fun h => kummerBranchFactor_ne_zero (K := K) b
      (IsFractionRing.injective K[X] _ (h.trans (map_zero _).symm)))

/-- The reduced integral radical monomials form a basis over the rational-function field. -/
def kummerIntegralMonomialBasis :
    Module.Basis (Fin (n + 1)) (FractionRing K[X]) (KummerBranchField c b R n) :=
  ((AdjoinRoot.powerBasis (kummerBranchFieldPolynomial_irreducible c b R n).out.ne_zero).basis.reindex
    (finCongr (kummerBranchFieldPolynomial_natDegree c b R n))).unitsSMul
      (fun i => (branchFactorUnit (K := K) b)⁻¹ ^ (i.val * R / (n + 1)))

/-- The basis vectors are the explicitly reduced radical monomials. -/
theorem kummerIntegralMonomialBasis_apply (i : Fin (n + 1)) :
    kummerIntegralMonomialBasis c b R n i = kummerIntegralMonomial c b R n i.val := by
  rw [kummerIntegralMonomialBasis, Module.Basis.unitsSMul_apply, Module.Basis.reindex_apply,
    PowerBasis.basis_eq_pow, Units.smul_def, Units.val_pow_eq_pow_val,
    Units.val_inv_eq_inv_val, Algebra.smul_def]
  change algebraMap (FractionRing K[X]) (KummerBranchField c b R n)
    ((algebraMap K[X] (FractionRing K[X]) (1 - X ^ (b + 1)))⁻¹ ^ (i.val * R / (n + 1))) *
      AdjoinRoot.root (kummerBranchFieldPolynomial c b R n) ^ i.val = _
  rw [map_pow, map_inv₀, ← IsScalarTower.algebraMap_apply]
  simp only [kummerIntegralMonomial, div_eq_mul_inv, inv_pow, mul_comm]

/-- Every vector in the rational-function basis belongs to the actual integral closure. -/
theorem kummerIntegralMonomialBasis_integral (i : Fin (n + 1)) :
    IsIntegral K[X] (kummerIntegralMonomialBasis c b R n i) := by
  rw [kummerIntegralMonomialBasis_apply]
  exact kummerIntegralMonomial_integral c b R n i.val

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
