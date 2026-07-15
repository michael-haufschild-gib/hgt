import GaloisForLFunctions.HTGeometry.EllipticGammaCommensurableFactorization
import GaloisForLFunctions.HTGeometry.EllipticGammaProduct

/-!
# Commensurable factorization of the actual elliptic-gamma product

This identifies the additive product already used by the elliptic-gamma hierarchy with the
multiplicative product and transfers the unconditional residue-class factorization to it.
-/

open Complex
open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

/-- The existing additive elliptic-gamma product is the same actual product in its aligned
multiplicative coordinate. -/
theorem ellipticGammaProduct_eq_multiplicativeProduct (σ τ z : ℂ) :
    ellipticGammaProduct σ τ z =
      ellipticGammaMultiplicativeProduct (ellipticNome σ) (ellipticNome τ)
        (ellipticThetaCoordinate τ z) := by
  rfl

/-- Felder--Varchenko factorization for the actual additive elliptic-gamma product, stated in the
multiplicative coordinate in which commensurability is intrinsic. -/
theorem ellipticGammaProduct_commensurable_factorization
    {σ τ P z : ℂ} {m n : ℕ} [NeZero m] [NeZero n]
    (hp : ellipticNome σ ^ m = P) (hq : ellipticNome τ ^ n = P) :
    ellipticGammaProduct σ τ z =
      ellipticGammaCommensurableFamilyProduct
        (ellipticNome σ) (ellipticNome τ) P (ellipticThetaCoordinate τ z) m n := by
  rw [ellipticGammaProduct_eq_multiplicativeProduct]
  exact ellipticGammaMultiplicativeProduct_flattened_factorization
    (ellipticNome_ne_zero σ) (ellipticNome_ne_zero τ)
    (ellipticThetaCoordinate_ne_zero τ z) hp hq

end

end GaloisForLFunctions
