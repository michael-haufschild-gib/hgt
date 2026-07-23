import GaloisForLFunctions.HTGeometry.EllipticGammaInversion
import GaloisForLFunctions.HTGeometry.EllipticGammaProductCommensurableFactorization

/-!
# Reflection of commensurable elliptic-Gamma factorization

Additive period commensurability flattens the elliptic-Gamma product into a finite residue-class
family, while additive reflection inverts the original product.  Applying the same factorization
on both sides shows that reflection and Felder--Varchenko flattening commute exactly.
-/

namespace GaloisForLFunctions

noncomputable section

/-- **Commensurable reflection-factorization law.**  Every additive-period commensurable
elliptic-Gamma family product is inverted by the reflected additive coordinate. -/
theorem ellipticGammaCommensurableFamilyProduct_additiveReflection
    {σ τ z : ℂ} {m n : ℕ} [NeZero m] [NeZero n]
    (hperiod : ∃ k : ℤ, (m : ℂ) * σ = (n : ℂ) * τ + (k : ℂ)) :
    ellipticGammaCommensurableFamilyProduct
        (ellipticNome σ) (ellipticNome τ) (ellipticNome σ ^ m)
        (ellipticThetaCoordinate τ (σ - z)) m n =
      (ellipticGammaCommensurableFamilyProduct
        (ellipticNome σ) (ellipticNome τ) (ellipticNome σ ^ m)
        (ellipticThetaCoordinate τ z) m n)⁻¹ := by
  have hz := ellipticGammaProduct_additivePeriod_factorization
    (σ := σ) (τ := τ) (z := z) hperiod
  have href := ellipticGammaProduct_additivePeriod_factorization
    (σ := σ) (τ := τ) (z := σ - z) hperiod
  calc
    ellipticGammaCommensurableFamilyProduct
          (ellipticNome σ) (ellipticNome τ) (ellipticNome σ ^ m)
          (ellipticThetaCoordinate τ (σ - z)) m n =
        ellipticGammaProduct σ τ (σ - z) := href.symm
    _ = (ellipticGammaProduct σ τ z)⁻¹ :=
      ellipticGammaProduct_reflection σ τ z
    _ = (ellipticGammaCommensurableFamilyProduct
          (ellipticNome σ) (ellipticNome τ) (ellipticNome σ ^ m)
          (ellipticThetaCoordinate τ z) m n)⁻¹ := congrArg Inv.inv hz

end

end GaloisForLFunctions
