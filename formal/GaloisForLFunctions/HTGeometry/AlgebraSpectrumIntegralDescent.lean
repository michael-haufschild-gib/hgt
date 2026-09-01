import GaloisForLFunctions.HTGeometry.AlgebraSpectrumIntegralSurjective
import GaloisForLFunctions.HTGeometry.MvPolynomialAwayComplexPoints

/-!
# Path connectedness descends along an injective integral map of complex algebras

All the algebra/tower instances of the integral extension are introduced *inside* the proof, so a
call site never has to unify against them.  This is what keeps the horizon instantiation cheap.
-/

namespace GaloisForLFunctions.HTGeometry

namespace AlgSpec

/-- **Path connectedness descends along an injective integral complex-algebra map.** -/
theorem pathConnectedSpace_of_injective_integral
    {A B : Type*} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) (hinj : Function.Injective f)
    (hint : ∀ b : B, ∃ p : Polynomial A, p.Monic ∧ Polynomial.eval₂ f.toRingHom b p = 0)
    [PathConnectedSpace (AlgSpec B)] : PathConnectedSpace (AlgSpec A) := by
  letI : Algebra A B := f.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq fun c => (f.commutes c).symm
  haveI : Algebra.IsIntegral A B := by
    constructor
    intro b
    obtain ⟨p, hp, hpe⟩ := hint b
    exact ⟨p, hp, hpe⟩
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  exact pathConnectedSpace_of_continuous_surjective
    (continuous_precomp (IsScalarTower.toAlgHom ℂ A B)) surjective_precomp_of_isIntegral

end AlgSpec

end GaloisForLFunctions.HTGeometry
