import GaloisForLFunctions.HTGeometry.ComplexAffineAlgebraicSmoothPoint
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.RingHom.Surjective
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# Localized multivariable-polynomial cotangent coordinates

The Kähler differentials of a finite multivariable polynomial ring have their coordinate basis.
Localization is formally étale, so base change transports that basis to every local polynomial
ring.  The theorems below identify the transported coordinates of `D f` with the localized
partial derivatives of `f`, including after an arbitrary field base change.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped TensorProduct

noncomputable section

/-- The coordinate basis of the Kähler differentials of a localized complex polynomial ring. -/
noncomputable def localizedMvPolynomialKaehlerBasis
    {σ : Type} [Finite σ] (Q : Ideal (MvPolynomial σ ℂ)) [Q.IsPrime] :
    Module.Basis σ (Localization.AtPrime Q)
      Ω[Localization.AtPrime Q⁄ℂ] := by
  letI : Algebra.FormallyEtale (MvPolynomial σ ℂ) (Localization.AtPrime Q) :=
    Algebra.FormallyEtale.of_isLocalization Q.primeCompl
  exact ((KaehlerDifferential.mvPolynomialBasis ℂ σ).baseChange
      (Localization.AtPrime Q)).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
      ℂ (MvPolynomial σ ℂ) (Localization.AtPrime Q))

/-- In the localized cotangent basis, `D f` has the localized partial derivatives of `f` as its
coordinates. -/
theorem localizedMvPolynomialKaehlerBasis_repr_D_algebraMap
    {σ : Type} [Finite σ] (Q : Ideal (MvPolynomial σ ℂ)) [Q.IsPrime]
    (r : MvPolynomial σ ℂ) (i : σ) :
    (localizedMvPolynomialKaehlerBasis Q).repr
        (KaehlerDifferential.D ℂ (Localization.AtPrime Q)
          (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q) r)) i =
      algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q)
        (MvPolynomial.pderiv i r) := by
  letI : Algebra.FormallyEtale (MvPolynomial σ ℂ) (Localization.AtPrime Q) :=
    Algebra.FormallyEtale.of_isLocalization Q.primeCompl
  simp [localizedMvPolynomialKaehlerBasis,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    Module.Basis.baseChange_repr_tmul, Algebra.smul_def]

/-- The same coordinate formula after extending the localized cotangent space to a field. -/
theorem localizedMvPolynomialKaehlerBasis_baseChange_repr_D_algebraMap
    {σ : Type} [Finite σ]
    (Q : Ideal (MvPolynomial σ ℂ)) [Q.IsPrime]
    (K : Type) [Field K]
    [Algebra ℂ K]
    [Algebra (MvPolynomial σ ℂ) K]
    [IsScalarTower ℂ (MvPolynomial σ ℂ) K]
    [Algebra (Localization.AtPrime Q) K]
    [IsScalarTower ℂ (Localization.AtPrime Q) K]
    [IsScalarTower (MvPolynomial σ ℂ) (Localization.AtPrime Q) K]
    (r : MvPolynomial σ ℂ) (i : σ) :
    ((localizedMvPolynomialKaehlerBasis Q).baseChange K).repr
        (1 ⊗ₜ[Localization.AtPrime Q]
          KaehlerDifferential.D ℂ (Localization.AtPrime Q)
            (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q) r)) i =
      algebraMap (Localization.AtPrime Q) K
        (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q)
          (MvPolynomial.pderiv i r)) := by
  rw [Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
  congr 1
  exact localizedMvPolynomialKaehlerBasis_repr_D_algebraMap Q r i

end

end GaloisForLFunctions.HTGeometry
