import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# Cotangent coordinates of a localized polynomial ring over an arbitrary base

The Kähler differentials of a multivariable polynomial ring are free on the coordinate
differentials.  A localization is formally étale, so base change transports that basis to the local
rings, and the transported coordinates of `D f` are the partial derivatives of `f`.

This is the arbitrary-base version of `LocalizedMvPolynomialCotangent`, whose statements are over
the complex numbers.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped TensorProduct

noncomputable section

/-- The coordinate basis of the Kähler differentials of a localized polynomial ring. -/
noncomputable def mvPolynomialLocalizationCotangentBasis
    (k : Type*) [CommRing k] {σ : Type*} [Finite σ] (Q : Ideal (MvPolynomial σ k)) [Q.IsPrime] :
    Module.Basis σ (Localization.AtPrime Q) Ω[Localization.AtPrime Q⁄k] := by
  letI : Algebra.FormallyEtale (MvPolynomial σ k) (Localization.AtPrime Q) :=
    Algebra.FormallyEtale.of_isLocalization Q.primeCompl
  exact ((KaehlerDifferential.mvPolynomialBasis k σ).baseChange
      (Localization.AtPrime Q)).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
      k (MvPolynomial σ k) (Localization.AtPrime Q))

/-- In the localized cotangent basis, `D f` has the localized partial derivatives of `f` as its
coordinates. -/
theorem mvPolynomialLocalizationCotangentBasis_repr_D_algebraMap
    (k : Type*) [CommRing k] {σ : Type*} [Finite σ] (Q : Ideal (MvPolynomial σ k)) [Q.IsPrime]
    (r : MvPolynomial σ k) (i : σ) :
    (mvPolynomialLocalizationCotangentBasis k Q).repr
        (KaehlerDifferential.D k (Localization.AtPrime Q)
          (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q) r)) i =
      algebraMap (MvPolynomial σ k) (Localization.AtPrime Q) (MvPolynomial.pderiv i r) := by
  letI : Algebra.FormallyEtale (MvPolynomial σ k) (Localization.AtPrime Q) :=
    Algebra.FormallyEtale.of_isLocalization Q.primeCompl
  simp [mvPolynomialLocalizationCotangentBasis,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    Module.Basis.baseChange_repr_tmul, Algebra.smul_def]

/-- The coordinate basis of the Kähler differentials of any localization of a polynomial ring. -/
noncomputable def localizationCotangentBasis
    (k : Type*) [CommRing k] {σ : Type*} [Finite σ]
    (T : Type*) [CommRing T] [Algebra (MvPolynomial σ k) T] [Algebra k T]
    [IsScalarTower k (MvPolynomial σ k) T]
    (S : Submonoid (MvPolynomial σ k)) [IsLocalization S T] :
    Module.Basis σ T Ω[T⁄k] := by
  letI : Algebra.FormallyEtale (MvPolynomial σ k) T :=
    Algebra.FormallyEtale.of_isLocalization S
  exact ((KaehlerDifferential.mvPolynomialBasis k σ).baseChange T).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k (MvPolynomial σ k) T)

/-- In that basis, `D f` has the localized partial derivatives of `f` as its coordinates. -/
theorem localizationCotangentBasis_repr_D_algebraMap
    (k : Type*) [CommRing k] {σ : Type*} [Finite σ]
    (T : Type*) [CommRing T] [Algebra (MvPolynomial σ k) T] [Algebra k T]
    [IsScalarTower k (MvPolynomial σ k) T]
    (S : Submonoid (MvPolynomial σ k)) [IsLocalization S T]
    (r : MvPolynomial σ k) (i : σ) :
    (localizationCotangentBasis k T S).repr
        (KaehlerDifferential.D k T (algebraMap (MvPolynomial σ k) T r)) i =
      algebraMap (MvPolynomial σ k) T (MvPolynomial.pderiv i r) := by
  letI : Algebra.FormallyEtale (MvPolynomial σ k) T :=
    Algebra.FormallyEtale.of_isLocalization S
  simp [localizationCotangentBasis,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    Module.Basis.baseChange_repr_tmul, Algebra.smul_def]

end

end GaloisForLFunctions.HTGeometry
