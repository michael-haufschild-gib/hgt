import GaloisForLFunctions.HTGeometry.Critical.Schur.ValuationDVR
import GaloisForLFunctions.HTGeometry.MvPolynomialLocalizationCotangent

/-!
# Coordinate cotangent basis at the actual source Schur place

The source Schur valuation ring was built by transporting the height-one localization of the Schur
coordinate ring through the coordinate field equivalence.  Composing that transport with the
valuation-subring model of a discrete valuation ring makes the transport a ring isomorphism from
the localization itself, so the source Schur valuation ring *is* a localization of the Schur
coordinate polynomial ring.  Localizations are formally étale, so its Kähler differentials over the
ground field are free on the coordinate differentials.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open IsDiscreteValuationRing

set_option synthInstance.maxHeartbeats 400000

variable (K : Type*) [Field K] [CharZero K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n)

/-- The Schur local ring in the coordinate presentation is its valuation-subring model. -/
noncomputable def criticalSchurCoordinateLocalizationEquiv :
    Localization.AtPrime (criticalSchurPrimeDivisor K hm hn).1 ≃+*
      criticalSchurCoordinateValuationSubring K hm hn := by
  change Localization.AtPrime (criticalSchurPrimeDivisor K hm hn).1 ≃+*
    ((IsDiscreteValuationRing.maximalIdeal
      (Localization.AtPrime (criticalSchurPrimeDivisor K hm hn).1)).valuation
        (FractionRing (criticalSchurSourceRing K m n))).valuationSubring
  exact IsDiscreteValuationRing.equivValuationSubring

/-- The Schur local ring in the coordinate presentation is the actual source Schur valuation
ring. -/
noncomputable def criticalSchurSourceLocalizationEquiv :
    Localization.AtPrime (criticalSchurPrimeDivisor K hm hn).1 ≃+*
      criticalSchurSourceValuationSubring K hm hn :=
  (criticalSchurCoordinateLocalizationEquiv K hm hn).trans
    (criticalSchurSourceValuationRingEquiv K hm hn).symm

/-- The Schur coordinate ring acts on the actual source Schur valuation ring. -/
noncomputable instance criticalSchurSourceValuationAlgebra :
    Algebra (criticalSchurSourceRing K m n) (criticalSchurSourceValuationSubring K hm hn) :=
  ((criticalSchurSourceLocalizationEquiv K hm hn).toRingHom.comp
    (algebraMap (criticalSchurSourceRing K m n)
      (Localization.AtPrime (criticalSchurPrimeDivisor K hm hn).1))).toAlgebra

/-- **The actual source Schur valuation ring is the localization of the Schur coordinate ring at
the Schur prime.** -/
noncomputable instance criticalSchurSourceValuation_isLocalization :
    IsLocalization (criticalSchurPrimeDivisor K hm hn).1.primeCompl
      (criticalSchurSourceValuationSubring K hm hn) :=
  IsLocalization.isLocalization_of_algEquiv _
    ({ criticalSchurSourceLocalizationEquiv K hm hn with commutes' := fun _ => rfl } :
      Localization.AtPrime (criticalSchurPrimeDivisor K hm hn).1 ≃ₐ[criticalSchurSourceRing K m n]
        criticalSchurSourceValuationSubring K hm hn)

/-- Ground field structure on the actual source Schur valuation ring. -/
noncomputable instance criticalSchurSourceValuationGroundAlgebra :
    Algebra K (criticalSchurSourceValuationSubring K hm hn) :=
  ((algebraMap (criticalSchurSourceRing K m n)
      (criticalSchurSourceValuationSubring K hm hn)).comp
    (algebraMap K (criticalSchurSourceRing K m n))).toAlgebra

instance criticalSchurSourceValuationGroundTower :
    IsScalarTower K (criticalSchurSourceRing K m n)
      (criticalSchurSourceValuationSubring K hm hn) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The coordinate cotangent basis of the actual source Schur valuation ring. -/
noncomputable def criticalSchurSourceCotangentBasis :
    Module.Basis (Fin (m + n - 1 + 1)) (criticalSchurSourceValuationSubring K hm hn)
      Ω[criticalSchurSourceValuationSubring K hm hn⁄K] :=
  localizationCotangentBasis K (criticalSchurSourceValuationSubring K hm hn)
    (criticalSchurPrimeDivisor K hm hn).1.primeCompl

end

end GaloisForLFunctions.HTGeometry
