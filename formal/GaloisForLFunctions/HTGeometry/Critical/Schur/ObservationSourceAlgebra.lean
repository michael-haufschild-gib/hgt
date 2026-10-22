import GaloisForLFunctions.HTGeometry.Critical.Schur.SourceCotangent
import GaloisForLFunctions.HTGeometry.Critical.Schur.IntegralClosurePlace
import GaloisForLFunctions.HTGeometry.ValuationSubringResidueAlgebraic

/-!
# The observation-to-source Schur place as an algebra extension

This installs the structures the ramification criterion needs at the actual Schur place: the ground
field acts compatibly on both valuation rings, the observation ring acts on the source ring through
the inclusion of a pulled-back valuation subring (hence locally), the extension is essentially of
finite type, and its residue extension is algebraic — hence separable, the residue field having
characteristic zero.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open IsLocalRing

set_option synthInstance.maxHeartbeats 800000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n)

omit [IsAlgClosed K] in
/-- The Schur coordinate ring acts on the source Schur valuation ring by evaluation. -/
theorem coe_algebraMap_criticalSchurSourceValuation (p : criticalSchurSourceRing K m n) :
    ((algebraMap (criticalSchurSourceRing K m n)
        (criticalSchurSourceValuationSubring K hm hn) p :
          criticalSchurSourceValuationSubring K hm hn) : criticalSourceField K m n)
      = MvPolynomial.aeval (criticalSourceSchurCoordinates K hm hn) p := by
  show (criticalSchurSourceLocalizationEquiv K hm hn
      (algebraMap (criticalSchurSourceRing K m n)
        (Localization.AtPrime (criticalSchurPrimeDivisor K hm hn).1) p) :
          criticalSourceField K m n) = _
  rw [← criticalSourceSchurFieldEquiv_algebraMap_apply K hm hn p]
  show criticalSourceSchurFieldEquiv K hm hn
      (algebraMap (Localization.AtPrime (criticalSchurPrimeDivisor K hm hn).1)
        (FractionRing (criticalSchurSourceRing K m n))
        (algebraMap (criticalSchurSourceRing K m n)
          (Localization.AtPrime (criticalSchurPrimeDivisor K hm hn).1) p)) = _
  rw [← IsScalarTower.algebraMap_apply]

omit [IsAlgClosed K] in
/-- Ground-field constants embed compatibly into the source Schur valuation ring. -/
theorem coe_algebraMap_ground_criticalSchurSourceValuation (c : K) :
    ((algebraMap K (criticalSchurSourceValuationSubring K hm hn) c :
        criticalSchurSourceValuationSubring K hm hn) : criticalSourceField K m n)
      = algebraMap K (criticalSourceField K m n) c := by
  show ((algebraMap (criticalSchurSourceRing K m n)
      (criticalSchurSourceValuationSubring K hm hn)
      (algebraMap K (criticalSchurSourceRing K m n) c) : _) :
        criticalSourceField K m n) = _
  rw [coe_algebraMap_criticalSchurSourceValuation K hm hn]
  simp [MvPolynomial.algebraMap_eq]

/-- Ground field structure on the observation Schur valuation ring. -/
noncomputable instance criticalSchurObservationGroundAlgebra :
    Algebra K (criticalSchurObservationValuationSubring K hm hn) :=
  (criticalObservationSchurConstantBaseMap K hm hn).toAlgebra

/-- The observation Schur valuation ring acts on the source Schur valuation ring. -/
noncomputable instance criticalSchurObservationSourceAlgebra :
    Algebra (criticalSchurObservationValuationSubring K hm hn)
      (criticalSchurSourceValuationSubring K hm hn) :=
  (valuationSubringComapInclusion
    (algebraMap (criticalObservationField K m n) (criticalSourceField K m n))
    (criticalSchurSourceValuationSubring K hm hn)).toAlgebra

instance criticalSchurObservationSourceIsLocalHom :
    IsLocalHom (algebraMap (criticalSchurObservationValuationSubring K hm hn)
      (criticalSchurSourceValuationSubring K hm hn)) :=
  valuationSubringComapInclusion_isLocalHom
    (algebraMap (criticalObservationField K m n) (criticalSourceField K m n))
    (criticalSchurSourceValuationSubring K hm hn)

instance criticalSchurObservationSourceTower :
    IsScalarTower K (criticalSchurObservationValuationSubring K hm hn)
      (criticalSchurSourceValuationSubring K hm hn) := by
  refine IsScalarTower.of_algebraMap_eq fun c => ?_
  apply Subtype.ext
  rw [coe_algebraMap_ground_criticalSchurSourceValuation K hm hn c]
  show _ = algebraMap (criticalObservationField K m n) (criticalSourceField K m n)
    ((criticalObservationSchurConstantBaseMap K hm hn c : _) : criticalObservationField K m n)
  show algebraMap K (criticalSourceField K m n) c
    = algebraMap (criticalObservationField K m n) (criticalSourceField K m n)
      (algebraMap K (criticalObservationField K m n) c)
  rw [← IsScalarTower.algebraMap_apply]

instance criticalSchurSourceValuation_essFiniteType_ground :
    Algebra.EssFiniteType K (criticalSchurSourceValuationSubring K hm hn) := by
  haveI : Algebra.EssFiniteType (criticalSchurSourceRing K m n)
      (criticalSchurSourceValuationSubring K hm hn) :=
    Algebra.EssFiniteType.of_isLocalization _ (criticalSchurPrimeDivisor K hm hn).1.primeCompl
  exact Algebra.EssFiniteType.comp K (criticalSchurSourceRing K m n) _

instance criticalSchurSourceValuation_essFiniteType_observation :
    Algebra.EssFiniteType (criticalSchurObservationValuationSubring K hm hn)
      (criticalSchurSourceValuationSubring K hm hn) :=
  Algebra.EssFiniteType.of_comp K _ _

instance criticalSchurResidue_isAlgebraic :
    Algebra.IsAlgebraic (ResidueField (criticalSchurObservationValuationSubring K hm hn))
      (ResidueField (criticalSchurSourceValuationSubring K hm hn)) := by
  haveI : FiniteDimensional (criticalObservationField K m n) (criticalSourceField K m n) :=
    criticalSourceField_finiteDimensional_criticalObservationField K hm hn
  haveI : Algebra.IsAlgebraic (criticalObservationField K m n) (criticalSourceField K m n) :=
    Algebra.IsAlgebraic.of_finite _ _
  exact isAlgebraic_residueField_comap (criticalSchurSourceValuationSubring K hm hn)

theorem criticalSchurObservation_map_maximalIdeal_ne_bot :
    (maximalIdeal (criticalSchurObservationValuationSubring K hm hn)).map
      (algebraMap (criticalSchurObservationValuationSubring K hm hn)
        (criticalSchurSourceValuationSubring K hm hn)) ≠ ⊥ := by
  have hinj : Function.Injective
      (algebraMap (criticalSchurObservationValuationSubring K hm hn)
        (criticalSchurSourceValuationSubring K hm hn)) :=
    valuationSubringComapInclusion_injective
      (algebraMap (criticalObservationField K m n) (criticalSourceField K m n))
      (criticalSchurSourceValuationSubring K hm hn)
  rw [Ne, Ideal.map_eq_bot_iff_of_injective hinj]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible
    (criticalSchurObservationValuationSubring K hm hn)
  intro hbot
  have hmem : π ∈ maximalIdeal (criticalSchurObservationValuationSubring K hm hn) := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    exact hπ.not_isUnit
  rw [hbot, Ideal.mem_bot] at hmem
  exact hπ.ne_zero hmem

end

end GaloisForLFunctions.HTGeometry
