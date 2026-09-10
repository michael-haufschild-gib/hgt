import GaloisForLFunctions.HTGeometry.BorisovGabberVasiuEtale
import GaloisForLFunctions.HTGeometry.FormalEtaleJetCompatibility

/-!
# Truncated arcs of characteristic-power endomorphisms

The etale characteristic-power family of Borisov--Gabber--Vasiu supplies a
closed certificate for the corpus's formal-etale jet compatibility theorem.
Every order is covered, including coefficients where the polynomial degree drops.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Arcs of every order satisfy the cartesian lifting law for this actual polynomial family. -/
theorem bgvPowerMap_truncatedArc_pullback_bijective (p : ℕ) [CharP R p]
    (b : R) (n : ℕ) :
    Function.Bijective (etaleArcPullbackMap (bgvPowerMap p b).toRingHom
      (truncatedArcAugmentation (R := S) n).toRingHom) :=
  formallyEtale_truncatedArc_pullback_bijective (bgvPowerMap p b).toRingHom
    (bgvPowerMap_formallyEtale p b) n

/-- The full space of arcs based at a source point is preserved by the characteristic-power map. -/
def bgvPowerMap_truncatedArc_basedEquiv (p : ℕ) [CharP R p]
    (b : R) (point : Polynomial R →+* S) (n : ℕ) :
    BasedRingArc (truncatedArcAugmentation (R := S) n).toRingHom point ≃
      BasedRingArc (truncatedArcAugmentation (R := S) n).toRingHom
        (point.comp (bgvPowerMap p b).toRingHom) :=
  formallyEtale_truncatedArc_basedEquiv (bgvPowerMap p b).toRingHom
    (bgvPowerMap_formallyEtale p b) point n

/-- Coefficient-preserving based arcs have the same exact lifting property. -/
def bgvPowerMap_truncatedArc_basedAlgEquiv (p : ℕ) [CharP R p]
    (b : R) (point : Polynomial R →ₐ[R] R) (n : ℕ) :
    BasedAlgArc (truncatedArcAugmentation (R := R) n) point ≃
      BasedAlgArc (truncatedArcAugmentation (R := R) n) (point.comp (bgvPowerMap p b)) :=
  formallyEtale_truncatedArc_basedAlgEquiv (bgvPowerMap p b)
    (bgvPowerMap_formallyEtale p b) point n

end GaloisForLFunctions.HTGeometry
