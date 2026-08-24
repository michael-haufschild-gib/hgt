import GaloisForLFunctions.HTGeometry.HasseFamily
import GaloisForLFunctions.HTGeometry.PrimeRadialFusionFieldCorrespondence
import GaloisForLFunctions.HTGeometry.ConstitutiveAdaptiveProcompletion
import GaloisForLFunctions.HTGeometry.ActualityWallFlatness
import GaloisForLFunctions.HTGeometry.GammaCommonInverseCollar
import GaloisForLFunctions.HTGeometry.StanleyReisnerFacetCoordinates
import GaloisForLFunctions.HTGeometry.FacetTranslationCoordinates
import GaloisForLFunctions.HTGeometry.StanleyReisnerFacetLaurentHasse
import GaloisForLFunctions.HTGeometry.BorelWeil.FlagCechHasse
import GaloisForLFunctions.HTGeometry.FiniteEvaluationHasse
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.CloneReencoding

/-!
# Further profile-valued Hasse applications

Faithful profiles from arithmetic, constitutive, wall, jet, Stanley--Reisner, Čech, evaluation,
and valuation-shell constructions are exposed through the common `HasseFamily` interface.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v

/-- Positive formal-series coefficients detect a complete prime-radial profile. -/
def primeRadialCoefficientHasseFamily : HasseFamily PrimeRadialProfile ℕ where
  Local := fun _ => ℂ
  profile := primeRadialCoefficientProfile
  profile_injective := primeRadialCoefficientProfile_injective

/-- Membership at every natural coordinate detects a finite constitutive law. -/
def finiteLawHasseFamily : HasseFamily (Finset ℕ) ℕ where
  Local := fun _ => Bool
  profile := finiteLawProfile
  profile_injective := finiteLawProfile_injective

/-- Boolean wall coordinates detect classes modulo wall indistinguishability. -/
def actualityWallQuotientHasseFamily
    {X : Type u} {W : Type v} (side : W → X → Bool) (base : X) :
    HasseFamily (Quotient (wallIndistinguishableSetoid side)) W where
  Local := fun _ => Bool
  profile := actualityWallProfileQuotient side base
  profile_injective := actualityWallProfileQuotient_injective side base

/-- Taylor-normalized critical jets detect the Möbius parameter. -/
def mobiusCriticalJetHasseFamily : HasseFamily ℂ ℕ where
  Local := fun _ => ℂ
  profile := mobiusCriticalJetProfile
  profile_injective := mobiusCriticalJetProfile_injective

/-- Ordinary facet-polynomial coordinates detect a Stanley--Reisner quotient class. -/
def stanleyReisnerFacetPolynomialHasseFamily
    {R α : Type*} [CommRing R] [DecidableEq α]
    (facets : Finset (Finset α)) :
    HasseFamily (MvPolynomial α R ⧸ stanleyReisnerIdeal R facets) facets where
  Local := fun F => MvPolynomial F.1 R
  profile := stanleyReisnerFacetPolynomialCoordinates facets
  profile_injective := stanleyReisnerFacetPolynomialCoordinates_injective facets

/-- Translation coordinates on all facets detect a Stanley--Reisner quotient class. -/
def stanleyReisnerFacetTranslationHasseFamily
    {R α : Type*} [CommRing R] [DecidableEq α]
    (facets : Finset (Finset α)) :
    HasseFamily (MvPolynomial α R ⧸ stanleyReisnerIdeal R facets) facets where
  Local := fun _ => MvPolynomial α R
  profile := stanleyReisnerFacetTranslationCoordinates facets
  profile_injective := stanleyReisnerFacetTranslationCoordinates_injective facets

/-- Denominator-shifted Laurent rows on all facets detect a Stanley--Reisner quotient class. -/
def stanleyReisnerFacetLaurentHasseFamily
    {R α : Type*} [CommRing R] [Fintype α] [DecidableEq α]
    (d : translationSubmonoid R α) (facets : Finset (Finset α)) :
    HasseFamily (MvPolynomial α R ⧸ stanleyReisnerIdeal R facets) facets where
  Local := fun _ => (α → ℤ) →₀ R
  profile := stanleyReisnerFacetLaurentHasseMap d facets
  profile_injective := stanleyReisnerFacetLaurentHasseMap_injective d facets

/-- Restrictions to every Bruhat-chart intersection detect a dominant global section. -/
def BorelWeil.bruhatChartHasseFamily
    {N : ℕ} {k : Type u} [Field k] [Infinite k]
    (lam : BorelWeil.BorelWeilDominantWeight N) :
    HasseFamily (BorelWeil.polySections (k := k) lam.1)
      (Finset (Equiv.Perm (Fin N))) where
  Local := fun _ => BorelWeil.FlagLoc N k
  profile := fun p => BorelWeil.globalCochain (fun i => (lam.1 i : ℤ)) p.1
  profile_injective := by
    intro p q h
    apply Subtype.ext
    exact BorelWeil.globalCochain_injective h

/-- A proved finite dual-evaluation packet is a Hasse family on coefficient vectors. -/
def FiniteEvaluationHasseData.hasseFamily
    {J : Type u} {α : Type v} [Fintype J] [DecidableEq J]
    {f : J → α → ℂ} (D : FiniteEvaluationHasseData f) :
    HasseFamily (J → ℂ) J where
  Local := fun _ => ℂ
  profile := D.localPacket
  profile_injective := D.localPacket_injective

/-- Valuation vectors on the shell with fixed top bound `M` and an attained zero coordinate. -/
abbrev CrossingValuationShell (ι : Type u) (M : ℕ) :=
  {x : ι → ℕ // (∀ p, x p ≤ M) ∧ ∃ p, x p = 0}

/-- Crossing times at every coordinate detect a bounded valuation-shell point. -/
def crossingValuationShellHasseFamily (ι : Type u) (M : ℕ) :
    HasseFamily (CrossingValuationShell ι M) ι where
  Local := fun _ => ℕ
  profile := fun x => HTGeometry.ConstraintRelativity.crossingProfile M x.1
  profile_injective := by
    intro x y h
    apply Subtype.ext
    exact HTGeometry.ConstraintRelativity.crossingProfile_injective
      x.2.1 y.2.1 x.2.2 y.2.2 h

end
end GaloisForLFunctions.HTGeometry
