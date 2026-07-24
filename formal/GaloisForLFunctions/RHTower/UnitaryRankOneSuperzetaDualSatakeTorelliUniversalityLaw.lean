import GaloisForLFunctions.RHTower.FiniteSuperzetaSpectralTorelliUniversalityLaw
import GaloisForLFunctions.RHTower.UnitaryRankOneDualSatakeTorelliUniversalityLaw

/-!
# Unitary rank-one superzeta/dual-Satake Torelli universality

Finite superzeta Torelli makes the complete additive resolvent trace a faithful multiset
coordinate. On a unitary rank-one spectrum, abstract duality is conjugation. Combining the two
facts turns primal/dual trace equality into a sharp finite Satake-reality test and propagates that
test to every secular moment and local Euler factor.
-/

open scoped BigOperators
open Finset

namespace GaloisForLFunctions

noncomputable section

/-- Complete additive superzeta resolvent trace of a finite unitary rank-one spectrum. -/
def unitaryRankOneSuperzetaResolventTrace {n : ℕ}
    (f : Fin n → Circle) : PowerSeries ℂ :=
  ∑ i, PowerSeries.mk fun m => (f i : ℂ) ^ m

/-- Complete additive superzeta trace after abstract rank-one dualization. -/
def unitaryRankOneDualSuperzetaResolventTrace {n : ℕ}
    (f : Fin n → Circle) : PowerSeries ℂ :=
  ∑ i, PowerSeries.mk fun m =>
    ((rankOneDualMultiplier (f i) : Circle) : ℂ) ^ m

/-- Equality of primal and dual superzeta traces is exactly closure of the spectral multiset under
rank-one duality. -/
theorem unitaryRankOneSuperzetaResolventTrace_eq_dual_iff_spectrumClosed
    {n : ℕ} (f : Fin n → Circle) :
    unitaryRankOneSuperzetaResolventTrace f =
        unitaryRankOneDualSuperzetaResolventTrace f ↔
      unitaryRankOneDualSpectrum f = unitaryRankOneSpectrum f := by
  constructor
  · intro htrace
    have hmult :=
      (finiteSuperzetaResolventTrace_eq_iff
        (fun i => (f i : ℂ))
        (fun i => ((rankOneDualMultiplier (f i) : Circle) : ℂ))).1
        (by simpa [unitaryRankOneSuperzetaResolventTrace,
          unitaryRankOneDualSuperzetaResolventTrace] using htrace)
    simpa [unitaryRankOneSpectrum, unitaryRankOneDualSpectrum] using hmult.symm
  · intro hclosed
    apply
      (finiteSuperzetaResolventTrace_eq_iff
        (fun i => (f i : ℂ))
        (fun i => ((rankOneDualMultiplier (f i) : Circle) : ℂ))).2
    simpa [unitaryRankOneSpectrum, unitaryRankOneDualSpectrum] using hclosed.symm

/-- **Unitary rank-one superzeta/dual-Satake Torelli law.** Equality of the complete primal and
dual additive resolvent traces is detected by reality of only the first cardinality-many secular
moments. It then forces reality of every moment and dual invariance of every local Euler factor. -/
theorem unitaryRankOne_superzetaDualSatakeTorelliUniversality
    {n : ℕ} (f : Fin n → Circle) :
    (unitaryRankOneSuperzetaResolventTrace f =
          unitaryRankOneDualSuperzetaResolventTrace f ↔
        ∀ k ≤ n,
          (starRingEnd ℂ) ((univ.val.map (fun i => (f i : ℂ) ^ k)).sum) =
            (univ.val.map (fun i => (f i : ℂ) ^ k)).sum) ∧
      (unitaryRankOneSuperzetaResolventTrace f =
          unitaryRankOneDualSuperzetaResolventTrace f →
        (∀ m : ℕ,
          (starRingEnd ℂ) ((univ.val.map (fun i => (f i : ℂ) ^ m)).sum) =
            (univ.val.map (fun i => (f i : ℂ) ^ m)).sum) ∧
        ∀ x : ℂ,
          ((unitaryRankOneSpectrum f).map (fun a => 1 - a * x)).prod =
            ((unitaryRankOneSpectrum f).map (fun a => 1 - a⁻¹ * x)).prod) := by
  have htrace :=
    unitaryRankOneSuperzetaResolventTrace_eq_dual_iff_spectrumClosed f
  constructor
  · exact htrace.trans (unitaryRankOneDualSpectrum_closed_iff_firstMoments_real f)
  · intro h
    exact unitaryRankOneDualSpectrum_allMoments_real_and_localFactor_eq f
      (htrace.mp h)

end

end GaloisForLFunctions
