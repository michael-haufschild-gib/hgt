import GaloisForLFunctions.HTGeometry.ValuationSubringInertiaDictionary
import GaloisForLFunctions.HTGeometry.DedekindResidueFieldAtPlace

/-!
# Dedekind places as valuation rings

A normalized adic valuation has a proper valuation ring, and contracting
its maximal ideal recovers the original prime. Thus distinct height-one
primes give distinct valuation rings in the fraction field.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open IsDedekindDomain
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ValuationInertia
variable {B L : Type*} [CommRing B] [IsDedekindDomain B] [Field L]
    [Algebra B L] [IsFractionRing B L]

/-- A normalized adic valuation has a proper valuation ring. -/
theorem heightOne_valuationSubring_ne_top (w : HeightOneSpectrum B) :
    (w.valuation L).valuationSubring ≠ ⊤ := by
  intro htop
  obtain ⟨x, hx⟩ := w.valuation_surjective L (WithZero.exp (1 : ℤ))
  have hle : w.valuation L x ≤ 1 := by
    change x ∈ (w.valuation L).valuationSubring
    rw [htop]
    trivial
  rw [hx, ← WithZero.exp_zero, WithZero.exp_le_exp] at hle
  omega

/-- The center of a normalized adic valuation is its original Dedekind prime. -/
theorem heightOne_centerPrime (w : HeightOneSpectrum B) :
    centerPrime (w.valuation L).valuationSubring (algebraMap_mem_valuationSubringAtPlace L w) = w.asIdeal := by
  ext a
  rw [mem_centerPrime_iff, Valuation.mem_maximalIdeal_iff]
  change w.valuation L (algebraMap B L a) < 1 ↔ a ∈ w.asIdeal
  rw [HeightOneSpectrum.valuation_lt_one_iff_mem]

/-- Distinct Dedekind places have distinct valuation rings in their common fraction field. -/
theorem heightOne_valuationSubring_injective :
    Function.Injective (fun w : HeightOneSpectrum B => (w.valuation L).valuationSubring) := by
  intro v w hvw
  change (v.valuation L).valuationSubring = (w.valuation L).valuationSubring at hvw
  let V : {W : ValuationSubring L // ∀ a : B, algebraMap B L a ∈ W} :=
    ⟨(v.valuation L).valuationSubring, algebraMap_mem_valuationSubringAtPlace L v⟩
  let W : {W : ValuationSubring L // ∀ a : B, algebraMap B L a ∈ W} :=
    ⟨(w.valuation L).valuationSubring, algebraMap_mem_valuationSubringAtPlace L w⟩
  have hVW : V = W := Subtype.ext hvw
  have h := congrArg (fun U : {W : ValuationSubring L // ∀ a : B, algebraMap B L a ∈ W} =>
    centerPrime U.val U.property) hVW
  change centerPrime (v.valuation L).valuationSubring (algebraMap_mem_valuationSubringAtPlace L v) =
    centerPrime (w.valuation L).valuationSubring (algebraMap_mem_valuationSubringAtPlace L w) at h
  rw [heightOne_centerPrime, heightOne_centerPrime] at h
  exact HeightOneSpectrum.ext h

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
