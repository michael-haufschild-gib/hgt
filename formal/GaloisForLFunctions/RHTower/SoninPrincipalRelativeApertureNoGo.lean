import GaloisForLFunctions.RHTower.SoninApertureRestrictionDefect
import GaloisForLFunctions.RHTower.SoninApertureAreaRigidity
import GaloisForLFunctions.RHTower.SoninPrincipalRelativeTraceSplitting
import Mathlib.Data.Nat.Prime.Infinite

/-!
# Principal-relative aperture closure no-go

The finite-prime Sonin signed finite part splits an operator into a principal shell and an exact
Schatten-1 relative correction.  This module proves that class is not closed under any strict
aperture enlargement.  The diagonal restriction defect is noncompact in a crossing chamber, so it
cannot be a relative correction.  Euclid's theorem supplies a genuine prime scale crossing every
strict positive aperture pair.  Hence every strict enlargement creates a new noncompact principal
channel.
-/

noncomputable section

namespace RHTower

/-- The strict-crossing aperture defect cannot lie in the exact principal-relative ideal. -/
theorem evenCentralSoninQuadraticCorner_restrictionDefect_not_mem_principalRelativeIdeal
    {a b r : ℝ} (ha : 0 < a) (hab : a < b) (hr : 1 < r)
    (hbr : b < r * a) :
    ¬ IsSoninPrincipalRelativeIdeal
      (evenCentralSoninQuadraticCorner b r r hr hr -
        evenCentralSoninProjection b *
          evenCentralSoninQuadraticCorner a r r hr hr *
            evenCentralSoninProjection b) := by
  intro hrelative
  exact evenCentralSoninQuadraticCorner_restrictionDefect_not_isCompactOperator
    ha hab hr hbr hrelative.isCompactOperator

/-- No trace-class relative correction can make the diagonal prime corner compatible across a
strict crossing aperture step. -/
theorem no_principalRelativeCorrection_for_aperture_restriction
    {a b r : ℝ} (ha : 0 < a) (hab : a < b) (hr : 1 < r)
    (hbr : b < r * a) :
    ¬ ∃ K : evenSubspace →L[ℂ] evenSubspace,
      IsSoninPrincipalRelativeIdeal K ∧
      evenCentralSoninQuadraticCorner b r r hr hr =
        evenCentralSoninProjection b *
          evenCentralSoninQuadraticCorner a r r hr hr *
            evenCentralSoninProjection b + K := by
  rintro ⟨K, hK, hcompat⟩
  apply evenCentralSoninQuadraticCorner_restrictionDefect_not_mem_principalRelativeIdeal
    ha hab hr hbr
  apply hK.of_eq
  rw [hcompat]
  abel

/-- **Prime-source aperture no-go.**  Every strict positive aperture enlargement is crossed by a
genuine prime scale whose diagonal restriction defect lies outside the principal-relative ideal. -/
theorem exists_prime_restrictionDefect_not_mem_principalRelativeIdeal
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ p : Nat.Primes,
      ¬ IsSoninPrincipalRelativeIdeal
        (evenCentralSoninQuadraticCorner b (p : ℝ) (p : ℝ)
            (by exact_mod_cast p.prop.one_lt) (by exact_mod_cast p.prop.one_lt) -
          evenCentralSoninProjection b *
            evenCentralSoninQuadraticCorner a (p : ℝ) (p : ℝ)
              (by exact_mod_cast p.prop.one_lt) (by exact_mod_cast p.prop.one_lt) *
                evenCentralSoninProjection b) := by
  obtain ⟨n : ℕ, hn : b / a < n⟩ := exists_nat_gt (b / a)
  obtain ⟨p : ℕ, hnp : n ≤ p, hp : p.Prime⟩ := Nat.exists_infinite_primes n
  let pp : Nat.Primes := ⟨p, hp⟩
  have hpr : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hratio : b / a < (p : ℝ) := hn.trans_le (by exact_mod_cast hnp)
  have hbp : b < (p : ℝ) * a := (div_lt_iff₀ ha).mp hratio
  refine ⟨pp, ?_⟩
  simpa only [pp] using
    evenCentralSoninQuadraticCorner_restrictionDefect_not_mem_principalRelativeIdeal
      ha hab hpr hbp

end RHTower
