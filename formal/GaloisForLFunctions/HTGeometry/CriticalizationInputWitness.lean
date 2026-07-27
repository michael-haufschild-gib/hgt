import GaloisForLFunctions.HTGeometry.NormalCrossingCriticalDerivedPhase

/-!
# The criticalization input is canonical

Every field of `NormalCrossingFamilyCriticalizationInput` is pinned by one of its own equations: the
Barnes annihilator is the span of the normal-crossing polynomial, the sine, elliptic-gamma and
cotangent-Fitting ideals are all the Veronese ideal, and the two ranks are the quotient rank.  So the
bundle carries no freedom beyond the choice of that rank, and taking any rank function produces an
input.  The criticalization theorem is therefore a statement about existing objects.
-/

open GaloisForLFunctions.VeroneseIdeal

namespace GaloisForLFunctions.HTGeometry

/-- **The canonical criticalization input** attached to a rank function. -/
noncomputable def normalCrossingFamilyCriticalizationInput_canonical
    (F : Type*) [Field F] (r : ℕ) (Packet : Type*) (rank : Packet → ℕ) :
    NormalCrossingFamilyCriticalizationInput F r Packet where
  barnesAnnihilator := Ideal.span {normalCrossingPolynomial (F := F) r}
  sineAnnihilator := veroneseIdeal F (Fin (r + 1)) r
  ellipticGammaAnnihilator := veroneseIdeal F (Fin (r + 1)) r
  cotangentFittingPullback := veroneseIdeal F (Fin (r + 1)) r
  sineRank := rank
  ellipticGammaRank := rank
  quotientRank := rank
  barnes_exact := rfl
  sine_exact := rfl
  ellipticGamma_exact := rfl
  cotangentFitting_exact := rfl
  sine_rank_exact := rfl
  ellipticGamma_rank_exact := rfl

/-- The criticalization law holds on the canonical input: the Veronese ideal is the intrinsic
critical ideal of the normal-crossing source equation. -/
theorem normalCrossing_crossFamily_criticalization_canonical
    (F : Type*) [Field F] (r : ℕ) (Packet : Type*) (rank : Packet → ℕ) :
    veroneseIdeal F (Fin (r + 1)) r =
      derivationalCriticalIdeal (R := F) (normalCrossingPolynomial (F := F) r) :=
  (normalCrossing_crossFamily_criticalization
    (normalCrossingFamilyCriticalizationInput_canonical F r Packet rank)).2.1

end GaloisForLFunctions.HTGeometry
