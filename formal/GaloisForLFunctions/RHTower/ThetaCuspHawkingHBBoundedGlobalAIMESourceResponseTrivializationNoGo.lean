import GaloisForLFunctions.RHTower.ThetaCuspHawkingHBCompactGlobalAIMESourceResponseNoGo

/-!
# Arbitrary bounded global AIME response is a nonselective HB premise

The compact-response no-go leaves bounded noncompact operators as a formal survivor.  This file
classifies that survivor before assigning it physical meaning.  For a nonzero absorbed seed,
universal cancellation of the literal cubic AIME packet by a bounded operator `Delta` is exactly
the basis-diagonal condition

`(Delta e_q)(q) = -1`

on every Xi copy.  Equivalently, `Delta + I` has zero canonical diagonal.  Thus the entire solution
space is the affine space `-I + {zero-diagonal bounded operators}`.

In particular, the canonical bounded response `-I` cancels every AIME pole numerator for every
seed, without inspecting the Xi divisor.  It is necessarily noncompact.  Consequently existence
of an arbitrary bounded single-packet cancelling response is nonselective and cannot be the first
RH-bearing premise in the proposed chain

`bounded AIME cancellation` -> `full causal-cut extinction` ->
`source-FE clock covariance` -> `RH`.

The surviving physical burden is sharper: construct the radiative retarded-minus-advanced jump on
the corpus's two-leg Peierls carrier, with its complex-bilinear pairing, cyclic residual, skew
causal jump, and independent source/left-QNM legs.  A same-coordinate operator on one Hilbert
packet does not supply that incidence.

`[PROVED HERE] [LEAN-PROVED] [HB ROUTE KILL] [BOUNDED-CLASS TRIVIALIZATION]`
`[AFFINE CLASSIFICATION] [NOVELTY AUDITED 2026-08-31] [NOVELTY UNVERIFIED]`
-/

open Complex

namespace RHTower

noncomputable section

/-- Canonical bounded response which returns the negative of the literal AIME source packet. -/
def d4HBXiHilbertNegativeIdentity :
    D4HBXiHilbertPacket →L[ℂ] D4HBXiHilbertPacket :=
  -(ContinuousLinearMap.id ℂ D4HBXiHilbertPacket)

@[simp]
theorem d4HBXiHilbertNegativeIdentity_apply (x : D4HBXiHilbertPacket) :
    d4HBXiHilbertNegativeIdentity x = -x := by
  rfl

/-- Exact classification of all bounded global responses cancelling one nonzero AIME seed. -/
theorem d4HBBoundedAIMESourceResponseCancellation_iff_diagonal_eq_neg_one
    (Delta : D4HBXiHilbertPacket →L[ℂ] D4HBXiHilbertPacket)
    (amplitude : ℂ) (ha : amplitude ≠ 0) :
    (∀ q : XiZeroCopy,
      d4HBCompactAIMESourceResponseFullPoleNumerator Delta amplitude q = 0) ↔
      ∀ q : XiZeroCopy,
        Delta (d4HBXiHilbertBasisVector q) q = -1 := by
  constructor
  · intro h q
    exact d4HBCompactAIMESourceResponse_diagonal_eq_neg_one
      Delta amplitude ha h q
  · intro h q
    let N := d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q)
    unfold d4HBCompactAIMESourceResponseFullPoleNumerator
    rw [d4HBHilbertAIMESourcePacket, map_smul]
    change N + N * Delta (d4HBXiHilbertBasisVector q) q = 0
    rw [h q]
    ring

/-- A bounded operator has zero canonical Xi-basis diagonal. -/
def D4HBXiHilbertZeroDiagonal
    (Z : D4HBXiHilbertPacket →L[ℂ] D4HBXiHilbertPacket) : Prop :=
  ∀ q : XiZeroCopy, Z (d4HBXiHilbertBasisVector q) q = 0

/-- Affine classification: every bounded canceller is `-I` plus an arbitrary zero-diagonal
bounded operator, and every such operator cancels. -/
theorem d4HBBoundedAIMESourceResponseCancellation_iff_zeroDiagonal_add_id
    (Delta : D4HBXiHilbertPacket →L[ℂ] D4HBXiHilbertPacket)
    (amplitude : ℂ) (ha : amplitude ≠ 0) :
    (∀ q : XiZeroCopy,
      d4HBCompactAIMESourceResponseFullPoleNumerator Delta amplitude q = 0) ↔
      D4HBXiHilbertZeroDiagonal
        (Delta + ContinuousLinearMap.id ℂ D4HBXiHilbertPacket) := by
  rw [d4HBBoundedAIMESourceResponseCancellation_iff_diagonal_eq_neg_one
    Delta amplitude ha]
  constructor
  · intro h q
    change Delta (d4HBXiHilbertBasisVector q) q +
      d4HBXiHilbertBasisVector q q = 0
    rw [h q]
    simp [d4HBXiHilbertBasisVector]
  · intro h q
    have hq := h q
    change Delta (d4HBXiHilbertBasisVector q) q +
      d4HBXiHilbertBasisVector q q = 0 at hq
    have hdiag : Delta (d4HBXiHilbertBasisVector q) q = -1 := by
      change Delta (lp.single 2 q 1) q = -1
      simp [d4HBXiHilbertBasisVector] at hq
      linear_combination hq
    exact hdiag

/-- The canonical negative identity cancels the literal cubic AIME numerator on every Xi copy,
for every seed, without any arithmetic premise. -/
theorem d4HBXiHilbertNegativeIdentityAIMESourceResponse_universalCancellation
    (amplitude : ℂ) (q : XiZeroCopy) :
    d4HBCompactAIMESourceResponseFullPoleNumerator
        d4HBXiHilbertNegativeIdentity amplitude q = 0 := by
  unfold d4HBCompactAIMESourceResponseFullPoleNumerator
  rw [d4HBHilbertAIMESourcePacket, map_smul]
  simp [d4HBXiHilbertNegativeIdentity, d4HBXiHilbertBasisVector]

/-- The canonical bounded canceller lies outside the compact class, exactly as forced by the
previous essential-distance theorem. -/
theorem d4HBXiHilbertNegativeIdentity_not_compact :
    ¬ IsCompactOperator d4HBXiHilbertNegativeIdentity := by
  intro hcompact
  exact not_d4HBCompactAIMESourceResponse_universalCancellation
    d4HBXiHilbertNegativeIdentity 1 one_ne_zero
      (d4HBXiHilbertNegativeIdentityAIMESourceResponse_universalCancellation 1) hcompact

/-- Closed route class: arbitrary bounded single-packet AIME cancellation is constructively
automatic and its complete solution space is an affine zero-diagonal class.  Any RH-bearing
successor must add the missing two-leg physical Peierls incidence. -/
def D4HBBoundedGlobalAIMESourceResponseExistenceRouteKilled : Prop :=
  (∀ (Delta : D4HBXiHilbertPacket →L[ℂ] D4HBXiHilbertPacket)
      (amplitude : ℂ), amplitude ≠ 0 →
    ((∀ q : XiZeroCopy,
        d4HBCompactAIMESourceResponseFullPoleNumerator Delta amplitude q = 0) ↔
      D4HBXiHilbertZeroDiagonal
        (Delta + ContinuousLinearMap.id ℂ D4HBXiHilbertPacket))) ∧
  (∀ (amplitude : ℂ) (q : XiZeroCopy),
    d4HBCompactAIMESourceResponseFullPoleNumerator
      d4HBXiHilbertNegativeIdentity amplitude q = 0) ∧
  ¬ IsCompactOperator d4HBXiHilbertNegativeIdentity

/-- Premise-free certificate killing arbitrary bounded single-packet response existence as an HB
producer. -/
theorem d4HBBoundedGlobalAIMESourceResponseExistenceRouteKilled :
    D4HBBoundedGlobalAIMESourceResponseExistenceRouteKilled := by
  exact ⟨fun Delta amplitude ha =>
      d4HBBoundedAIMESourceResponseCancellation_iff_zeroDiagonal_add_id
        Delta amplitude ha,
    d4HBXiHilbertNegativeIdentityAIMESourceResponse_universalCancellation,
    d4HBXiHilbertNegativeIdentity_not_compact⟩

end

end RHTower
