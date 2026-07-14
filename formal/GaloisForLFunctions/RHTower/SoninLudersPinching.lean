import GaloisForLFunctions.RHTower.CCMSoninResolventCommutator

/-!
# Lüders pinching removes cutoff-commutation hypotheses

For an idempotent cutoff `e`, the nonselective two-outcome measurement channel

`D_e(X) = eXe + (1-e)X(1-e)`

deletes both off-diagonal cutoff corners.  Consequently `D_e(X)` commutes with `e` for every
input `X`.  The exact identity

`X + (1-2e)X(1-2e) = 2 D_e(X)`

also identifies this Lüders channel with the finite `Z₂` parity twirl whenever division by two is
available.

The final theorem substitutes the pinched observable into the existing resolvent-dressed Sonin
commutator formula.  It removes that theorem's assumed commutation with the physical cutoff; the
only surviving anomaly channel is again the Fourier-edge commutator.
-/

namespace RHTower

noncomputable section

variable {R : Type*} [Ring R]

/-- The nonselective two-outcome Lüders pinching associated with an idempotent cutoff. -/
def ludersPinching (e X : R) : R :=
  e * X * e + (1 - e) * X * (1 - e)

/-- The parity involution associated with a two-sector cutoff. -/
def cutoffParity (e : R) : R :=
  1 - 2 * e

/-- The Lüders channel is exactly the normalized `Z₂` parity twirl, stated without division:
the parity-orbit sum is twice the pinching.  This polynomial identity does not itself require
idempotence. -/
theorem parityTwirlNumerator_eq_two_mul_ludersPinching (e X : R) :
    X + cutoffParity e * X * cutoffParity e = 2 * ludersPinching e X := by
  simp only [cutoffParity, ludersPinching]
  noncomm_ring

/-- An idempotent cutoff acts on the left of its pinching by selecting the cutoff block. -/
theorem mul_ludersPinching_eq_cutoffBlock
    {e : R} (he : IsIdempotentElem e) (X : R) :
    e * ludersPinching e X = e * X * e := by
  have hee : e * e = e := he
  have hec : e * (1 - e) = 0 := by
    rw [mul_sub, mul_one, hee, sub_self]
  simp only [ludersPinching, mul_add, ← mul_assoc, hee, hec, zero_mul, add_zero]

/-- An idempotent cutoff acts on the right of its pinching by selecting the same cutoff block. -/
theorem ludersPinching_mul_eq_cutoffBlock
    {e : R} (he : IsIdempotentElem e) (X : R) :
    ludersPinching e X * e = e * X * e := by
  have hee : e * e = e := he
  have hce : (1 - e) * e = 0 := by
    rw [sub_mul, one_mul, hee, sub_self]
  simp only [ludersPinching, add_mul, mul_assoc, hee, hce, mul_zero, add_zero]

/-- A nonselective Lüders pinching commutes with the measured cutoff, with no premise on the
unpinched observable. -/
theorem ccmCommutator_ludersPinching_eq_zero
    {e : R} (he : IsIdempotentElem e) (X : R) :
    ccmCommutator (ludersPinching e X) e = 0 := by
  rw [ccmCommutator, ludersPinching_mul_eq_cutoffBlock he,
    mul_ludersPinching_eq_cutoffBlock he, sub_self]

/-- The Lüders pinching deletes the lower cutoff-boundary corner of every observable. -/
theorem crossBoundary_ludersPinching_eq_zero
    {e : R} (he : IsIdempotentElem e) (X : R) :
    crossBoundary e (ludersPinching e X) = 0 := by
  apply crossBoundary_eq_zero_of_commute he
  exact sub_eq_zero.mp (ccmCommutator_ludersPinching_eq_zero he X)

/-- The Lüders pinching also deletes the upper cutoff-boundary corner. -/
theorem upperBoundary_ludersPinching_eq_zero
    {e : R} (he : IsIdempotentElem e) (X : R) :
    upperBoundary e (ludersPinching e X) = 0 := by
  apply upperBoundary_eq_zero_of_commute he
  exact sub_eq_zero.mp (ccmCommutator_ludersPinching_eq_zero he X)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- **Pinched Sonin commutator law.**  Replacing an arbitrary observable by its nonselective
Lüders pinching at the physical cutoff removes the commutation premise from the exact
resolvent-dressed Sonin formula. -/
theorem ccmCommutator_ludersPinching_soninIntersectionProjection
    (A B : Submodule ℂ H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection]
    [(A.orthogonal ⊓ B.orthogonal).HasOrthogonalProjection]
    (hT : ‖soninAlternatingBlock A B‖ < 1)
    (X : H →L[ℂ] H) :
    let X₀ := ludersPinching A.starProjection X
    let E := A.orthogonal.starProjection
    let V := soninProjectionResolvent A B hT
    ccmCommutator X₀ (soninIntersectionProjection A B) =
      -E * V *
        (ccmCommutator X₀ B.starProjection * A.starProjection * B.starProjection * V *
            B.starProjection +
          B.starProjection * A.starProjection * ccmCommutator X₀ B.starProjection * V *
            B.starProjection +
          ccmCommutator X₀ B.starProjection) * E := by
  dsimp
  exact ccmCommutator_soninIntersectionProjection A B hT _
    (ccmCommutator_ludersPinching_eq_zero
      A.isIdempotentElem_starProjection X)

end

end RHTower
