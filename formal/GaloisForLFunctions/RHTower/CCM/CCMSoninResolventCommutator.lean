/-
# Resolvent-dressed Sonin commutator

The exact Sonin projection is not the formal complement of the physical and
Fourier cutoffs.  It is a resolvent correction of that complement.  This file
proves the noncommutative algebra needed to transport a position commutator
through the correction.

If `X` commutes with the physical cutoff `A`, then the entire commutator with
the exact intersection projection factors through `[X,B]`, the Fourier-edge
commutator, dressed by the alternating-block resolvent.  Thus the Sonin
correction creates no independent anomaly channel: it only propagates the
existing boundary edge channel.
-/
import GaloisForLFunctions.RHTower.SoninProjectionCalkin

noncomputable section

namespace RHTower

open ContinuousLinearMap

variable {R : Type*} [Ring R]

/-- Ring-theoretic commutator, used uniformly for bounded operator algebras. -/
def ccmCommutator (X Y : R) : R :=
  X * Y - Y * X

/-- Resolvent commutator identity `[X,(1-T)⁻¹] = (1-T)⁻¹[X,T](1-T)⁻¹`. -/
theorem ccmCommutator_inv_one_sub
    (X T V : R)
    (hL : V * (1 - T) = 1) (hR : (1 - T) * V = 1) :
    ccmCommutator X V = V * ccmCommutator X T * V := by
  have hxv : X * V = V * (1 - T) * X * V := by
    rw [hL, one_mul]
  have hvx : V * X = V * X * (1 - T) * V := by
    calc
      V * X = V * X * 1 := by rw [mul_one]
      _ = V * X * ((1 - T) * V) := by rw [hR]
      _ = V * X * (1 - T) * V := by noncomm_ring
  rw [ccmCommutator, hxv, hvx, ccmCommutator]
  noncomm_ring

/-- Leibniz rule for the ring commutator. -/
theorem ccmCommutator_mul (X Y Z : R) :
    ccmCommutator X (Y * Z) =
      ccmCommutator X Y * Z + Y * ccmCommutator X Z := by
  simp [ccmCommutator]
  noncomm_ring

/-- Additivity over subtraction for the ring commutator. -/
theorem ccmCommutator_sub (X Y Z : R) :
    ccmCommutator X (Y - Z) = ccmCommutator X Y - ccmCommutator X Z := by
  simp [ccmCommutator]
  noncomm_ring

/-- The identity operator has zero commutator. -/
theorem ccmCommutator_one (X : R) :
    ccmCommutator X 1 = 0 := by
  simp [ccmCommutator]

/-- Passing to a complement reverses the commutator sign. -/
theorem ccmCommutator_one_sub (X Y : R) :
    ccmCommutator X (1 - Y) = -ccmCommutator X Y := by
  rw [ccmCommutator_sub, ccmCommutator_one, zero_sub]

/-- Exact algebraic dressing law for a two-projection resolvent formula.  When
`[X,A]=0`, every term factors through `[X,B]`. -/
theorem ccmCommutator_dressed_two_projection
    (X A B V : R)
    (hXA : ccmCommutator X A = 0)
    (hL : V * (1 - B * A * B) = 1)
    (hR : (1 - B * A * B) * V = 1) :
    let E := 1 - A
    let Q := E - E * V * B * E
    ccmCommutator X Q =
      -E * V *
        (ccmCommutator X B * A * B * V * B +
          B * A * ccmCommutator X B * V * B +
          ccmCommutator X B) * E := by
  dsimp
  have hXE : ccmCommutator X (1 - A) = 0 := by
    rw [ccmCommutator_one_sub, hXA, neg_zero]
  have hXV := ccmCommutator_inv_one_sub X (B * A * B) V hL hR
  have hXT : ccmCommutator X (B * A * B) =
      ccmCommutator X B * A * B + B * A * ccmCommutator X B := by
    rw [show B * A * B = B * (A * B) by noncomm_ring,
      ccmCommutator_mul, ccmCommutator_mul, hXA]
    noncomm_ring
  rw [ccmCommutator_sub, ccmCommutator_mul, ccmCommutator_mul,
    ccmCommutator_mul, hXE, zero_mul, zero_add, mul_zero, add_zero, hXV, hXT]
  noncomm_ring

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Exact Sonin specialization.  A bounded observable commuting with the first
forbidden projection sees the exact intersection projection only through the
second boundary commutator, conjugated by the prolate/Sonin resolvent. -/
theorem ccmCommutator_soninIntersectionProjection
    (A B : Submodule ℂ H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection]
    [(A.orthogonal ⊓ B.orthogonal).HasOrthogonalProjection]
    (hT : ‖soninAlternatingBlock A B‖ < 1)
    (X : H →L[ℂ] H)
    (hXA : ccmCommutator X A.starProjection = 0) :
    let E := A.orthogonal.starProjection
    let V := soninProjectionResolvent A B hT
    ccmCommutator X (soninIntersectionProjection A B) =
      -E * V *
        (ccmCommutator X B.starProjection * A.starProjection * B.starProjection * V *
            B.starProjection +
          B.starProjection * A.starProjection * ccmCommutator X B.starProjection * V *
            B.starProjection +
          ccmCommutator X B.starProjection) * E := by
  dsimp
  rw [soninIntersectionProjection_eq_resolventFormula A B hT]
  have hE : A.orthogonal.starProjection = 1 - A.starProjection := by
    simpa using A.starProjection_orthogonal'
  rw [hE]
  apply ccmCommutator_dressed_two_projection
  · exact hXA
  · let T : H →L[ℂ] H := soninAlternatingBlock A B
    let e : (H →L[ℂ] H)ˣ := Units.oneSub T (by simpa [T] using hT)
    change (↑(e⁻¹) : H →L[ℂ] H) * (↑e : H →L[ℂ] H) = 1
    rw [← Units.val_mul]
    simp
  · let T : H →L[ℂ] H := soninAlternatingBlock A B
    let e : (H →L[ℂ] H)ˣ := Units.oneSub T (by simpa [T] using hT)
    change (↑e : H →L[ℂ] H) * (↑(e⁻¹) : H →L[ℂ] H) = 1
    rw [← Units.val_mul]
    simp

end RHTower
