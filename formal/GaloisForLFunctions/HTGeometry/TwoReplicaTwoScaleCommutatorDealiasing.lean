import GaloisForLFunctions.HTGeometry.TwoReplicaFirstOrderCliffordInterpolation

/-!
# Two-scale commutator de-aliasing

For two commuting involutions, first-order conjugation data at a single scale
aliases the collective commutator with a relative-even component.  Comparing
the exact scales `1` and `2` cancels that component and recovers the full
collective commutator.  The identity is purely algebraic and holds in every
noncommutative ring satisfying the displayed relations.
-/

open scoped Matrix Kronecker

namespace GaloisForLFunctions.HTGeometry

theorem twoInvolutionTwoScaleDifferenceIdentity
    {R : Type*} [Ring R]
    (A B J X : R)
    (hA : A * A = 1) (hB : B * B = 1) (hAB : A * B = B * A)
    (hJ : J * J = -1)
    (hJA : J * A = A * J)
    (hJB : J * B = B * J) (hJX : J * X = X * J) :
    let H : R := A + B
    let R0 : R := A * B
    let T1p : R := 1 + J * H - R0
    let T1m : R := 1 - J * H - R0
    let T2p : R := 1 + 2 * J * H - 4 * R0
    let T2m : R := 1 - 2 * J * H - 4 * R0
    12 * ringCommutator H X =
      J * ((T2p * X * T2m - T2m * X * T2p) -
        8 * (T1p * X * T1m - T1m * X * T1p)) := by
  dsimp
  have hBA : B * A = A * B := hAB.symm
  have hHR : (A + B) * (A * B) = A + B := by
    calc
      (A + B) * (A * B) = A * (A * B) + B * (A * B) := by rw [add_mul]
      _ = B + A := by rw [← mul_assoc, hA, one_mul, ← mul_assoc, hBA,
        mul_assoc, hB, mul_one]
      _ = A + B := add_comm _ _
  have hRH : (A * B) * (A + B) = A + B := by
    calc
      (A * B) * (A + B) = (A * B) * A + (A * B) * B := by rw [mul_add]
      _ = B + A := by rw [mul_assoc, hBA, ← mul_assoc, hA, one_mul,
        mul_assoc, hB, mul_one]
      _ = A + B := add_comm _ _
  have hJH : J * (A + B) = (A + B) * J := by
    rw [mul_add, add_mul, hJA, hJB]
  have hJR : J * (A * B) = (A * B) * J := by
    calc
      J * (A * B) = (J * A) * B := by rw [mul_assoc]
      _ = (A * J) * B := by rw [hJA]
      _ = A * (J * B) := by rw [mul_assoc]
      _ = A * (B * J) := by rw [hJB]
      _ = (A * B) * J := by rw [mul_assoc]
  have hdelta1 :
      (1 + J * (A + B) - A * B) * X *
          (1 - J * (A + B) - A * B) -
        (1 - J * (A + B) - A * B) * X *
          (1 + J * (A + B) - A * B) =
      2 * ((J * (A + B)) * X * (1 - A * B) -
        (1 - A * B) * X * (J * (A + B))) := by
    noncomm_ring
  have hdelta2 :
      (1 + 2 * J * (A + B) - 4 * (A * B)) * X *
          (1 - 2 * J * (A + B) - 4 * (A * B)) -
        (1 - 2 * J * (A + B) - 4 * (A * B)) * X *
          (1 + 2 * J * (A + B) - 4 * (A * B)) =
      4 * ((J * (A + B)) * X * (1 - 4 * (A * B)) -
        (1 - 4 * (A * B)) * X * (J * (A + B))) := by
    noncomm_ring
  unfold ringCommutator
  rw [hdelta1, hdelta2]
  have hcollapse :
      4 * ((J * (A + B)) * X * (1 - 4 * (A * B)) -
          (1 - 4 * (A * B)) * X * (J * (A + B))) -
        8 * (2 * ((J * (A + B)) * X * (1 - A * B) -
          (1 - A * B) * X * (J * (A + B)))) =
      -12 * ((J * (A + B)) * X - X * (J * (A + B))) := by
    noncomm_ring
  rw [hcollapse]
  have hJHX : J * ((J * (A + B)) * X) = -((A + B) * X) := by
    calc
      J * ((J * (A + B)) * X) = (J * J) * (A + B) * X := by
        noncomm_ring
      _ = -((A + B) * X) := by rw [hJ]; noncomm_ring
  have hXJH : J * (X * (J * (A + B))) = -(X * (A + B)) := by
    calc
      J * (X * (J * (A + B))) = (J * J) * X * (A + B) := by
        noncomm_ring [hJX]
      _ = -(X * (A + B)) := by rw [hJ]; noncomm_ring
  have hJD :
      J * ((J * (A + B)) * X - X * (J * (A + B))) =
        -((A + B) * X - X * (A + B)) := by
    rw [mul_sub, hJHX, hXJH]
    noncomm_ring
  symm
  calc
    J * (-12 * ((J * (A + B)) * X - X * (J * (A + B)))) =
        -12 * (J * ((J * (A + B)) * X - X * (J * (A + B)))) := by
          noncomm_ring
    _ = 12 * ((A + B) * X - X * (A + B)) := by rw [hJD]; noncomm_ring

end GaloisForLFunctions.HTGeometry
