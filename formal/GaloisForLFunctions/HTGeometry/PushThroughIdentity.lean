import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.NoncommRing

/-!
# The push-through identity

If `1 - S T` and `1 - T S` are both invertible, then

`T (1 - S T)⁻¹ S = (T S) (1 - T S)⁻¹`.

The mechanism is the intertwining `T (1 - S T) = (1 - T S) T`, which conjugates one inverse into
the other; the remaining step is that `1 - T S` commutes with `T S`, so the product may be
collected on either side.  Nothing beyond ring identities and invertibility is used, so the
statement holds in any ring.
-/

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [Ring R]

/-- **The intertwining behind the push-through identity.** -/
theorem mul_one_sub_mul (T S : R) : T * (1 - S * T) = (1 - T * S) * T := by
  noncomm_ring

/-- **The push-through identity.** -/
theorem pushThrough {T S : R} {u v : Rˣ}
    (hu : (u : R) = 1 - S * T) (hv : (v : R) = 1 - T * S) :
    T * (↑u⁻¹ : R) * S = (T * S) * (↑v⁻¹ : R) := by
  have hinter : T * (u : R) = (v : R) * T := by
    rw [hu, hv]
    exact mul_one_sub_mul T S
  have hswap : (↑v⁻¹ : R) * T = T * (↑u⁻¹ : R) := by
    have key : (v : R) * (T * (↑u⁻¹ : R)) = T := by
      rw [← mul_assoc, ← hinter, mul_assoc, Units.mul_inv, mul_one]
    calc (↑v⁻¹ : R) * T = (↑v⁻¹ : R) * ((v : R) * (T * (↑u⁻¹ : R))) := by rw [key]
      _ = T * (↑u⁻¹ : R) := by rw [← mul_assoc, Units.inv_mul, one_mul]
  have hvc : (v : R) * (T * S) = (T * S) * (v : R) := by
    rw [hv]
    noncomm_ring
  have hcomm : (↑v⁻¹ : R) * (T * S) = (T * S) * (↑v⁻¹ : R) := by
    have key : (v : R) * ((T * S) * (↑v⁻¹ : R)) = T * S := by
      rw [← mul_assoc, hvc, mul_assoc, Units.mul_inv, mul_one]
    calc (↑v⁻¹ : R) * (T * S) = (↑v⁻¹ : R) * ((v : R) * ((T * S) * (↑v⁻¹ : R))) := by rw [key]
      _ = (T * S) * (↑v⁻¹ : R) := by rw [← mul_assoc, Units.inv_mul, one_mul]
  calc T * (↑u⁻¹ : R) * S = ((↑v⁻¹ : R) * T) * S := by rw [hswap]
    _ = (↑v⁻¹ : R) * (T * S) := by rw [mul_assoc]
    _ = (T * S) * (↑v⁻¹ : R) := hcomm

end GaloisForLFunctions.HTGeometry
