import GaloisForLFunctions.HilbertMetric.SymmetricFockShadow

/-!
# Exact inverse for a two-replica collective commutator

Let `p` and `q` be commuting involutions, representing the same physical
involution on two replica factors.  On the sector odd under simultaneous
conjugation by `p*q`, the collective commutator `ad p + ad q` squares to
exactly four.  Hence it has no kernel there.  The theorem is purely
algebraic and needs no spectral calculation.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Ring commutator. -/
def ringCommutator {A : Type*} [Ring A] (a x : A) : A := a * x - x * a

/-- On relative-odd two-replica parity, the collective commutator of two
commuting involutions squares to four. -/
theorem twoInvolution_collectiveCommutator_sq_of_relativeOdd
    {A : Type*} [Ring A]
    (p q x : A)
    (hp : p * p = 1) (hq : q * q = 1)
    (hpq : p * q = q * p)
    (hodd : (p * q) * x * (p * q) = -x) :
    ringCommutator p (ringCommutator p x + ringCommutator q x) +
        ringCommutator q (ringCommutator p x + ringCommutator q x) =
      4 * x := by
  have hp_pq : p * (p * q) = q := by
    rw [← mul_assoc, hp, one_mul]
  have hpq_p : (p * q) * p = q := by
    rw [mul_assoc, ← hpq, ← mul_assoc, hp, one_mul]
  have hpq_q : (p * q) * q = p := by
    rw [mul_assoc, hq, mul_one]
  have hpq_qp : (p * q) * (q * p) = 1 := by
    rw [← mul_assoc, mul_assoc p q q, hq, mul_one, hp]
  have hqpx : q * p * x = p * q * x := by rw [← hpq]
  have hxqp : x * q * p = x * p * q := by
    rw [mul_assoc, ← hpq, ← mul_assoc]
  have hsame : q * x * q = -(p * x * p) := by
    calc
      q * x * q = p * ((p * q) * x * (p * q)) * p := by
        symm
        calc
          p * ((p * q) * x * (p * q)) * p =
              (p * (p * q)) * x * ((p * q) * p) := by noncomm_ring
          _ = q * x * q := by rw [hp_pq, hpq_p]
      _ = p * (-x) * p := by rw [hodd]
      _ = -(p * x * p) := by noncomm_ring
  have hcross : q * x * p = -(p * x * q) := by
    calc
      q * x * p = p * ((p * q) * x * (p * q)) * q := by
        symm
        calc
          p * ((p * q) * x * (p * q)) * q =
              (p * (p * q)) * x * ((p * q) * q) := by noncomm_ring
          _ = q * x * p := by rw [hp_pq, hpq_q]
      _ = p * (-x) * q := by rw [hodd]
      _ = -(p * x * q) := by noncomm_ring
  have hgrade : p * q * x = -(x * p * q) := by
    calc
      p * q * x = ((p * q) * x * (p * q)) * (q * p) := by
        symm
        calc
          ((p * q) * x * (p * q)) * (q * p) =
              (p * q) * x * ((p * q) * (q * p)) := by noncomm_ring
          _ = p * q * x := by rw [hpq_qp, mul_one]
      _ = (-x) * (q * p) := by rw [hodd]
      _ = -(x * p * q) := by rw [← hpq]; noncomm_ring
  calc
    ringCommutator p (ringCommutator p x + ringCommutator q x) +
          ringCommutator q (ringCommutator p x + ringCommutator q x) =
        (p * p) * x + x * (p * p) +
          (q * q) * x + x * (q * q) +
          p * q * x + q * p * x + x * p * q + x * q * p -
          2 * (p * x * p + q * x * q) -
          2 * (p * x * q + q * x * p) := by
      unfold ringCommutator
      noncomm_ring
    _ = 4 * x - 2 * (p * x * p + q * x * q) +
          2 * (p * q * x + x * p * q) -
            2 * (p * x * q + q * x * p) := by
      rw [hp, hq, hqpx, hxqp]
      noncomm_ring
    _ = 4 * x := by rw [hsame, hcross, hgrade]; noncomm_ring

/-- If four is a unit, the relative-odd collective commutator is injective
pointwise. -/
theorem twoInvolution_collectiveCommutator_eq_zero_iff_of_relativeOdd
    {A : Type*} [Ring A]
    (p q x : A)
    (hp : p * p = 1) (hq : q * q = 1)
    (hpq : p * q = q * p)
    (hfour : IsUnit (4 : A))
    (hodd : (p * q) * x * (p * q) = -x) :
    ringCommutator p x + ringCommutator q x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have hsquare :=
      twoInvolution_collectiveCommutator_sq_of_relativeOdd
        p q x hp hq hpq hodd
    rw [hx] at hsquare
    have h4x : (4 : A) * x = 0 := by
      simpa [ringCommutator] using hsquare.symm
    apply hfour.mul_left_cancel
    simpa using h4x
  · rintro rfl
    simp [ringCommutator]

end GaloisForLFunctions.HTGeometry
