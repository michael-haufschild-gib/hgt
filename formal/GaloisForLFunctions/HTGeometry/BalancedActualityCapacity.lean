import GaloisForLFunctions.HTGeometry.ColorEventLocalResponseIndependence

/-!
# Balanced actuality capacity

Dimension formulae for Hermitian record, skew comparison, and transverse possibility are encoded
without division by doubling every real capacity.  Equality of the first two capacities forces
scalar dimension two.  Equality with transverse capacity then forces source size twice transverse
multiplicity.  The primitive balanced carrier is therefore the arithmetic profile `3 × 2` over a
two-real-dimensional scalar algebra.

These are unconditional arithmetic theorems.  They do not assert that physical events have equal
capacity, identify the selected scalar algebra with complex amplitudes, or assign physical forces
to the resulting carrier.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Twice the real dimension of the Hermitian part of `n × n` matrices over a scalar algebra of
real dimension `d`. -/
def doubledHermitianCapacity (d n : ℕ) : ℕ :=
  2 * n + d * n * (n - 1)

/-- Twice the real dimension of the skew-Hermitian part of `n × n` matrices over a scalar algebra
of real dimension `d` with a one-dimensional conjugation-fixed subspace. -/
def doubledSkewCapacity (d n : ℕ) : ℕ :=
  2 * n * (d - 1) + d * n * (n - 1)

/-- Twice the real dimension of `r × n` transverse matrices over a scalar algebra of real
dimension `d`. -/
def doubledTransverseCapacity (d n r : ℕ) : ℕ :=
  2 * d * n * r

/-- Equal Hermitian and skew capacities at nonzero source size force scalar dimension two. -/
theorem equal_hermitian_skew_capacity_forces_scalarDimension_two
    (d n : ℕ) (hn : 0 < n)
    (h :
      doubledHermitianCapacity d n =
        doubledSkewCapacity d n) :
    d = 2 := by
  unfold doubledHermitianCapacity doubledSkewCapacity at h
  have hbase : 2 * n = 2 * n * (d - 1) :=
    Nat.add_right_cancel h
  have hfactor : 1 = d - 1 := by
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2 * n)
    simpa [Nat.mul_assoc] using hbase
  omega

/-- At scalar dimension two, equal Hermitian and transverse capacities force source size twice
transverse multiplicity. -/
theorem equal_hermitian_transverse_capacity_forces_source_twice_transverse
    (n r : ℕ) (hn : 0 < n)
    (h :
      doubledHermitianCapacity 2 n =
        doubledTransverseCapacity 2 n r) :
    n = 2 * r := by
  have hnormalized : (2 * n) * n = (2 * n) * (2 * r) := by
    calc
      (2 * n) * n = doubledHermitianCapacity 2 n := by
        unfold doubledHermitianCapacity
        calc
          2 * n * n = 2 * n * (1 + (n - 1)) := by
            exact congrArg (fun q : ℕ => 2 * n * q)
              (show n = 1 + (n - 1) by omega)
          _ = 2 * n + 2 * n * (n - 1) := by ring
      _ = doubledTransverseCapacity 2 n r := h
      _ = (2 * n) * (2 * r) := by
        unfold doubledTransverseCapacity
        ring
  exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2 * n) hnormalized

/-- Three-way capacity balance classifies the scalar dimension and rectangular excess. -/
theorem balanced_actuality_capacity_classification
    (d n r : ℕ) (hn : 0 < n)
    (hHK :
      doubledHermitianCapacity d n =
        doubledSkewCapacity d n)
    (hHT :
      doubledHermitianCapacity d n =
        doubledTransverseCapacity d n r) :
    d = 2 ∧ n = 2 * r := by
  have hd :=
    equal_hermitian_skew_capacity_forces_scalarDimension_two d n hn hHK
  subst d
  exact ⟨rfl,
    equal_hermitian_transverse_capacity_forces_source_twice_transverse n r hn hHT⟩

/-- Primitive transverse multiplicity and three-way balance force the `3 × 2` arithmetic carrier
profile. -/
theorem primitive_balanced_actuality_capacity_classification
    (d n r m : ℕ) (hn : 0 < n)
    (hHK :
      doubledHermitianCapacity d n =
        doubledSkewCapacity d n)
    (hHT :
      doubledHermitianCapacity d n =
        doubledTransverseCapacity d n r)
    (hr : r = 1) (hm : m = n + r) :
    d = 2 ∧ n = 2 ∧ m = 3 := by
  obtain ⟨hd, hnr⟩ :=
    balanced_actuality_capacity_classification d n r hn hHK hHT
  omega

/-- In the primitive selected profile, all three doubled capacities are eight, hence all three
undoubled real capacities are four. -/
theorem primitive_balanced_actuality_capacities :
    doubledHermitianCapacity 2 2 = 8 ∧
      doubledSkewCapacity 2 2 = 8 ∧
      doubledTransverseCapacity 2 2 1 = 8 := by
  norm_num [doubledHermitianCapacity, doubledSkewCapacity, doubledTransverseCapacity]

end GaloisForLFunctions.HTGeometry
