import GaloisForLFunctions.HTGeometry.OrbitBalance

/-!
# Orbit balance with arbitrary additive coefficients

The divisor-level orbit obstruction in `OrbitBalance` uses integer coefficients.  Principal parts
of meromorphic functions instead have coefficients in `ℂ` (or, more generally, in an additive
commutative group).  This module supplies that coefficient-generic algebraic core.

On an integer-indexed translation orbit, every finitely supported shift coboundary has total
coefficient zero.  Consequently a single nonzero principal-part coefficient on one orbit cannot be
a shift coboundary.  This is the exact finite-support obstruction used after the cylinder descent
in the double-sine defect-coset theorem.
-/

namespace GaloisForLFunctions

open scoped BigOperators

noncomputable section

/-- Total coefficient of a finitely supported orbit datum with values in an additive commutative
monoid. -/
def additiveOrbitSum {ι A : Type*} [AddCommMonoid A] (D : ι →₀ A) : A :=
  D.sum fun _ a => a

@[simp]
theorem additiveOrbitSum_zero {ι A : Type*} [AddCommMonoid A] :
    additiveOrbitSum (0 : ι →₀ A) = 0 := by
  simp [additiveOrbitSum]

@[simp]
theorem additiveOrbitSum_single {ι A : Type*} [AddCommMonoid A]
    (i : ι) (a : A) :
    additiveOrbitSum (Finsupp.single i a) = a := by
  simp [additiveOrbitSum]

theorem additiveOrbitSum_add {ι A : Type*} [AddCommMonoid A]
    (D E : ι →₀ A) :
    additiveOrbitSum (D + E) = additiveOrbitSum D + additiveOrbitSum E := by
  rw [additiveOrbitSum, Finsupp.sum_add_index']
  · rfl
  · intro i
    rfl
  · intro i a b
    rfl

theorem additiveOrbitSum_sub {ι A : Type*} [AddCommGroup A]
    (D E : ι →₀ A) :
    additiveOrbitSum (D - E) = additiveOrbitSum D - additiveOrbitSum E := by
  rw [additiveOrbitSum]
  exact Finsupp.sum_sub_index (h := fun _ a => a) (by intro i a b; rfl)

/-- The coefficient-generic finite shift coboundary on an integer orbit. -/
def additiveIntShiftCoboundary {A : Type*} [AddCommGroup A]
    (E : ℤ →₀ A) : ℤ →₀ A :=
  E.support.sum fun z => Finsupp.single (z - 1) (E z) - Finsupp.single z (E z)

/-- Every finite additive shift coboundary has zero total coefficient on its orbit. -/
theorem additiveOrbitSum_intShiftCoboundary {A : Type*} [AddCommGroup A]
    (E : ℤ →₀ A) :
    additiveOrbitSum (additiveIntShiftCoboundary E) = 0 := by
  unfold additiveIntShiftCoboundary
  induction E.support using Finset.induction_on with
  | empty => simp
  | insert z s hzs ih =>
      rw [Finset.sum_insert hzs, additiveOrbitSum_add, additiveOrbitSum_sub,
        additiveOrbitSum_single, additiveOrbitSum_single, ih]
      abel

/-- Nonzero total coefficient separates an orbit datum from every finite shift coboundary. -/
theorem ne_additiveIntShiftCoboundary_of_additiveOrbitSum_ne_zero
    {A : Type*} [AddCommGroup A] {D : ℤ →₀ A}
    (hD : additiveOrbitSum D ≠ 0) (E : ℤ →₀ A) :
    D ≠ additiveIntShiftCoboundary E := by
  intro h
  apply hD
  rw [h, additiveOrbitSum_intShiftCoboundary]

/-- A single nonzero coefficient on one orbit cannot be a finite shift coboundary.  For `A=ℂ`,
this is the fixed-pole-order principal-part obstruction used in rational shift summability. -/
theorem single_ne_additiveIntShiftCoboundary {A : Type*} [AddCommGroup A]
    (z : ℤ) {a : A} (ha : a ≠ 0) (E : ℤ →₀ A) :
    Finsupp.single z a ≠ additiveIntShiftCoboundary E := by
  apply ne_additiveIntShiftCoboundary_of_additiveOrbitSum_ne_zero
  simpa using ha

end

end GaloisForLFunctions
