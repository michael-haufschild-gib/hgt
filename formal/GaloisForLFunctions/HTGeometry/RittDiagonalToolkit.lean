import GaloisForLFunctions.HTGeometry.RittScalingCoefficientEigen

/-!
# The diagonal toolkit: ratios of coefficients under a scaling twist

When the shift moves the coordinate by a pure scaling the coefficient equations of the coprime split
are `Φ(R_k)·a^k = d·R_k`, one per coefficient, with the *same* scalar `d`.  Two nonzero coefficients
therefore produce a relation with no `d` in it at all: their ratio `w = R_k/R_{k'}` satisfies

`Φ(w) = a^{k' − k}·w`,

a pure power of the coordinate's multiplier, with exponent the difference of the two degrees — never
zero when the degrees differ.  Since the multiplier of the `m`-th coordinate is `q/ρ^m`, that relation
has exponent pair `(k' − k)·(1, −m)`, which is nontrivial.

The denominator of the coprime representation is the cleanest instance: its equations have `d = a^e`
with no eigenvalue at all, so any coefficient below the top gives such a relation, and a denominator
without one is a pure power of the coordinate.
-/

namespace GaloisForLFunctions.HTGeometry

open _root_.Polynomial

variable {K : Type*} [Field K]

/-- **The ratio of two coefficients obeys a pure power relation.** -/
theorem ratio_eigen_of_two_coeffs (Φ : K →+* K) {a d : K} (ha : a ≠ 0) {x y : K}
    {k k' : ℕ} (hx : Φ x * a ^ k = d * x) (hy : Φ y * a ^ k' = d * y)
    (hy0 : y ≠ 0) :
    Φ (x / y) = a ^ ((k' : ℤ) - (k : ℤ)) * (x / y) := by
  have hΦy : Φ y ≠ 0 := fun h => hy0 ((RingHom.injective Φ) (by rw [h, map_zero]))
  have hak : (a : K) ^ k ≠ 0 := pow_ne_zero _ ha
  rw [map_div₀, zpow_sub₀ ha, zpow_natCast, zpow_natCast]
  field_simp
  linear_combination y * hx - x * hy

end GaloisForLFunctions.HTGeometry
