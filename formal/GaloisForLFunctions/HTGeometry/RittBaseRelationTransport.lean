import GaloisForLFunctions.HTGeometry.RittTreeChannelDegree
import GaloisForLFunctions.HTGeometry.RittRationalTransport

/-!
# The base relation of a tower collapse is an affine transport equation

The collapse of the jet tower produces a relation in the base field of the shape

`ψ u = b · u + A`,

with `b = q^i ρ^k` built from the multiplier and the chain-rule factor.  That is literally the
affine transport equation of weight zero for `u` with inhomogeneity `A`, so the pole-transport and
orbit machinery for rational maps applies to it directly.

Together with the degree computation — a base element fixed by the shift of a channel map is a
constant — this is the interface through which the remaining branch of the tower alternative is to
be refuted: the homogeneous case is Ritt's form or a constant, and the inhomogeneous case is a
transport equation.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K] [CharZero K]

/-- **A base relation is an affine transport equation of weight zero.** -/
theorem isRatAffineTransport_of_base_relation {R : RatFunc K}
    (hR : ¬ ∃ c : K, R = RatFunc.C c) {u A b : RatFunc K}
    (hrel : ratFuncSubstitutionAlgHom R hR u = b * u + A) :
    IsRatAffineTransport R hR 0 b A u := by
  rw [IsRatAffineTransport, zpow_zero, mul_one]
  exact hrel

/-- The homogeneous base relation of a channel map with trivial exponents pins the base element to
a constant. -/
theorem eq_C_of_base_relation_trivial {p : ℕ} (hp : 2 ≤ p) {u v : K} (huv : u ≠ v)
    {hR : ¬ ∃ c : K, treeRG p u v = RatFunc.C c} {a : RatFunc K}
    (hrel : ratFuncSubstitutionAlgHom (treeRG p u v) hR a = 1 * a + 0) :
    ∃ c : K, a = RatFunc.C c := by
  refine eq_C_of_substitution_fixed_treeRG hp huv (hR := hR) ?_
  rw [hrel, one_mul, add_zero]

/-- **The inhomogeneous base relation of a collapse, as a transport equation.**  The multiplier
`q^i ρ^k` of the relation is the coefficient `b` of the transport equation and the inhomogeneity is
the base multiple of the Faà di Bruno coefficient. -/
theorem isRatAffineTransport_of_inhomogeneous_base_relation {R : RatFunc K}
    (hR : ¬ ∃ c : K, R = RatFunc.C c) {u A z : RatFunc K} {lam : K} {i k : ℤ}
    (hrel : ratFuncSubstitutionAlgHom R hR u
      = RatFunc.C lam ^ i * (ratFuncDeriv R) ^ k * u + z * A) :
    IsRatAffineTransport R hR 0 (RatFunc.C lam ^ i * (ratFuncDeriv R) ^ k) (z * A) u :=
  isRatAffineTransport_of_base_relation hR hrel

end GaloisForLFunctions.HTGeometry
