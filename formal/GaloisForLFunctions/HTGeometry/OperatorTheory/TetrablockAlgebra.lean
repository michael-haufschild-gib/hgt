import GaloisForLFunctions.HTGeometry.OperatorTheory.HexablockAlgebra

/-!
# Tetrablock sum coordinates

For commuting isometries `u,v,z`, the polynomial tuple
`(z(u+v)/2,(u+v)/2,uvz)` satisfies the tetrablock cross relation.
The difference channel gives its exact complementary energy.
These are the algebraic identities underlying the parametrization in
Pal–Su–Tomar, *Hardy Spaces and Toeplitz operators on the Hexablock*, §8.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.Tetrablock
open Hexablock
variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

def x₁ (u v z : A) : A := z * halfSum u v
def x₂ (u v : A) : A := halfSum u v
def x₃ (u v z : A) : A := u * v * z

/-- The sum channel and its difference complement split identity exactly. -/
theorem energy (u v : A) (hu : star u * u = 1) (hv : star v * v = 1) :
    star (halfDiff u v) * halfDiff u v + star (x₂ u v) * x₂ u v = 1 := by
  have h := polarization u v 1
  simp only [mul_one, hu, hv] at h
  rw [x₂, h, smul_add]
  module

/-- The adjoint sum channel recovers its partner against the product coordinate. -/
theorem cross (u v z : A) (hu : star u * u = 1) (hv : star v * v = 1)
    (huv : Commute u v) (huz : Commute u z) (hvz : Commute v z) :
    star (x₂ u v) * x₃ u v z = x₁ u v z := by
  have hc : star v * u * v = u := by
    rw [mul_assoc, huv.eq, ← mul_assoc, hv, one_mul]
  calc
    star (x₂ u v) * x₃ u v z =
        (1 / 2 : ℂ) • ((star u * u) * v + star v * u * v) * z := by
      simp only [x₂, x₃, halfSum, star_smul, star_add, star_div₀, star_one, star_ofNat,
        smul_mul_assoc, add_mul, mul_add, mul_assoc]
    _ = halfSum u v * z := by rw [hu, one_mul, hc, add_comm v u]; rfl
    _ = x₁ u v z := (huz.add_left hvz).smul_left _

/-- The final coordinate of the tetrablock tuple is an isometry. -/
theorem last_isometry (u v z : A)
    (hu : star u * u = 1) (hv : star v * v = 1) (hz : star z * z = 1) :
    star (x₃ u v z) * x₃ u v z = 1 :=
  isometry_mul _ _ (isometry_mul _ _ hu hv) hz

end GaloisForLFunctions.HTGeometry.Tetrablock

#print axioms GaloisForLFunctions.HTGeometry.Tetrablock.energy
#print axioms GaloisForLFunctions.HTGeometry.Tetrablock.cross
#print axioms GaloisForLFunctions.HTGeometry.Tetrablock.last_isometry
