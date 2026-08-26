import GaloisForLFunctions.HTGeometry.AffineExponentialGroupHopf
import GaloisForLFunctions.HTGeometry.IteratedBialgebraProductImage
import Mathlib.RingTheory.HopfAlgebra.Quotient

/-!
# Antipode compatibility for affine-exponential coordinates

For the commutative Hopf coordinate algebra of `Gₐⁿ × Gₘⁿ`, comultiplication commutes with
the antipode applied in both tensor factors.  This is the inversion-symmetry input for stable
finite-product image kernels.
-/

open scoped TensorProduct
open Coalgebra Bialgebra HopfAlgebra

namespace GaloisForLFunctions.HTGeometry

open AffineExponentialGroup

noncomputable section

/-- In affine-exponential coordinates, inversion before multiplication is inversion in both
factors after multiplication. -/
theorem affineExponential_comul_antipode
    (k : Type*) [Field k] {n : ℕ} :
    (Bialgebra.comulAlgHom k (CoordinateAlgebra k n)).comp
        (HopfAlgebra.antipodeAlgHom k (CoordinateAlgebra k n)) =
      (tensorAlgHom
        (HopfAlgebra.antipodeAlgHom k (CoordinateAlgebra k n))
        (HopfAlgebra.antipodeAlgHom k (CoordinateAlgebra k n))).comp
          (Bialgebra.comulAlgHom k (CoordinateAlgebra k n)) := by
  ext m
  · change
      Coalgebra.comul (R := k)
          (HopfAlgebra.antipode k (torusCharacter k m)) =
        tensorAlgHom
          (HopfAlgebra.antipodeAlgHom k (CoordinateAlgebra k n))
          (HopfAlgebra.antipodeAlgHom k (CoordinateAlgebra k n))
          (Coalgebra.comul (R := k) (torusCharacter k m))
    rw [antipode_torusCharacter, comul_torusCharacter, comul_torusCharacter]
    simp only [tensorAlgHom_tmul]
    rw [show
      HopfAlgebra.antipodeAlgHom k (CoordinateAlgebra k n) (torusCharacter k m) =
        torusCharacter k (-m) by exact antipode_torusCharacter k m]
  · change
      Coalgebra.comul (R := k)
          (HopfAlgebra.antipode k (additiveCoordinate k m)) =
        tensorAlgHom
          (HopfAlgebra.antipodeAlgHom k (CoordinateAlgebra k n))
          (HopfAlgebra.antipodeAlgHom k (CoordinateAlgebra k n))
          (Coalgebra.comul (R := k) (additiveCoordinate k m))
    rw [antipode_additiveCoordinate, map_neg, comul_additiveCoordinate]
    simp only [map_add, tensorAlgHom_tmul, map_one]
    rw [show
      HopfAlgebra.antipodeAlgHom k (CoordinateAlgebra k n) (additiveCoordinate k m) =
        -additiveCoordinate k m by exact antipode_additiveCoordinate k m]
    simp only [TensorProduct.neg_tmul, TensorProduct.tmul_neg]
    abel

end

end GaloisForLFunctions.HTGeometry
