import GaloisForLFunctions.HTGeometry.CotangentPresentationCokernel
import GaloisForLFunctions.HTGeometry.SquareMatrixCorankOne

/-!
# The different of a square presentation is the Jacobian ideal

The whole Jacobian–different bridge, in one citable statement.  For a square presentation over a
discrete valuation ring whose reduced Jacobian has vanishing determinant but a surviving cofactor of
codimension one:

```text
annihilator_kaehler_eq_span_jacobian_of_det_eq_zero
    ** Ann (Ω[S⁄R]) = (P.jacobian) **
```

One containment is `JacobianKaehlerAnnihilator.jacobian_smul_kaehler_eq_zero`, which needs no
hypotheses at all; the other is the Smith-normal-form computation of
`CorankOneCokernelDeterminant`, transported through the cotangent presentation of
`CotangentPresentationCokernel` and stated in rank form by `SquareMatrixCorankOne`.

Read at a place of a finite extension this says the divisorial order of the different is the order
of the Jacobian, so a Jacobian of order one is a simple fold.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Algebra

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsDomain S]
variable [IsDiscreteValuationRing S] [Algebra R S] {N : ℕ}

/-- **The different of a square presentation over a discrete valuation ring is the Jacobian
ideal, whenever the reduced Jacobian has corank one.**  This is the citable form of the whole
Jacobian–different bridge: `jacobian_smul_kaehler_eq_zero` gives one containment for free, and the
Smith-normal-form computation gives the other. -/
theorem annihilator_kaehler_eq_span_jacobian_of_det_eq_zero
    (P : Algebra.PreSubmersivePresentation R S (Fin (N + 1)) (Fin (N + 1)))
    (hmap : P.map = _root_.id)
    (hdet : ((LinearMap.toMatrix' P.aevalDifferential).map (IsLocalRing.residue S)).det = 0)
    {r c : Fin N → Fin (N + 1)}
    (hB : (((LinearMap.toMatrix' P.aevalDifferential).map
      (IsLocalRing.residue S)).submatrix r c).det ≠ 0) :
    Module.annihilator S Ω[S⁄R] = Ideal.span {P.jacobian} :=
  annihilator_kaehler_eq_span_jacobian P hmap
    (rank_add_one_eq_of_det_eq_zero (r := r) (c := c) _ hdet hB)

end

end GaloisForLFunctions.HTGeometry
