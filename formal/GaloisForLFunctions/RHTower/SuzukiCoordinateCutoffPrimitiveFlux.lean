import GaloisForLFunctions.RHTower.SuzukiCoordinateCutoffCovariance

/-!
# Suzuki coordinate-cutoff primitive flux

The first-order defect produced by a noncommuting coordinate cutoff is not a zero-order source.
The complete product-rule defect is, however, the derivative of a zero-order commutator plus a
zero-order cutoff event. This file proves the exact pointwise operator identity before any analytic
Gamma-space estimates.

The theorem is unconditional and assumes neither RH nor the conjectural completed Suzuki orbit
equation.
-/

namespace GaloisForLFunctions.RHTower

/-- Abstract coefficient `2L I + C` in the differentiated logarithmic normal equation. -/
def twoLPlus {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : ℝ) (C : Module.End ℝ V) : Module.End ℝ V :=
  (2 * L) • LinearMap.id + C

/-- Pointwise product-rule form of the primitive cutoff identity.

`Fdot` is the derivative of the carrier profile, while `Mdot` is the derivative of the cutoff.
The four terms in the first parenthesis on the right are exactly the product-rule expansion of
`∂L ([C,M]F)`. -/
theorem primitiveCutoffFlux_pointwise
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : ℝ) (C M Mdot : Module.End ℝ V) (F Fdot : V) :
    twoLPlus L C (Mdot F + M Fdot) - M (twoLPlus L C Fdot) =
      (C (Mdot F) + C (M Fdot) - Mdot (C F) - M (C Fdot)) +
        Mdot (twoLPlus L C F) := by
  simp only [twoLPlus, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_coe,
    id_eq, map_add, map_smul]
  module

/-- Commutator of two real-linear endomorphisms. -/
def linearCommutator {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A M : Module.End ℝ V) : Module.End ℝ V :=
  A.comp M - M.comp A

/-- Full primitive cutoff identity with an arbitrary zero-order operator `Z`.

The final term is exactly `[Z,M]F`; no derivative of `F` remains outside the expanded primitive
derivative. -/
theorem primitiveCutoffFlux_with_zeroOrder_pointwise
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : ℝ) (C Z M Mdot : Module.End ℝ V) (F Fdot : V) :
    (twoLPlus L C (Mdot F + M Fdot) + Z (M F)) -
        M (twoLPlus L C Fdot + Z F) =
      ((C (Mdot F) + C (M Fdot) - Mdot (C F) - M (C Fdot)) +
        Mdot (twoLPlus L C F)) +
        linearCommutator Z M F := by
  simp only [twoLPlus, linearCommutator, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.id_coe, id_eq, LinearMap.sub_apply, LinearMap.comp_apply, map_add, map_smul]
  module

end GaloisForLFunctions.RHTower
