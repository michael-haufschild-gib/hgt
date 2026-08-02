import GaloisForLFunctions.RHTower.DeningerRadialFrechet

/-!
# The three spaces of the Poisson sequence are Fréchet

Schwartz space is complete and metrizable, so its closed subspaces are; the radial space is a closed
subspace of a countable product of copies of it, so it is too; and the cokernel is the quotient of a
complete first countable topological group by a closed subgroup, hence complete.

* `instPseudoMetrizableSpaceDeningerMeyerCap`, `instPseudoMetrizableSpaceDeningerRadialCompat` :
  the two source spaces are metrizable.
* `deningerMZeta_completeSpace` : **the cokernel is complete.**
-/

open scoped Real SchwartzMap Topology
open Filter Complex GaloisForLFunctions TopologicalSpace

noncomputable section

namespace RHTower

/-! ## Metrizability -/

instance instPseudoMetrizableSpaceDeningerMeyerCap : PseudoMetrizableSpace DeningerMeyerCap :=
  TopologicalSpace.PseudoMetrizableSpace.subtype (DeningerMeyerCap : Set 𝓢(ℝ, ℂ))

instance instPseudoMetrizableSpaceDeningerRadialCompat :
    PseudoMetrizableSpace deningerRadialCompat :=
  TopologicalSpace.PseudoMetrizableSpace.subtype
    ((deningerRadialCompat : Submodule ℂ (∀ _ : ℤ, 𝓢(ℝ, ℂ))) : Set (∀ _ : ℤ, 𝓢(ℝ, ℂ)))

/-! ## The uniform structure of the radial space -/

instance instIsUniformAddGroupDeningerRadialCompat : IsUniformAddGroup deningerRadialCompat :=
  IsUniformAddGroup.comap
    (deningerRadialCompat.toAddSubgroup.subtype : deningerRadialCompat →+ (∀ _ : ℤ, 𝓢(ℝ, ℂ)))

/-! ## The cokernel is complete -/

/-- **The cokernel of the Poisson operator is complete**: the quotient of a complete first
countable topological group by a subgroup. -/
theorem deningerMZeta_completeSpace :
    @CompleteSpace DeningerMZeta (IsTopologicalAddGroup.leftUniformSpace DeningerMZeta) :=
  QuotientAddGroup.completeSpace_left deningerRadialCompat
    ((LinearMap.range (deningerPoissonLM) : Submodule ℂ deningerRadialCompat).toAddSubgroup)

end RHTower

end
