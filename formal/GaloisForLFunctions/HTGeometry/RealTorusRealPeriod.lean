import GaloisForLFunctions.HTGeometry.RealTorusIdentityComponent
import GaloisForLFunctions.HTGeometry.HaarMeasureSubgroupIndex

/-!
# The real period is the number of components times the period of the identity component

For a real torus `A = V / Λ` with real structure `σ`, every left-invariant measure `μ` on the group
of real points satisfies

```
μ (A(ℝ)) = #π₀(A(ℝ)) · μ (A(ℝ)⁰) = #Ĥ¹(⟨σ⟩, Λ) · μ (A(ℝ)⁰) .
```

This is equation `(5.1)` of Suzuki, *Duality invariance of Faltings heights, Hodge line bundles and
global periods* (arXiv:2504.04993),

```
∫_{A(ℝ)} dz₁ ∧ … ∧ dz_g = #π₀(A(ℝ)) ,
```

once the identity-component period is normalised to `1`.  The normalisation itself is the statement
`∫_{A(ℝ)⁰} dz₁ ∧ … ∧ dz_g = 1`, which is about integration of differential forms over a real torus
and is not available on the present mathlib base; everything else in the equation is proved here.
-/

namespace GaloisForLFunctions.HTGeometry.RealTorusTop

open MeasureTheory Submodule Module

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {σ : V →ₗ[ℝ] V} {Λ : Submodule ℤ V}

/-- **The real period equals `#π₀` times the period of the identity component.** -/
theorem measure_univ_realPoints (hσ : ∀ x, σ (σ x) = x) (hΛ : ∀ x ∈ Λ, σ x ∈ Λ)
    [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    [MeasurableSpace (realPoints σ Λ hΛ)] [BorelSpace (realPoints σ Λ hΛ)]
    (μ : Measure (realPoints σ Λ hΛ)) [μ.IsAddLeftInvariant] :
    μ Set.univ = Nat.card (InvolutionTate.H1 (RealTorus.sigmaLat σ Λ hΛ))
      * μ (connectedComponent (0 : realPoints σ Λ hΛ)) := by
  haveI hΛclosed : IsClosed (Λ.toAddSubgroup : Set V) := AddSubgroup.isClosed_of_discrete
  haveI : MeasurableAdd (realPoints σ Λ hΛ) :=
    ⟨fun c => (continuous_const_add c).measurable, fun c => (continuous_add_const c).measurable⟩
  set H := (imageFixed σ Λ).addSubgroupOf (realPoints σ Λ hΛ) with hH
  have hcompact : IsCompact ((imageFixed σ Λ : AddSubgroup (Torus Λ)) : Set (Torus Λ)) := by
    rw [coe_imageFixed]
    exact isCompact_imageFixed hσ hΛ
  have hclosed : IsClosed ((H : AddSubgroup (realPoints σ Λ hΛ)) :
      Set (realPoints σ Λ hΛ)) :=
    hcompact.isClosed.preimage continuous_subtype_val
  haveI : Finite ((realPoints σ Λ hΛ) ⧸ H) := finite_quotient_realPoints hσ hΛ
  have hindex : H.index = Nat.card (InvolutionTate.H1 (RealTorus.sigmaLat σ Λ hΛ)) :=
    card_quotient_realPoints hσ hΛ
  rw [connectedComponent_eq hσ hΛ, ← hindex]
  exact HaarIndex.measure_univ_eq_index_mul H hclosed.measurableSet μ

end GaloisForLFunctions.HTGeometry.RealTorusTop
