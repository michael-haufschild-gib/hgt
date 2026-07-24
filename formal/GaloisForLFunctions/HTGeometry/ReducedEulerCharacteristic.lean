import GaloisForLFunctions.HTGeometry.ReducedH1FirstBetti
import GaloisForLFunctions.HTGeometry.ReducedH0DiscreteComplex

/-!
# The reduced Euler–Poincaré identity for a finite graph

With the full reduced simplicial cohomology of the `1`-skeleton in hand — `H̃⁰` of dimension
`components − 1` and `H̃¹` of dimension `|E| − |V| + components` — the reduced Euler characteristic
satisfies the Euler–Poincaré identity

`dim H̃⁰ + |E| + 1 = dim H̃¹ + |V|`   (both sides equal `|E| + components`),

equivalently `χ̃ = dim H̃⁰ − dim H̃¹ = |V| − |E| − 1`.  This ties the two reduced Betti numbers to the
combinatorial Euler characteristic of the complex.
-/

namespace GaloisForLFunctions

open SimpleGraph

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G : SimpleGraph V)
  [DecidableRel G.Adj] (F : Type*) [Field F]

/-- **Reduced Euler–Poincaré identity.**  `dim H̃⁰ + |E| + 1 = dim H̃¹ + |V|`. -/
theorem reduced_euler_poincare [Nonempty V] :
    Module.finrank F
        (componentConstant G F ⧸
          (F ∙ (⟨fun _ => (1 : F), one_mem_componentConstant G F⟩ : componentConstant G F)))
        + (orientedEdges G).card + 1
      = Module.finrank F
          ((orientedEdges G → F) ⧸ LinearMap.range (orientedCoboundary G F))
        + Fintype.card V := by
  have h0 := finrank_reducedH0 G F
  have h1 := finrank_reducedH1 G F
  haveI : Nonempty G.ConnectedComponent := ⟨G.connectedComponentMk (Classical.arbitrary V)⟩
  have hc : 1 ≤ Fintype.card G.ConnectedComponent := Fintype.card_pos
  have hcv : Fintype.card G.ConnectedComponent ≤ Fintype.card V :=
    Fintype.card_le_of_surjective _ (fun c => ConnectedComponent.ind (fun v => ⟨v, rfl⟩) c)
  have hrank : Fintype.card V - Fintype.card G.ConnectedComponent ≤ (orientedEdges G).card := by
    rw [← finrank_orientedCoboundary_range G F]
    calc Module.finrank F (LinearMap.range (orientedCoboundary G F))
          ≤ Module.finrank F (orientedEdges G → F) := Submodule.finrank_le _
      _ = (orientedEdges G).card := by rw [Module.finrank_pi]; exact Fintype.card_coe _
  rw [h0, h1]
  omega

end

end GaloisForLFunctions
