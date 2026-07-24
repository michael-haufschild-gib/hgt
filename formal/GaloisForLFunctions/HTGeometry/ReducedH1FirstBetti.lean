import GaloisForLFunctions.HTGeometry.GraphCoboundary

/-!
# Reduced first cohomology of a finite complex is the first Betti number

Completing the reduced simplicial cohomology of the `1`-skeleton of a finite complex (a `SimpleGraph`),
this file computes the reduced first cohomology `H̃¹`.  Choosing an orientation of each edge (via a
linear order on the vertices), the degree-`1` coboundary target is the oriented-edge cochains, and

`H̃¹ = C¹ / im δ⁰ = (oriented edges → F) / im δ⁰`,

whose dimension is the first Betti number

`dim H̃¹ = |oriented edges| − (|V| − components) = |E| − |V| + components`,

by rank–nullity (`ker δ⁰ = componentConstant`, dimension = number of components) and the
quotient-dimension formula.  Together with `H̃⁰ = components − 1` this is the full reduced simplicial
cohomology of a finite graph.
-/

namespace GaloisForLFunctions

open SimpleGraph

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G : SimpleGraph V)
  [DecidableRel G.Adj] (F : Type*) [Field F]

/-- The oriented edges: adjacent pairs `(u,v)` with `u < v`. -/
def orientedEdges : Finset (V × V) :=
  Finset.univ.filter (fun p => p.1 < p.2 ∧ G.Adj p.1 p.2)

omit [DecidableEq V] in
theorem mem_orientedEdges {u v : V} : (u, v) ∈ orientedEdges G ↔ u < v ∧ G.Adj u v := by
  simp [orientedEdges]

/-- The degree-`1` coboundary into oriented-edge cochains: `(δ⁰ f)(u,v) = f v − f u`. -/
def orientedCoboundary : (V → F) →ₗ[F] (orientedEdges G → F) where
  toFun f := fun e => f e.val.2 - f e.val.1
  map_add' f g := by funext e; simp only [Pi.add_apply]; ring
  map_smul' r f := by
    funext e; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

omit [DecidableEq V] in
/-- The kernel of the oriented coboundary is the component-constant cochains. -/
theorem orientedCoboundary_ker :
    LinearMap.ker (orientedCoboundary G F) = componentConstant G F := by
  ext f
  rw [LinearMap.mem_ker, mem_componentConstant]
  constructor
  · intro hf u v huv
    rcases lt_trichotomy u v with h | h | h
    · have h0 : orientedCoboundary G F f ⟨(u, v), (mem_orientedEdges G).mpr ⟨h, huv⟩⟩ = 0 := by
        rw [hf]; rfl
      exact (sub_eq_zero.mp h0).symm
    · exact absurd h (G.ne_of_adj huv)
    · have h0 : orientedCoboundary G F f ⟨(v, u), (mem_orientedEdges G).mpr ⟨h, huv.symm⟩⟩ = 0 := by
        rw [hf]; rfl
      exact sub_eq_zero.mp h0
  · intro hf
    funext e
    obtain ⟨⟨u, v⟩, he⟩ := e
    rw [mem_orientedEdges] at he
    show f v - f u = 0
    rw [sub_eq_zero]; exact (hf u v he.2).symm

/-- The rank of the oriented coboundary is `|V| − (number of components)`. -/
theorem finrank_orientedCoboundary_range :
    Module.finrank F (LinearMap.range (orientedCoboundary G F))
      = Fintype.card V - Fintype.card G.ConnectedComponent := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (orientedCoboundary G F)
  rw [orientedCoboundary_ker, finrank_componentConstant] at hrn
  have hV : Module.finrank F (V → F) = Fintype.card V := Module.finrank_pi F
  rw [hV] at hrn
  omega

/-- **Reduced first cohomology is the first Betti number.**  The reduced first cohomology
`H̃¹ = (oriented edges → F) / im δ⁰` has dimension `|E| − (|V| − components) = |E| − |V| + components`. -/
theorem finrank_reducedH1 :
    Module.finrank F ((orientedEdges G → F) ⧸ LinearMap.range (orientedCoboundary G F))
      = (orientedEdges G).card - (Fintype.card V - Fintype.card G.ConnectedComponent) := by
  have hquot := Submodule.finrank_quotient_add_finrank (LinearMap.range (orientedCoboundary G F))
  have hW : Module.finrank F (orientedEdges G → F) = (orientedEdges G).card := by
    rw [Module.finrank_pi]; exact Fintype.card_coe _
  rw [finrank_orientedCoboundary_range, hW] at hquot
  omega

end

end GaloisForLFunctions
