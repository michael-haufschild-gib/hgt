import GaloisForLFunctions.RHTower.Deninger.DeningerAbsGenerator

/-!
# The Calderón graph is Lagrangian

The Green symplectic form on Cauchy data is `⟪φ, μ⟫ - ⟪ν, ψ⟫`, and a pair is symplectically
orthogonal to the graph of an operator exactly when it lies in the adjoint of that graph.  So the
graph of a densely defined self-adjoint operator is its own symplectic orthogonal: isotropy is
symmetry, and maximality is the identification of the adjoint domain.

For the Kummer phase stage the operator is the absolute value of the phase generator, whose graph is
therefore Lagrangian.

* `deningerGraph_symplectic_iff` : the adjoint of a submodule is its symplectic orthogonal.
* `deningerCalderonGraph_lagrangian` : the graph of a self-adjoint operator is Lagrangian.
* `deningerAbsGenerator_graph_lagrangian` : the Kummer Calderón graph is Lagrangian.
-/

namespace RHTower

open HilbertSchmidt

noncomputable section

universe u

section Lagrangian

variable {𝕜 : Type*} [RCLike 𝕜] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

omit [CompleteSpace H] in
/-- **Symplectic orthogonality to a submodule of Cauchy data is membership in its adjoint.**  The
Green form `⟪ν, φ'⟫ - ⟪φ, ν'⟫` is exactly the pairing defining the adjoint. -/
theorem deningerGraph_symplectic_iff (g : Submodule 𝕜 (H × H)) (x : H × H) :
    x ∈ g.adjoint ↔ ∀ a b, (a, b) ∈ g → inner 𝕜 b x.fst - inner 𝕜 a x.snd = 0 :=
  Submodule.mem_adjoint_iff g x

/-- **The graph of a densely defined self-adjoint operator is Lagrangian.**  Its symplectic
orthogonal is the graph of the adjoint, which is the operator itself. -/
theorem deningerCalderonGraph_lagrangian {A : H →ₗ.[𝕜] H} (hdense : Dense (A.domain : Set H))
    (hA : IsSelfAdjoint A) : A.graph.adjoint = A.graph := by
  rw [← LinearPMap.adjoint_graph_eq_graph_adjoint hdense, LinearPMap.isSelfAdjoint_def.mp hA]

end Lagrangian

section KummerGraph

variable {ι : Type u} [DecidableEq ι]

/-- **The Kummer Calderón graph is Lagrangian.**  The Cauchy data of the Poisson extension are the
graph of the absolute value of the phase generator, which is densely defined and self-adjoint. -/
theorem deningerAbsGenerator_graph_lagrangian (ℓ : ι → ℝ) :
    (deningerAbsGenerator ℓ).graph.adjoint = (deningerAbsGenerator ℓ).graph :=
  deningerCalderonGraph_lagrangian (maximalRealDiagonal_dense _)
    (deningerAbsGenerator_isSelfAdjoint ℓ)

/-- **The phase generator's graph is Lagrangian** as well. -/
theorem deningerPhaseGenerator_graph_lagrangian (ℓ : ι → ℝ) :
    (deningerPhaseGenerator ℓ).graph.adjoint = (deningerPhaseGenerator ℓ).graph :=
  deningerCalderonGraph_lagrangian (deningerPhaseGenerator_dense ℓ)
    (deningerPhaseGenerator_isSelfAdjoint ℓ)

end KummerGraph

end

end RHTower
