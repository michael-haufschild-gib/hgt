import Mathlib

/-!
# Gauss--Bonnet for finite simple graphs

A finite simple graph carries an intrinsic curvature, defined purely combinatorially by counting
the complete subgraphs through a vertex.  Writing `c_n(x)` for the number of `n`-cliques of `G`
containing the vertex `x`, the curvature of `G` at `x` is

```text
K(x) = Σ_{n ≥ 1} (-1)^(n+1) c_n(x) / n
     = 1 - deg(x)/2 + (# triangles at x)/3 - (# K₄ at x)/4 + ⋯
```

and the Euler characteristic of `G` is the alternating count of its complete subgraphs

```text
χ(G) = Σ_{n ≥ 1} (-1)^(n+1) v_n,      v_n = # of n-cliques of G.
```

**Gauss--Bonnet.**  `Σ_{x ∈ V} K(x) = χ(G)`.

The proof is one double count: every `n`-clique contains exactly `n` vertices, so it is shared
equally between them, `Σ_x c_n(x) = n · v_n`.  Curvature is thus the Euler characteristic
distributed over the vertices, exactly as in the smooth theorem.

This is the graph-theoretic Gauss--Bonnet theorem.  It is unconditional and holds for every finite
simple graph, with no regularity, planarity or embedding hypothesis.
-/

open Finset
open scoped Real

namespace GaloisForLFunctions.HTGeometry.GaussBonnet

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The number of `n`-cliques of `G` containing a given vertex. -/
def cliquesAt (x : V) (n : ℕ) : ℕ := #{s ∈ G.cliqueFinset n | x ∈ s}

/-- The clique numbers of `G`: `cliqueCount n` is the number of `n`-cliques. -/
def cliqueCount (n : ℕ) : ℕ := #(G.cliqueFinset n)

/-- The **combinatorial curvature** of a finite simple graph at a vertex:
`K(x) = Σ_{n ≥ 1} (-1)^(n+1) c_n(x)/n`. -/
noncomputable def graphCurvature (x : V) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (Fintype.card V),
    (-1 : ℝ) ^ (n + 1) * (cliquesAt G x n : ℝ) / (n : ℝ)

/-- The **Euler characteristic** of a finite simple graph:
`χ(G) = Σ_{n ≥ 1} (-1)^(n+1) v_n`. -/
noncomputable def graphEulerChar : ℝ :=
  ∑ n ∈ Finset.Icc 1 (Fintype.card V), (-1 : ℝ) ^ (n + 1) * (cliqueCount G n : ℝ)

/-- **Every `n`-clique is shared equally between its `n` vertices.** -/
theorem sum_cliquesAt (n : ℕ) :
    ∑ x : V, cliquesAt G x n = n * cliqueCount G n := by
  have hstep : ∑ x : V, cliquesAt G x n
      = ∑ s ∈ G.cliqueFinset n, ∑ x : V, if x ∈ s then 1 else 0 := by
    simp only [cliquesAt, Finset.card_filter]
    exact Finset.sum_comm
  rw [hstep]
  have hcard : ∀ s ∈ G.cliqueFinset n, (∑ x : V, if x ∈ s then 1 else 0) = n := by
    intro s hs
    have hs' : s.card = n := (SimpleGraph.mem_cliqueFinset_iff.mp hs).2
    simp [← hs']
  rw [Finset.sum_congr rfl hcard]
  simp [cliqueCount, mul_comm]

/-- **Gauss--Bonnet for finite simple graphs.**  The total combinatorial curvature of a finite
simple graph is its Euler characteristic. -/
theorem gauss_bonnet_graph :
    ∑ x : V, graphCurvature G x = graphEulerChar G := by
  unfold graphCurvature graphEulerChar
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsum : ∑ x : V, ((-1 : ℝ) ^ (n + 1) * (cliquesAt G x n : ℝ) / (n : ℝ))
      = (-1 : ℝ) ^ (n + 1) / (n : ℝ) * ∑ x : V, (cliquesAt G x n : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [hsum]
  have hcount : ∑ x : V, (cliquesAt G x n : ℝ) = (n : ℝ) * (cliqueCount G n : ℝ) := by
    have := sum_cliquesAt G n
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) this
  rw [hcount]
  field_simp

/-- The same statement in the normalization of the smooth theorem:
`Σ_x 2π K(x) = 2π χ(G)`. -/
theorem gauss_bonnet_graph_two_pi :
    ∑ x : V, 2 * π * graphCurvature G x = 2 * π * graphEulerChar G := by
  rw [← Finset.mul_sum, gauss_bonnet_graph G]

end GaloisForLFunctions.HTGeometry.GaussBonnet
