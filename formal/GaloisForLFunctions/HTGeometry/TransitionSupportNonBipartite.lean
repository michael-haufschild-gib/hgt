import GaloisForLFunctions.HTGeometry.LocalInteractionLiftAnalyticRelationLaw

/-!
# A triangle in the support graph forbids bipartiteness

The leaf-extension laws assume that the support graph of a transition matrix is not bipartite, and
nothing produced it.  Bipartiteness is two-colourability, so any odd cycle refutes it, and the
shortest one is a triangle: three distinct sites whose mutual transition products do not vanish.

The criterion is checkable entrywise on the matrix, and it applies in particular to every transition
matrix with no vanishing off-diagonal entry on at least three sites.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **A triangle forbids a two-colouring.**  Three mutually adjacent vertices cannot receive
pairwise distinct colours from a two-element palette. -/
theorem not_isBipartite_of_adj_triangle {V : Type*} {G : SimpleGraph V} {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hac : G.Adj a c) : ¬ G.IsBipartite := by
  rintro ⟨C⟩
  have h1 : (C a).val ≠ (C b).val := fun h => C.valid hab (Fin.ext h)
  have h2 : (C b).val ≠ (C c).val := fun h => C.valid hbc (Fin.ext h)
  have h3 : (C a).val ≠ (C c).val := fun h => C.valid hac (Fin.ext h)
  have ha := (C a).isLt
  have hb := (C b).isLt
  have hc := (C c).isLt
  omega

/-- **A nonvanishing transition triangle makes the support graph nonbipartite.** -/
theorem not_isBipartite_transitionSupportGraph_of_triangle {α : Type*}
    {transition : Matrix α α ℂ} {a b c : α}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (h1 : transition a b * transition b a ≠ 0)
    (h2 : transition b c * transition c b ≠ 0)
    (h3 : transition a c * transition c a ≠ 0) :
    ¬ (transitionSupportGraph transition).IsBipartite :=
  not_isBipartite_of_adj_triangle (G := transitionSupportGraph transition)
    ⟨hab, h1⟩ ⟨hbc, h2⟩ ⟨hac, h3⟩

/-- **Every fully supported transition matrix on three or more sites is nonbipartite.** -/
theorem not_isBipartite_transitionSupportGraph_of_offDiag_ne_zero {α : Type*}
    {transition : Matrix α α ℂ} (hsupp : ∀ i j, i ≠ j → transition i j ≠ 0)
    {a b c : α} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ¬ (transitionSupportGraph transition).IsBipartite :=
  not_isBipartite_transitionSupportGraph_of_triangle hab hbc hac
    (mul_ne_zero (hsupp a b hab) (hsupp b a hab.symm))
    (mul_ne_zero (hsupp b c hbc) (hsupp c b hbc.symm))
    (mul_ne_zero (hsupp a c hac) (hsupp c a hac.symm))

end GaloisForLFunctions.HTGeometry
