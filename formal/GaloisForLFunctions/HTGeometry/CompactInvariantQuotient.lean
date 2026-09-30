import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Compact operators on literal Hilbert quotients

A continuous operator preserving a subspace induces a continuous operator
on the quotient itself. When orthogonal projection exists, the orthogonal
representative gives an isometric bounded section. Factoring the induced
operator through that section proves compactness on the literal quotient.
The orthogonal complement is used only to construct the section.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K E : Type*} [RCLike K] [NormedAddCommGroup E] [InnerProductSpace K E]

/-- A continuous operator preserving a subspace induces an operator on its literal quotient. -/
def continuousInvariantQuotient (T : E →L[K] E) (S : Submodule K E)
    (hS : ∀ x ∈ S, T x ∈ S) : (E ⧸ S) →L[K] (E ⧸ S) :=
  S.liftQL (S.mkQL.comp T) (fun x hx => by
    change S.mkQ (T x) = 0
    exact (Submodule.Quotient.mk_eq_zero S).mpr (hS x hx))

theorem continuousInvariantQuotient_toLinearMap (T : E →L[K] E) (S : Submodule K E)
    (hS : ∀ x ∈ S, T x ∈ S) :
    (continuousInvariantQuotient T S hS).toLinearMap = S.mapQ S T.toLinearMap (fun {_} hx => hS _ hx) := rfl

theorem continuousInvariantQuotient_mkQL (T : E →L[K] E) (S : Submodule K E)
    (hS : ∀ x ∈ S, T x ∈ S) (x : E) :
    continuousInvariantQuotient T S hS (S.mkQL x) = S.mkQL (T x) := rfl

/-- The bounded section selects the orthogonal representative of a quotient class. -/
def orthogonalQuotientSection (S : Submodule K E) [S.HasOrthogonalProjection] :
    (E ⧸ S) →L[K] E :=
  Sᗮ.subtypeL.comp S.quotientEquivOrthogonal.toContinuousLinearEquiv.toContinuousLinearMap

theorem mkQL_orthogonalQuotientSection (S : Submodule K E) [S.HasOrthogonalProjection]
    (x : E ⧸ S) : S.mkQL (orthogonalQuotientSection S x) = x := by
  let v : Sᗮ := S.quotientEquivOrthogonal x
  change S.mkQL (v : E) = x
  calc
    _ = S.quotientEquivOrthogonal.symm v :=
      (S.quotientEquivOrthogonal_symm_eq_mk v v.property).symm
    _ = x := S.quotientEquivOrthogonal.symm_apply_apply x

theorem norm_orthogonalQuotientSection (S : Submodule K E) [S.HasOrthogonalProjection]
    (x : E ⧸ S) : ‖orthogonalQuotientSection S x‖ = ‖x‖ :=
  S.quotientEquivOrthogonal.norm_map x

theorem continuousInvariantQuotient_eq_comp_section
    (T : E →L[K] E) (S : Submodule K E) [S.HasOrthogonalProjection]
    (hS : ∀ x ∈ S, T x ∈ S) :
    continuousInvariantQuotient T S hS = S.mkQL.comp (T.comp (orthogonalQuotientSection S)) := by
  ext x
  change continuousInvariantQuotient T S hS x = S.mkQL (T (orthogonalQuotientSection S x))
  rw [← continuousInvariantQuotient_mkQL T S hS, mkQL_orthogonalQuotientSection]

/-- Compactness descends to the literal Hilbert quotient. -/
theorem isCompactOperator_continuousInvariantQuotient
    (T : E →L[K] E) (S : Submodule K E) [S.HasOrthogonalProjection]
    (hS : ∀ x ∈ S, T x ∈ S) (hT : IsCompactOperator T) :
    IsCompactOperator (continuousInvariantQuotient T S hS) := by
  rw [continuousInvariantQuotient_eq_comp_section]
  exact (hT.comp_clm (orthogonalQuotientSection S)).clm_comp S.mkQL

end

end GaloisForLFunctions.HTGeometry
