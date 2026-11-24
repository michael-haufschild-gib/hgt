import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.RationalExteriorPullback
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.NormalizedDiagonalSystem

/-! The graph map on form tensors takes the wedge of the two rational
pullbacks and specializes tensor scalars by the same field maps. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology TensorProduct

namespace GlobalTheory.WH

open GlobalTheory.PD

variable {k E L : Type} [Field k] [Field E] [Field L] [Algebra k E] [Algebra k L]
  (j₁ j₂ : E →ₐ[k] L) {p q : ℕ}

/-- Restrict tensor scalars to the two field maps of a correspondence. -/
abbrev graphScalarMap : E ⊗[k] E →ₐ[k] L := Algebra.TensorProduct.productMap j₁ j₂

def graphDRPullback : DR k E ⊗[k] DR k E →ₗ[k] DR k L :=
  TensorProduct.lift (LinearMap.mul k (DR k L)) ∘ₗ
    TensorProduct.map (pullbackDR j₁).toLinearMap (pullbackDR j₂).toLinearMap

theorem graphDRPullback_tmul (u v : DR k E) :
    graphDRPullback j₁ j₂ (u ⊗ₜ[k] v) = pullbackDR j₁ u * pullbackDR j₂ v := by
  rw [graphDRPullback, LinearMap.comp_apply, TensorProduct.map_tmul, TensorProduct.lift.tmul]
  rfl

/-- Pull back both form factors and take their exterior product. -/
def graphFormPullback :
    ExteriorDifferentials k E q ⊗[k] ExteriorDifferentials k E p →ₗ[k] DR k L :=
  graphDRPullback j₁ j₂ ∘ₗ
    TensorProduct.map
      ((ExteriorDifferentials k E q).subtype.restrictScalars k)
      ((ExteriorDifferentials k E p).subtype.restrictScalars k)

theorem graphFormPullback_tmul (u : ExteriorDifferentials k E q) (v : ExteriorDifferentials k E p) :
    graphFormPullback j₁ j₂ (u ⊗ₜ[k] v) = pullbackDR j₁ (u : DR k E) * pullbackDR j₂ (v : DR k E) := by
  rw [graphFormPullback, LinearMap.comp_apply, TensorProduct.map_tmul, graphDRPullback_tmul]
  rfl

theorem graphFormPullback_action (s : E ⊗[k] E)
    (a : ExteriorDifferentials k E q ⊗[k] ExteriorDifferentials k E p) :
    graphFormPullback j₁ j₂ (tensorScalarAction s a) = graphScalarMap j₁ j₂ s • graphFormPullback j₁ j₂ a := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | add s t hs ht => simp only [map_add, LinearMap.add_apply, add_smul, hs, ht]
  | tmul b c =>
    induction a using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv => simp only [map_add, hu, hv, smul_add]
    | tmul u v =>
      rw [tensorScalarAction_tmul, graphFormPullback_tmul, graphFormPullback_tmul,
        Submodule.coe_smul, Submodule.coe_smul, pullbackDR_smul, pullbackDR_smul,
        Algebra.TensorProduct.productMap_apply_tmul, smul_mul_smul_comm]

end GlobalTheory.WH
