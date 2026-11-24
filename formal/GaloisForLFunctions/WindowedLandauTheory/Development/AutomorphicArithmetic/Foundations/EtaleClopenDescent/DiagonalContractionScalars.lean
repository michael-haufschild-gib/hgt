import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveAffineIdentityTensor
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.RationalTensorCoordinates

/-! A trace-wedge identity tensor annihilates scalar equations vanishing
under multiplication of the two function-field factors. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology TensorProduct

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E] {p q : ℕ}

local instance {r : ℕ} : IsScalarTower k F (ExteriorDifferentials k E r) :=
  IsScalarTower.to₁₂₄ k F E (ExteriorDifferentials k E r)

omit [Algebra k F] [IsScalarTower k F E] in
private theorem traceWedgeLeftDual_smul_balance (τ : DR k E →ₗ[E] E)
    (a : E) (u : ExteriorDifferentials k E q) (v : ExteriorDifferentials k E p) :
    traceWedgeLeftDual (F := F) τ (a • u) v = traceWedgeLeftDual (F := F) τ u (a • v) := by
  simp only [traceWedgeLeftDual_apply, Submodule.coe_smul, smul_mul_assoc, mul_smul_comm]

/-- Multiplying the first tensor factor by a field scalar has the same
effect as multiplying the input of the identity action by that scalar. -/
theorem traceWedgeContraction_act_tmul (τ : DR k E →ₗ[E] E)
    (a b : E) (t : ExteriorDifferentials k E q ⊗[k] ExteriorDifferentials k E p)
    (v : ExteriorDifferentials k E p) :
    tensorContraction ((traceWedgeLeftDual (F := F) τ).flip v)
        (tensorScalarAction (a ⊗ₜ[k] b) t) =
      b • tensorContraction ((traceWedgeLeftDual (F := F) τ).flip (a • v)) t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add t u ht hu => simp only [map_add, ht, hu, smul_add]
  | tmul u w =>
    simp only [tensorScalarAction_tmul, tensorContraction_tmul, LinearMap.flip_apply,
      traceWedgeLeftDual_smul_balance]
    let c := traceWedgeLeftDual (F := F) τ u (a • v)
    have hc (w' : ExteriorDifferentials k E p) : c • w' = algebraMap F E c • w' :=
      (IsScalarTower.algebraMap_smul E c w').symm
    change c • (b • w) = b • (c • w)
    rw [hc (b • w), hc w, smul_smul, smul_smul, mul_comm]

/-- If a tensor acts by multiplication by a base-field scalar, applying
any function-field tensor to it specializes that tensor to the diagonal. -/
theorem traceWedgeContraction_act_eq (τ : DR k E →ₗ[E] E)
    {t : ExteriorDifferentials k E q ⊗[k] ExteriorDifferentials k E p} {f : F}
    (ht : ∀ v : ExteriorDifferentials k E p,
      tensorContraction ((traceWedgeLeftDual (F := F) τ).flip v) t = f • v)
    (s : E ⊗[k] E) (v : ExteriorDifferentials k E p) :
    tensorContraction ((traceWedgeLeftDual (F := F) τ).flip v)
        (tensorScalarAction s t) = Algebra.TensorProduct.lmul' k s • (f • v) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply, add_smul, ha, hb]
  | tmul a b =>
    rw [traceWedgeContraction_act_tmul, ht, Algebra.TensorProduct.lmul'_apply_tmul]
    have hf (w : ExteriorDifferentials k E p) : f • w = algebraMap F E f • w :=
      (IsScalarTower.algebraMap_smul E f w).symm
    simp only [hf, smul_smul]
    exact congrArg (fun s : E => s • v) (by ac_rfl)

end GlobalTheory.PD
