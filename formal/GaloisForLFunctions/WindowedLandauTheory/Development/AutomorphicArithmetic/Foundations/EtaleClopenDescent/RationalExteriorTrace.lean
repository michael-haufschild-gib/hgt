import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.RationalExteriorPullback
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EtaleFormTraceBaseChange
import Mathlib.RingTheory.Algebraic.Integral

/-! The trace on the exterior algebra of a finite étale function-field extension. -/

noncomputable section

open GlobalTheory.SchemeCohomology
open scoped DirectSum GlobalTheory.CechDR GlobalTheory.SchemeCohomology

namespace GlobalTheory.CechDR

variable (k E L : Type*) [Field k] [Field E] [Field L]
  [Algebra k E] [Algebra k L] [Algebra E L] [IsScalarTower k E L]
  [Module.Finite E L] [Algebra.Etale E L]

private def traceDegree (p : ℕ) :
    ExteriorDifferentials k L p →ₗ[k] DR k E where
  toFun ω := finiteEtaleFormTrace k E L p ω
  map_add' ω η := congrArg Subtype.val ((finiteEtaleFormTrace k E L p).map_add ω η)
  map_smul' c ω := by
    change ((finiteEtaleFormTrace k E L p (c • ω) :
      ExteriorDifferentials k E p) : DR k E) = _
    have hs : c • ω = algebraMap k E c • ω := by
      rw [← IsScalarTower.algebraMap_smul L c ω,
        ← IsScalarTower.algebraMap_smul L (algebraMap k E c) ω,
        IsScalarTower.algebraMap_apply k E]
    rw [hs, map_smul, Submodule.coe_smul_of_tower,
      IsScalarTower.algebraMap_smul E]
    rfl

/-- Trace acts degree by degree by the finite étale trace of forms. -/
def traceDR : DR k L →ₗ[k] DR k E :=
  (DirectSum.toModule k ℕ (DR k E) (traceDegree k E L)).comp
    ((DirectSum.decomposeLinearEquiv (fun p => ⋀[L]^p Ω[L⁄k])).restrictScalars k).toLinearMap

@[simp] theorem traceDR_degree (p : ℕ) (ω : ExteriorDifferentials k L p) :
    traceDR k E L (ω : DR k L) = (finiteEtaleFormTrace k E L p ω : DR k E) := by
  change DirectSum.toModule k ℕ (DR k E) (traceDegree k E L)
    (DirectSum.decompose (fun p => ⋀[L]^p Ω[L⁄k]) (ω : DR k L)) = _
  rw [DirectSum.decompose_coe]
  exact DirectSum.toModule_lof (M := fun j => ExteriorDifferentials k L j)
    (φ := traceDegree k E L) k p ω

end GlobalTheory.CechDR

namespace GlobalTheory.SchemeCohomology

variable {A B E L : Type*} [CommRing A] [CommRing B] [IsDomain B] [Field E] [Field L]
  [Algebra A B] [Algebra A E] [Algebra A L] [Algebra B L] [Algebra E L]
  [IsScalarTower A B L] [IsScalarTower A E L] [IsFractionRing A E] [IsFractionRing B L]
  [Module.Finite A B]

/-- A finite inclusion of domains induces the base-change square on fraction fields. -/
theorem fractionFields_isPushout (hinj : Function.Injective (algebraMap A B)) :
    Algebra.IsPushout A E B L := by
  letI : Nontrivial A := (algebraMap A B).domain_nontrivial
  letI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  infer_instance

end GlobalTheory.SchemeCohomology
