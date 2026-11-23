import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FiniteEtaleFormTrace

/-! Trace of differentials commutes with base change of a finite étale algebra. -/

noncomputable section

open TensorProduct

namespace GlobalTheory.SchemeCohomology

variable {k A B E L : Type*} [CommRing k] [CommRing A] [CommRing B] [CommRing E] [CommRing L]
  [Algebra k A] [Algebra k B] [Algebra k E] [Algebra k L]
  [Algebra A B] [Algebra A E] [Algebra A L] [Algebra B L] [Algebra E L]
  [IsScalarTower k A B] [IsScalarTower k A E]
  [IsScalarTower k B L] [IsScalarTower k E L]
  [IsScalarTower A B L] [IsScalarTower A E L]

private theorem algebraFormPullback_comm (p : ℕ) (ω : ExteriorDifferentials k A p) :
    algebraFormPullback k B L p (algebraFormPullback k A B p ω) =
      algebraFormPullback k E L p (algebraFormPullback k A E p ω) := by
  let f := IsScalarTower.toAlgHom k A B
  let g := IsScalarTower.toAlgHom k B L
  let f' := IsScalarTower.toAlgHom k A E
  let g' := IsScalarTower.toAlgHom k E L
  have h : g.comp f = g'.comp f' := AlgHom.ext fun a =>
    (IsScalarTower.algebraMap_apply A B L a).symm.trans (IsScalarTower.algebraMap_apply A E L a)
  rw [algebraFormPullback_eq_map k B L g rfl, algebraFormPullback_eq_map k A B f rfl,
    algebraFormPullback_eq_map k E L g' rfl, algebraFormPullback_eq_map k A E f' rfl,
    ← ExteriorDifferentials.map_comp, ← ExteriorDifferentials.map_comp, h]

variable [Module.Finite A B] [Algebra.Etale A B] [Module.Finite E L] [Algebra.Etale E L]
  [Algebra.IsPushout A E B L]

/-- Extending a form and then tracing gives the extension of its trace. -/
theorem finiteEtaleFormTrace_baseChange (p : ℕ) (η : ExteriorDifferentials k B p) :
    finiteEtaleFormTrace k E L p (algebraFormPullback k B L p η) =
      algebraFormPullback k A E p (finiteEtaleFormTrace k A B p η) := by
  let e := (algebraFormPullback_isBaseChange k A B p).equiv
  obtain ⟨ξ, rfl⟩ := e.surjective η
  induction ξ using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b ω =>
    rw [show e (b ⊗ₜ[A] ω) = b • algebraFormPullback k A B p ω from
      (algebraFormPullback_isBaseChange k A B p).equiv_tmul b ω]
    rw [map_smul, ← IsScalarTower.algebraMap_smul L b,
      algebraFormPullback_comm (k := k) (A := A) (B := B) (E := E) (L := L) p ω,
      finiteEtaleFormTrace_smul_pullback, finiteEtaleFormTrace_smul_pullback,
      finiteEtaleAlgebraTrace_baseChange (S := E) (C := L) A B b, map_smul,
      IsScalarTower.algebraMap_smul E]

end GlobalTheory.SchemeCohomology
