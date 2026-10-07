import GaloisForLFunctions.HTGeometry.QuadraticRootFieldEquiv

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open Polynomial
open scoped IntermediateField
variable {F L : Type*} [Field F] [Field L] [Algebra F L]
variable {c : F} {r : L} (hr : r * r = algebraMap F L c) (hc : ¬ IsSquare c)
variable (e : F ≃+* F) (he : e c = c)

include hr hc he in
private theorem minpoly_map_of_fixed_radicand :
    (minpoly F r).map e = minpoly F r := by
  rw [minpoly_of_root_nonsquare hr hc]
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  exact congrArg (fun a : F => X ^ 2 - C a) he

/-- A base automorphism fixing a nonsquare radicand lifts while fixing its root. -/
def quadraticSemilinearEquiv : F⟮r⟯ ≃+* F⟮r⟯ :=
  let q := IntermediateField.adjoinRootEquivAdjoin F (isIntegral_of_sq_mem_bot hr)
  q.symm.toRingEquiv.trans ((AdjoinRoot.mapRingEquiv e (minpoly F r) (minpoly F r)
    (by rw [minpoly_map_of_fixed_radicand hr hc e he])).trans q.toRingEquiv)

theorem quadraticSemilinearEquiv_base (a : F) :
    quadraticSemilinearEquiv hr hc e he (algebraMap F F⟮r⟯ a) =
      algebraMap F F⟮r⟯ (e a) := by
  unfold quadraticSemilinearEquiv
  simp only [RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv,
    AlgEquiv.commutes, AdjoinRoot.coe_mapRingEquiv, AdjoinRoot.algebraMap_eq,
    AdjoinRoot.map_of]
  exact (IntermediateField.adjoinRootEquivAdjoin F
    (isIntegral_of_sq_mem_bot hr)).commutes (e a)

theorem quadraticSemilinearEquiv_gen :
    quadraticSemilinearEquiv hr hc e he (IntermediateField.AdjoinSimple.gen F r) =
      IntermediateField.AdjoinSimple.gen F r := by
  unfold quadraticSemilinearEquiv
  simp only [RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv,
    IntermediateField.adjoinRootEquivAdjoin_symm_apply_gen,
    AdjoinRoot.coe_mapRingEquiv, AdjoinRoot.map_root,
    IntermediateField.adjoinRootEquivAdjoin_apply_root]

theorem quadraticSemilinearEquiv_involutive (hinv : Function.Involutive e) :
    Function.Involutive (quadraticSemilinearEquiv hr hc e he) := by
  let σ := quadraticSemilinearEquiv hr hc e he
  let τ : F⟮r⟯ →ₐ[F] F⟮r⟯ :=
    { __ := σ.toRingHom.comp σ.toRingHom
      commutes' a := by
        change σ (σ (algebraMap F F⟮r⟯ a)) = algebraMap F F⟮r⟯ a
        simp only [σ, quadraticSemilinearEquiv_base, hinv a] }
  have hτ : τ = AlgHom.id F F⟮r⟯ := by
    apply (IntermediateField.adjoin.powerBasis (isIntegral_of_sq_mem_bot hr)).algHom_ext
    change σ (σ (IntermediateField.AdjoinSimple.gen F r)) =
      IntermediateField.AdjoinSimple.gen F r
    simp only [σ, quadraticSemilinearEquiv_gen]
  intro x
  exact congrArg (fun f : F⟮r⟯ →ₐ[F] F⟮r⟯ => f x) hτ

end GaloisForLFunctions.HTGeometry
