import GaloisForLFunctions.HTGeometry.QuadraticRootFieldEquiv

/-!
# Conjugation on an actual quadratic root field

The power-basis equivalence between the roots `r` and `-r` gives the canonical
base-field automorphism of `F(r)`. Its action on the generator and its square
are proved on this intermediate field, without choosing another presentation.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open scoped IntermediateField
variable {F L M : Type*} [Field F] [Field L] [Field M] [Algebra F L] [Algebra F M]

theorem quadraticRootFieldEquiv_gen {c : F} {r : L} {s : M}
    (hr : r * r = algebraMap F L c) (hs : s * s = algebraMap F M c)
    (hc : ¬ IsSquare c) :
    quadraticRootFieldEquiv hr hs hc
      ⟨r, IntermediateField.mem_adjoin_simple_self F r⟩ =
        ⟨s, IntermediateField.mem_adjoin_simple_self F s⟩ := by
  exact PowerBasis.equivOfMinpoly_gen _ _ _

theorem adjoin_neg_root (r : L) : F⟮-r⟯ = F⟮r⟯ := by
  apply le_antisymm
  · apply IntermediateField.adjoin_simple_le_iff.mpr
    exact IntermediateField.neg_mem _ (IntermediateField.mem_adjoin_simple_self F r)
  · apply IntermediateField.adjoin_simple_le_iff.mpr
    simpa only [neg_neg] using
      IntermediateField.neg_mem F⟮-r⟯ (IntermediateField.mem_adjoin_simple_self F (-r))

def quadraticRootConjugation {c : F} {r : L}
    (hr : r * r = algebraMap F L c) (hc : ¬ IsSquare c) : F⟮r⟯ ≃ₐ[F] F⟮r⟯ :=
  (quadraticRootFieldEquiv hr (by simpa only [neg_mul_neg] using hr) hc).trans
    (IntermediateField.equivOfEq (adjoin_neg_root r))

theorem quadraticRootConjugation_gen {c : F} {r : L}
    (hr : r * r = algebraMap F L c) (hc : ¬ IsSquare c) :
    quadraticRootConjugation hr hc ⟨r, IntermediateField.mem_adjoin_simple_self F r⟩ =
      -⟨r, IntermediateField.mem_adjoin_simple_self F r⟩ := by
  unfold quadraticRootConjugation
  rw [AlgEquiv.trans_apply, quadraticRootFieldEquiv_gen]
  rfl

theorem quadraticRootConjugation_involutive {c : F} {r : L}
    (hr : r * r = algebraMap F L c) (hc : ¬ IsSquare c) :
    Function.Involutive (quadraticRootConjugation hr hc) := by
  let e := quadraticRootConjugation hr hc
  have he : e.toAlgHom.comp e.toAlgHom = AlgHom.id F F⟮r⟯ := by
    apply (IntermediateField.adjoin.powerBasis (isIntegral_of_sq_mem_bot hr)).algHom_ext
    change e (e ⟨r, IntermediateField.mem_adjoin_simple_self F r⟩) =
      ⟨r, IntermediateField.mem_adjoin_simple_self F r⟩
    simp only [e, quadraticRootConjugation_gen, map_neg, neg_neg]
  intro x
  exact congrArg (fun f : F⟮r⟯ →ₐ[F] F⟮r⟯ => f x) he

end GaloisForLFunctions.HTGeometry
