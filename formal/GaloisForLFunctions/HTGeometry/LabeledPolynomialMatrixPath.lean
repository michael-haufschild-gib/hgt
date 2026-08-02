import GaloisForLFunctions.HTGeometry.PolynomialMatrixSimpleSpectrumTransport
import Mathlib.Topology.Path

/-!
# Labelled simple-spectrum paths form a groupoid

This file packages a parameter path together with a complete, injective
characteristic-root path for every label.  Reversal, concatenation, and label
permutation preserve the certificate.  The construction makes common-base
monodromy arguments literal: no unnamed conjugating permutation can enter.
-/

open Topology unitInterval

namespace GaloisForLFunctions.HTGeometry

structure LabeledPolynomialMatrixPath
    {θ J : Type*} [Fintype J] [DecidableEq J]
    (M : Matrix J J (MvPolynomial θ ℂ))
    (p q : θ → ℂ) (rootP rootQ : J → ℂ) where
  parameterPath : Path p q
  rootPath : ∀ x, Path (rootP x) (rootQ x)
  root_is :
    ∀ x s,
      (M.map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ)
          (parameterPath s))).charpoly.eval
        (rootPath x s) = 0
  root_injective :
    ∀ s, Function.Injective fun x => rootPath x s

namespace LabeledPolynomialMatrixPath

variable {θ J : Type*} [Fintype J] [DecidableEq J]
  {M : Matrix J J (MvPolynomial θ ℂ)}
  {p q r : θ → ℂ}
  {rootP rootQ rootR : J → ℂ}

noncomputable def symm
    (P : LabeledPolynomialMatrixPath M p q rootP rootQ) :
    LabeledPolynomialMatrixPath M q p rootQ rootP where
  parameterPath := P.parameterPath.symm
  rootPath x := (P.rootPath x).symm
  root_is x s := by
    simpa [Path.symm_apply, Function.comp_apply] using
      P.root_is x (unitInterval.symm s)
  root_injective s := by
    simpa [Path.symm_apply, Function.comp_apply] using
      P.root_injective (unitInterval.symm s)

noncomputable def trans
    (P : LabeledPolynomialMatrixPath M p q rootP rootQ)
    (Q : LabeledPolynomialMatrixPath M q r rootQ rootR) :
    LabeledPolynomialMatrixPath M p r rootP rootR where
  parameterPath := P.parameterPath.trans Q.parameterPath
  rootPath x := (P.rootPath x).trans (Q.rootPath x)
  root_is x s := by
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs
    · exact P.root_is _ _
    · exact Q.root_is _ _
  root_injective s := by
    intro x y hxy
    change
      ((P.rootPath x).trans (Q.rootPath x)) s =
        ((P.rootPath y).trans (Q.rootPath y)) s at hxy
    rw [Path.trans_apply, Path.trans_apply] at hxy
    split_ifs at hxy
    · exact P.root_injective _ hxy
    · exact Q.root_injective _ hxy

noncomputable def relabel
    (P : LabeledPolynomialMatrixPath M p q rootP rootQ)
    (e : J ≃ J) :
    LabeledPolynomialMatrixPath M p q
      (rootP ∘ e) (rootQ ∘ e) where
  parameterPath := P.parameterPath
  rootPath x := P.rootPath (e x)
  root_is x := P.root_is (e x)
  root_injective s := (P.root_injective s).comp e.injective

/-- Every labelled simple-spectrum path stays in the nonzero characteristic
resultant locus. -/
theorem resultant_ne_zero
    (P : LabeledPolynomialMatrixPath M p q rootP rootQ)
    (s : I) :
    MvPolynomial.eval (P.parameterPath s)
      (matrixCharacteristicResultantPolynomial M) ≠ 0 := by
  change
    (MvPolynomial.eval₂Hom (RingHom.id ℂ)
      (P.parameterPath s))
      (matrixCharacteristicResultantPolynomial M) ≠ 0
  rw [eval_matrixCharacteristicResultantPolynomial]
  exact
    matrixCharacteristicResultant_ne_zero_of_complete_injective_roots
      _
      (fun x => P.rootPath x s)
      (P.root_injective s)
      (P.root_is · s)

end LabeledPolynomialMatrixPath

end GaloisForLFunctions.HTGeometry
