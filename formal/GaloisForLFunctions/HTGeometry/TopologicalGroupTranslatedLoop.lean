import GaloisForLFunctions.HTGeometry.FundamentalGroupTopologicalGroup

/-!
# Basepoint transport of translated loops in a topological group

A loop at the identity can be translated to a loop at an arbitrary group element.  Conjugating
that translated loop by any path from the identity to the new basepoint recovers the original
fundamental-group class.  This is the basepoint-independence needed when a divisor meridian is
connected back to a fixed source sheet by an otherwise uncontrolled path.
-/

namespace GaloisForLFunctions.HTGeometry

open Path

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Left-translate a loop based at the identity to a loop based at `u`. -/
def translatedLoopPath (u : G) (g : Path (1 : G) 1) : Path u u where
  toFun t := u * g t
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

private def pathMulOneRight {a b : G} (p : Path a b) : Path a b where
  toFun t := p t * 1
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

private theorem conjugate_translatedLoopPath_mk_aux
    {u : G} (alpha : Path (1 : G) u) (g : Path (1 : G) 1) :
    Path.Homotopic.Quotient.mk
        ((pathMulOneRight alpha).trans
          ((translatedLoopPath u g).trans (pathMulOneRight alpha.symm))) =
      Path.Homotopic.Quotient.mk g := by
  let P : Path (1 : G) 1 := alpha.trans ((Path.refl u).trans alpha.symm)
  let Q : Path (1 : G) 1 := (Path.refl 1).trans (g.trans (Path.refl 1))
  have hpath :
      (pathMulOneRight alpha).trans
          ((translatedLoopPath u g).trans (pathMulOneRight alpha.symm)) =
        loopPointwiseMulPath P Q := by
    apply Path.ext
    funext t
    simp only [pathMulOneRight, translatedLoopPath, loopPointwiseMulPath,
      Path.trans_apply, Path.coe_mk_mk, P, Q, Path.refl_apply]
    split_ifs <;> simp
  rw [hpath, ← fundamentalGroupPointwiseMul_mk]
  have hP : Path.Homotopic.Quotient.mk P =
      Path.Homotopic.Quotient.mk (Path.refl (1 : G)) := by
    simp [P]
  have hQ : Path.Homotopic.Quotient.mk Q = Path.Homotopic.Quotient.mk g := by
    simp [Q]
  rw [hP, hQ, fundamentalGroupPointwiseMul_mk]
  apply congrArg Path.Homotopic.Quotient.mk
  apply Path.ext
  funext t
  simp [loopPointwiseMulPath]

/-- **Translated-loop basepoint transport.**  For any connector from the identity to `u`, the
connector-conjugate of the left-translated loop represents the original identity-based class. -/
theorem conjugate_translatedLoopPath_mk
    {u : G} (alpha : Path (1 : G) u) (g : Path (1 : G) 1) :
    Path.Homotopic.Quotient.mk
        (alpha.trans ((translatedLoopPath u g).trans alpha.symm)) =
      Path.Homotopic.Quotient.mk g := by
  have hpath :
      alpha.trans ((translatedLoopPath u g).trans alpha.symm) =
        (pathMulOneRight alpha).trans
          ((translatedLoopPath u g).trans (pathMulOneRight alpha.symm)) := by
    apply Path.ext
    funext t
    simp only [pathMulOneRight, translatedLoopPath, Path.trans_apply,
      Path.symm_apply, Path.coe_mk_mk]
    split_ifs <;> simp
  rw [hpath]
  exact conjugate_translatedLoopPath_mk_aux alpha g

end GaloisForLFunctions.HTGeometry
