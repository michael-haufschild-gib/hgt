import GaloisForLFunctions.HTGeometry.JetGermPolyGrowth
import GaloisForLFunctions.HTGeometry.JetPolynomialShift

/-!
# The unit shift on jet polynomial germs

The polynomial shift endomorphism of `JetPolynomialShift` induces the unit shift on the germ
evaluation as well as on the meromorphic-field evaluation.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

local instance jetShiftGermRatFuncAlgebra : Algebra (RatFunc ℂ) (Germ upperEndFilter ℂ) :=
  ratFuncGerm.toAlgebra

variable {r : ℕ}

/-- **The polynomial shift induces the unit shift on jet germs.** -/
theorem upperEndTranslateGerm_shiftedJetEval (lam : Fin r → ℝ) {M : ℕ}
    (idx : Fin M → Fin r × ℕ) (P : MvPolynomial (Fin M) (RatFunc ℂ)) :
    upperEndTranslateGerm 1 (shiftedJetEval lam idx P)
      = shiftedJetEval lam idx
          (jetShiftPoly
            (fun k => familyIncrement (fun i => ((lam i : ℝ) : ℂ)) (idx k).1 (idx k).2) P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a =>
      rw [shiftedJetEval, MvPolynomial.eval₂_C, jetShiftPoly_C, shiftedJetEval,
        MvPolynomial.eval₂_C]
      exact upperEndTranslateGerm_ratFuncGerm a
  | add p q hp hq =>
      have hL : upperEndTranslateGerm 1 (shiftedJetEval lam idx (p + q))
          = upperEndTranslateGerm 1 (shiftedJetEval lam idx p)
            + upperEndTranslateGerm 1 (shiftedJetEval lam idx q) := by
        rw [shiftedJetEval, MvPolynomial.eval₂_add, ← shiftedJetEval, ← shiftedJetEval, map_add]
      have hR : shiftedJetEval lam idx
            (jetShiftPoly
              (fun k => familyIncrement (fun i => ((lam i : ℝ) : ℂ)) (idx k).1 (idx k).2) (p + q))
          = shiftedJetEval lam idx
              (jetShiftPoly
                (fun k => familyIncrement (fun i => ((lam i : ℝ) : ℂ)) (idx k).1 (idx k).2) p)
            + shiftedJetEval lam idx
              (jetShiftPoly
                (fun k => familyIncrement (fun i => ((lam i : ℝ) : ℂ)) (idx k).1 (idx k).2) q) := by
        rw [map_add, shiftedJetEval, MvPolynomial.eval₂_add, ← shiftedJetEval, ← shiftedJetEval]
      rw [hL, hR, hp, hq]
  | mul_X p k hp =>
      have hL : upperEndTranslateGerm 1 (shiftedJetEval lam idx (p * MvPolynomial.X k))
          = upperEndTranslateGerm 1 (shiftedJetEval lam idx p)
            * (jetGerm lam (idx k)
              + ratFuncGerm (familyIncrement (fun i => ((lam i : ℝ) : ℂ)) (idx k).1 (idx k).2)) := by
        rw [shiftedJetEval, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, ← shiftedJetEval,
          map_mul, upperEndTranslateGerm_jetGerm]
      have hR : shiftedJetEval lam idx
            (jetShiftPoly
              (fun k => familyIncrement (fun i => ((lam i : ℝ) : ℂ)) (idx k).1 (idx k).2)
              (p * MvPolynomial.X k))
          = shiftedJetEval lam idx
              (jetShiftPoly
                (fun k => familyIncrement (fun i => ((lam i : ℝ) : ℂ)) (idx k).1 (idx k).2) p)
            * (jetGerm lam (idx k)
              + ratFuncGerm (familyIncrement (fun i => ((lam i : ℝ) : ℂ)) (idx k).1 (idx k).2)) := by
        rw [map_mul, jetShiftPoly_X, shiftedJetEval, MvPolynomial.eval₂_mul,
          MvPolynomial.eval₂_add, MvPolynomial.eval₂_X, MvPolynomial.eval₂_C, ← shiftedJetEval]
        rfl
      rw [hL, hR, hp]

end

end GaloisForLFunctions.HTGeometry
