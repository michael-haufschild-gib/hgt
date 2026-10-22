import GaloisForLFunctions.RHTower.Schanuel.SchanuelDefectAlgebraicIndependence
import GaloisForLFunctions.HTGeometry.AlgebraicClosureDerivationClosed

/-!
# Algebraic exclusion for Schanuel defect slopes

Algebraic-coefficient independence rules out every slope algebraic over the algebraic numbers, not
only rational slopes.  This is the transcendence clause in the stage-two defect-slope normal form.
-/

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- A scalar relating the two defects of a rationally independent pair is transcendental over the
algebraic closure of `ℚ` in `ℂ`. -/
theorem schanuelDefect_slope_transcendental_algebraicClosure
    (x : Fin 2 → ℂ) (hx : LinearIndependent ℚ x) (rho : ℂ)
    (hslope : schanuelDefect (x 1) = rho • schanuelDefect (x 0)) :
    Transcendental (algebraicClosure ℚ ℂ) rho := by
  intro halg
  let a : algebraicClosure ℚ ℂ :=
    ⟨rho, mem_algebraicClosure_of_isAlgebraic halg⟩
  let c : Fin 2 → algebraicClosure ℚ ℂ := ![-a, 1]
  have hsum : ∑ i, c i • schanuelDefect (x i) = 0 := by
    rw [Fin.sum_univ_two]
    simp only [c, Matrix.cons_val_zero, neg_smul, Matrix.cons_val_one, one_smul]
    rw [hslope]
    have harho : (a : ℂ) = rho := rfl
    rw [← harho]
    have hsmul : (a : ℂ) • schanuelDefect (x 0) =
        a • schanuelDefect (x 0) :=
      IsScalarTower.algebraMap_smul ℂ a _
    rw [hsmul]
    simp
  have hc := schanuelDefect_algebraic_relation x hx c hsum
  have hc1 := congrFun hc 1
  norm_num [c] at hc1

end

end GaloisForLFunctions.RHTower
