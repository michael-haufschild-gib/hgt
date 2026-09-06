import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicGradedLine
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# The Hilbert sum of actual homogeneous observation defects

Each summand has its attained physical quotient norm. The resulting complete
inner product space has explicit weighted coefficient formulas. Single-grade
inclusions preserve those norms, distinct grades are orthogonal, and the sum
of a vector's grade components converges to the vector.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial

attribute [local instance] cubicGradedLineNormedGroup cubicGradedLineInnerProductSpace
  cubicGradedLine_complete


@[reducible]
def cubicDefectHilbert : Type := lp cubicGradedDefect 2

theorem cubicDefectHilbert_complete : CompleteSpace cubicDefectHilbert := inferInstance

theorem cubicDefectHilbert_inner (x y : cubicDefectHilbert) :
    inner ℝ x y = ∑' k, (cubicGradedRecoveryGap k)^2 *
      cubicGradedDefectCoordinate k (x k) * cubicGradedDefectCoordinate k (y k) := by
  rw [lp.inner_eq_tsum]
  congr 1
  funext k
  exact cubicGradedLine_inner k (x k) (y k)

theorem cubicDefectHilbert_norm_sq (x : cubicDefectHilbert) :
    ‖x‖^2=∑' k, (cubicGradedRecoveryGap k)^2 *
      (cubicGradedDefectCoordinate k (x k))^2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℝ)]
  change inner ℝ x x = _
  rw [cubicDefectHilbert_inner]
  congr 1
  funext k
  ring

def cubicDefectHilbertSingle (k : ℕ) (x : cubicGradedDefect k) : cubicDefectHilbert :=
  lp.single 2 k x

theorem cubicDefectHilbertSingle_norm (k : ℕ) (x : cubicGradedDefect k) :
    ‖cubicDefectHilbertSingle k x‖=cubicGradedDefectNorm k x := by
  rw [cubicDefectHilbertSingle,lp.norm_single (by positivity),cubicGradedLine_norm]

theorem cubicDefectHilbertSingle_injective (k : ℕ) :
    Function.Injective (cubicDefectHilbertSingle k) :=
  (lp.isometry_single (E := cubicGradedDefect) (p := 2) k).injective

theorem cubicDefectHilbertSingle_inner (i j : ℕ) (x : cubicGradedDefect i)
    (y : cubicGradedDefect j) :
    i≠j → inner ℝ (cubicDefectHilbertSingle i x) (cubicDefectHilbertSingle j y)=0 := by
  intro hij
  change inner ℝ (lp.single 2 i x) (lp.single 2 j y)=0
  rw [lp.inner_single_left,lp.single_apply_ne 2 j y hij]
  exact inner_zero_right x

theorem cubicDefectHilbert_hasSum (x : cubicDefectHilbert) :
    HasSum (fun k => cubicDefectHilbertSingle k (x k)) x :=
  lp.hasSum_single (by simp) x

theorem cubicDefectHilbertSingle_observation (k : ℕ) (P : cubicHomogeneousSpace (k+1)) :
    ‖cubicDefectHilbertSingle k (cubicGradedDefectMk k P)‖=
      |cubicGradedCoefficient k P| * cubicGradedRecoveryGap k := by
  rw [cubicDefectHilbertSingle_norm,cubicGradedDefectNorm_eq,
    cubicGradedDefectCoordinate_mk]

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
