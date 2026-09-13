import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic.Abel
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Small quadratic correction solver

This module formalizes the contraction-mapping core of Lemma A.2 in the
Navier–Stokes paper.  An invertible linear response plus a bounded bilinear
remainder has a unique small solution under the paper's constant `8`
smallness condition.
-/

open Set

namespace GaloisForLFunctions.HTGeometry.NavierStokesQuadraticCorrection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Fixed-point map obtained by applying the inverse linear response. -/
noncomputable def correctionMap (B : E ≃L[ℝ] E) (Q : E →L[ℝ] E →L[ℝ] E) (d c : E) : E :=
  B.symm (d - Q c c)

/-- Radius used in Lemma A.2. -/
noncomputable def correctionRadius (B : E ≃L[ℝ] E) (d : E) : ℝ :=
  2 * ‖B.symm.toContinuousLinearMap‖ * ‖d‖

omit [CompleteSpace E] in
private theorem bilinear_norm_le (Q : E →L[ℝ] E →L[ℝ] E) (x y : E) :
    ‖Q x y‖ ≤ ‖Q‖ * ‖x‖ * ‖y‖ := by
  calc
    ‖Q x y‖ ≤ ‖Q x‖ * ‖y‖ := (Q x).le_opNorm y
    _ ≤ (‖Q‖ * ‖x‖) * ‖y‖ := by
      gcongr
      exact Q.le_opNorm x

omit [CompleteSpace E] in
private theorem bilinear_diagonal_sub (Q : E →L[ℝ] E →L[ℝ] E) (x y : E) :
    Q x x - Q y y = Q x (x - y) + Q (x - y) y := by
  calc
    Q x x - Q y y = (Q x x - Q x y) + (Q x y - Q y y) := by abel
    _ = Q x (x - y) + Q (x - y) y := by simp

omit [CompleteSpace E] in
private theorem correctionMap_norm_le
    (B : E ≃L[ℝ] E) (Q : E →L[ℝ] E →L[ℝ] E) (d c : E) :
    ‖correctionMap B Q d c‖ ≤
      ‖B.symm.toContinuousLinearMap‖ * (‖d‖ + ‖Q‖ * ‖c‖ * ‖c‖) := by
  calc
    ‖correctionMap B Q d c‖ ≤ ‖B.symm.toContinuousLinearMap‖ * ‖d - Q c c‖ :=
      B.symm.toContinuousLinearMap.le_opNorm _
    _ ≤ ‖B.symm.toContinuousLinearMap‖ * (‖d‖ + ‖Q c c‖) := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ ‖B.symm.toContinuousLinearMap‖ * (‖d‖ + ‖Q‖ * ‖c‖ * ‖c‖) := by
      gcongr
      exact bilinear_norm_le Q c c

omit [CompleteSpace E] in
private theorem correctionMap_sub_norm_le
    (B : E ≃L[ℝ] E) (Q : E →L[ℝ] E →L[ℝ] E) (d x y : E) :
    ‖correctionMap B Q d x - correctionMap B Q d y‖ ≤
      ‖B.symm.toContinuousLinearMap‖ * ‖Q‖ * (‖x‖ + ‖y‖) * ‖x - y‖ := by
  calc
    ‖correctionMap B Q d x - correctionMap B Q d y‖ =
        ‖B.symm (Q y y - Q x x)‖ := by
          simp only [correctionMap, ← map_sub]
          congr 2
          abel
    _ ≤ ‖B.symm.toContinuousLinearMap‖ * ‖Q y y - Q x x‖ :=
      B.symm.toContinuousLinearMap.le_opNorm _
    _ = ‖B.symm.toContinuousLinearMap‖ * ‖Q x x - Q y y‖ := by rw [norm_sub_rev]
    _ = ‖B.symm.toContinuousLinearMap‖ * ‖Q x (x - y) + Q (x - y) y‖ := by
      rw [bilinear_diagonal_sub]
    _ ≤ ‖B.symm.toContinuousLinearMap‖ *
        (‖Q x (x - y)‖ + ‖Q (x - y) y‖) := by
      gcongr
      exact norm_add_le _ _
    _ ≤ ‖B.symm.toContinuousLinearMap‖ *
        ((‖Q‖ * ‖x‖ * ‖x - y‖) + (‖Q‖ * ‖x - y‖ * ‖y‖)) := by
      have hx := bilinear_norm_le Q x (x - y)
      have hy := bilinear_norm_le Q (x - y) y
      gcongr
    _ = ‖B.symm.toContinuousLinearMap‖ * ‖Q‖ * (‖x‖ + ‖y‖) * ‖x - y‖ := by ring

omit [CompleteSpace E] in
/-- The paper's smallness condition makes the correction map preserve its prescribed ball. -/
theorem correctionMap_mapsTo_closedBall
    (B : E ≃L[ℝ] E) (Q : E →L[ℝ] E →L[ℝ] E) (d : E)
    (hsmall : 8 * ‖B.symm.toContinuousLinearMap‖ ^ 2 * ‖Q‖ * ‖d‖ ≤ 1) :
    MapsTo (correctionMap B Q d)
      (Metric.closedBall 0 (correctionRadius B d))
      (Metric.closedBall 0 (correctionRadius B d)) := by
  intro c hc
  rw [Metric.mem_closedBall, dist_zero_right] at hc ⊢
  have hβ : 0 ≤ ‖B.symm.toContinuousLinearMap‖ := norm_nonneg _
  have hκ : 0 ≤ ‖Q‖ := Q.opNorm_nonneg
  have hd : 0 ≤ ‖d‖ := norm_nonneg _
  have hc' : ‖c‖ ≤ 2 * ‖B.symm.toContinuousLinearMap‖ * ‖d‖ := by
    simpa [correctionRadius] using hc
  have hscaled := mul_le_mul_of_nonneg_right hsmall (mul_nonneg hβ hd)
  have hquadratic :
      ‖B.symm.toContinuousLinearMap‖ * ‖Q‖ *
          (2 * ‖B.symm.toContinuousLinearMap‖ * ‖d‖) ^ 2 ≤
        ‖B.symm.toContinuousLinearMap‖ * ‖d‖ := by
    nlinarith
  calc
    ‖correctionMap B Q d c‖ ≤
        ‖B.symm.toContinuousLinearMap‖ * (‖d‖ + ‖Q‖ * ‖c‖ * ‖c‖) :=
      correctionMap_norm_le B Q d c
    _ ≤ ‖B.symm.toContinuousLinearMap‖ *
        (‖d‖ + ‖Q‖ * (2 * ‖B.symm.toContinuousLinearMap‖ * ‖d‖) *
          (2 * ‖B.symm.toContinuousLinearMap‖ * ‖d‖)) := by
      gcongr
    _ ≤ 2 * ‖B.symm.toContinuousLinearMap‖ * ‖d‖ := by nlinarith
    _ = correctionRadius B d := by rw [correctionRadius]

omit [CompleteSpace E] in
/-- On the prescribed ball, the correction map has Lipschitz constant `1/2`. -/
theorem correctionMap_lipschitzOnWith_half
    (B : E ≃L[ℝ] E) (Q : E →L[ℝ] E →L[ℝ] E) (d : E)
    (hsmall : 8 * ‖B.symm.toContinuousLinearMap‖ ^ 2 * ‖Q‖ * ‖d‖ ≤ 1) :
    LipschitzOnWith (1 / 2 : NNReal) (correctionMap B Q d)
      (Metric.closedBall 0 (correctionRadius B d)) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  rw [Metric.mem_closedBall, dist_zero_right] at hx hy
  have hβ : 0 ≤ ‖B.symm.toContinuousLinearMap‖ := norm_nonneg _
  have hκ : 0 ≤ ‖Q‖ := Q.opNorm_nonneg
  have hd : 0 ≤ ‖d‖ := norm_nonneg _
  have hr : 0 ≤ correctionRadius B d := by
    simp [correctionRadius, mul_nonneg]
  have hcoef :
      ‖B.symm.toContinuousLinearMap‖ * ‖Q‖ *
        (correctionRadius B d + correctionRadius B d) ≤ 1 / 2 := by
    dsimp [correctionRadius]
    nlinarith
  have hnorm := correctionMap_sub_norm_le B Q d x y
  rw [dist_eq_norm, dist_eq_norm]
  calc
    ‖correctionMap B Q d x - correctionMap B Q d y‖ ≤
        ‖B.symm.toContinuousLinearMap‖ * ‖Q‖ * (‖x‖ + ‖y‖) * ‖x - y‖ := hnorm
    _ ≤ (‖B.symm.toContinuousLinearMap‖ * ‖Q‖ *
        (correctionRadius B d + correctionRadius B d)) * ‖x - y‖ := by
      gcongr
    _ ≤ (1 / 2 : ℝ) * ‖x - y‖ := by gcongr
    _ = ((1 / 2 : NNReal) : ℝ) * ‖x - y‖ := by norm_num

/--
Contraction core of Lemma A.2: the quadratic moment equation has exactly one solution
in the ball of radius `2 ‖B⁻¹‖ ‖d‖`, and iteration from zero converges to it.
-/
theorem existsUnique_quadratic_correction
    (B : E ≃L[ℝ] E) (Q : E →L[ℝ] E →L[ℝ] E) (d : E)
    (hsmall : 8 * ‖B.symm.toContinuousLinearMap‖ ^ 2 * ‖Q‖ * ‖d‖ ≤ 1) :
    ∃! c : E,
      ‖c‖ ≤ correctionRadius B d ∧ B c + Q c c = d := by
  let ball := Metric.closedBall (0 : E) (correctionRadius B d)
  let T := correctionMap B Q d
  have hmaps : MapsTo T ball ball := correctionMap_mapsTo_closedBall B Q d hsmall
  have hlip : LipschitzOnWith (1 / 2 : NNReal) T ball :=
    correctionMap_lipschitzOnWith_half B Q d hsmall
  have hzero : (0 : E) ∈ ball := by
    simp [ball, correctionRadius, mul_nonneg]
  have hcontr : ContractingWith (1 / 2 : NNReal) (hmaps.restrict T ball ball) := by
    refine ⟨by norm_num, ?_⟩
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simpa [Set.MapsTo.restrict, Subtype.dist_eq] using hlip.dist_le_mul x x.2 y y.2
  have hcomplete : IsComplete ball := Metric.isClosed_closedBall.isComplete
  obtain ⟨c, hc, hfix, _htend, _hest⟩ :=
    hcontr.exists_fixedPoint' hcomplete hmaps hzero (edist_ne_top 0 (T 0))
  have hlinear : d - Q c c = B c := by
    simpa [T, correctionMap] using congrArg B hfix
  have heq : B c + Q c c = d := by
    rw [← hlinear]
    abel
  refine ⟨c, ⟨?_, heq⟩, ?_⟩
  · simpa [ball, Metric.mem_closedBall, dist_zero_right] using hc
  · intro y hy
    have hyball : y ∈ ball := by
      simpa [ball, Metric.mem_closedBall, dist_zero_right] using hy.1
    have hyfix : T y = y := by
      apply B.injective
      simp only [T, correctionMap, B.apply_symm_apply]
      rw [← hy.2]
      abel
    have hdist := hlip.dist_le_mul c hc y hyball
    rw [hfix, hyfix] at hdist
    have hhalf : ((1 / 2 : NNReal) : ℝ) = 1 / 2 := by norm_num
    rw [hhalf] at hdist
    have : dist c y = 0 := by nlinarith [@dist_nonneg E _ c y]
    exact (eq_of_dist_eq_zero this).symm

end GaloisForLFunctions.HTGeometry.NavierStokesQuadraticCorrection
