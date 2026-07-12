import GaloisForLFunctions.RHTower.CCMRectangularObservablePoleTomography

/-!
# Manuscript capstones for fixed-window logarithmic Weil tomography

These declarations bundle the concrete theorem surface used by the standalone
paper.  They introduce no abstract substitute for the analytic content.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- Pointwise nonnegativity of the one fixed-width logarithmic family. -/
def RectangularLogSampleNonnegative (L : ℝ) : Prop :=
  ∀ n : ℕ, 0 ≤
    (xiWeilPolarization
      (xiRectangularTwoEdgeTransform L (Real.log n / 2))
      (xiRectangularTwoEdgeTransform L (Real.log n / 2))).re

/-- Eventual lower boundedness on the admissible logarithmic tail. -/
def RectangularLogSampleEventuallyBoundedBelow (L : ℝ) : Prop :=
  ∃ B : ℝ, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
    L ≤ Real.log n / 2 →
      B ≤ (xiWeilPolarization
        (xiRectangularTwoEdgeTransform L (Real.log n / 2))
        (xiRectangularTwoEdgeTransform L (Real.log n / 2))).re

/-- Norm boundedness on all admissible logarithmic samples. -/
def RectangularLogSampleNormBounded (L : ℝ) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, L ≤ Real.log n / 2 →
    ‖xiWeilPolarization
      (xiRectangularTwoEdgeTransform L (Real.log n / 2))
      (xiRectangularTwoEdgeTransform L (Real.log n / 2))‖ ≤ C

/-- Cofinal divergence below every real level on the admissible mesh. -/
def RectangularLogSampleCofinallyUnboundedBelow (L : ℝ) : Prop :=
  ∀ B : ℝ, ∀ N0 : ℕ, ∃ n : ℕ,
    N0 ≤ n ∧ L ≤ Real.log n / 2 ∧
      (xiWeilPolarization
        (xiRectangularTwoEdgeTransform L (Real.log n / 2))
        (xiRectangularTwoEdgeTransform L (Real.log n / 2))).re < B

/-- Direct combined form of the paper's fixed-window completeness theorem. -/
theorem fixedWindowLogarithmicWeilCompleteness_capstone
    {L : ℝ} (hL : 0 < L) :
    (RiemannHypothesis ↔ RectangularLogSampleNonnegative L) ∧
    (RiemannHypothesis ↔ RectangularLogSampleEventuallyBoundedBelow L) ∧
    (RiemannHypothesis ↔ RectangularLogSampleNormBounded L) ∧
    (¬RiemannHypothesis → RectangularLogSampleCofinallyUnboundedBelow L) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact riemannHypothesis_iff_rectangular_logSample_weil_nonneg hL
  · exact riemannHypothesis_iff_rectangular_logSample_weil_eventually_bddBelow hL
  · exact riemannHypothesis_iff_rectangular_logSample_weil_norm_bdd hL
  · intro hRH
    exact not_riemannHypothesis_implies_rectangular_weil_cofinally_unbounded_below
      hL hRH

/-- Direct combined form of the paper's observable tail theorem: initial
L-series agreement, global meromorphicity, and exact simple-pole support. -/
theorem fixedWindowObservablePoleTomography_capstone
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2) :
    (∀ (delta : ℝ), 0 ≤ delta →
      (∀ q : XiRightZeroCopy,
        (xiRightCenteredZero q).re ≤ delta) →
      ∀ s : ℂ, 1 + delta < s.re →
        LSeries (xiRectangularWeilTailCoefficient L N) s =
          xiRectangularWeilTailContinuation L N s) ∧
    MeromorphicOn (xiRectangularWeilTailContinuation L N)
      {s : ℂ | 1 < s.re} ∧
    (∀ s : ℂ, 1 < s.re →
      (meromorphicOrderAt (xiRectangularWeilTailContinuation L N) s =
          ((-1 : ℤ) : WithTop ℤ) ↔
        ∃ q : XiRightZeroCopy, xiRightShiftedPole q = s)) := by
  refine ⟨?_,
    meromorphicOn_xiRectangularWeilTailContinuation_rightOne hN, ?_⟩
  · intro delta hdelta0 hupper s hs
    exact LSeries_xiRectangularWeilTailCoefficient_eq_continuation
      hN hdelta0 hupper hs
  · intro s hs
    exact meromorphicOrderAt_xiRectangularWeilTailContinuation_eq_neg_one_iff
      hL hN hs

/-- Direct combined form of the paper's support-recovery corollary. -/
theorem fixedWindowObservableSupportRecovery_capstone
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2) :
    {ρ : ℂ | xi ρ = 0 ∧ 1 / 2 < ρ.re} =
        (fun s : ℂ => s - 1 / 2) ''
          {s : ℂ | 1 < s.re ∧
            meromorphicOrderAt
              (xiRectangularWeilTailContinuation L N) s =
                ((-1 : ℤ) : WithTop ℤ)} ∧
      (RiemannHypothesis ↔
        ∀ s : ℂ, 1 < s.re →
          AnalyticAt ℂ (xiRectangularWeilTailContinuation L N) s) := by
  exact ⟨xiRightZeroSupport_eq_image_observableSimplePoleSupport hL hN,
    riemannHypothesis_iff_observableTailContinuation_analytic_rightOne hL hN⟩

end

end RHTower
