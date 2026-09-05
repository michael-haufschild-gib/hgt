import GaloisForLFunctions.HTGeometry.GreedyBumpLocalGeometry
import GaloisForLFunctions.HTGeometry.ArcsineHankelPositiveDefinite
import GaloisForLFunctions.HTGeometry.BlackHoleDressedLogSpectralClock
import GaloisForLFunctions.HTGeometry.AtomicMomentHankelSection

/-!
# Greedy-bump geometry on positive Hankel metrics

This module applies the determinant-volume and matched trace-bias laws of arXiv:2609.03581 to
three positive-definite moment metrics already present in the corpus: arcsine moments, the
factorial-normalized black-hole zeta jet, and finite positive atomic designs.  Positivity and
nondegeneracy are carried by data, so every exported identity is unconditional.
-/

open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Arcsine moment Hankel blocks, viewed as nondegenerate template metrics. -/
def greedyBumpArcsineMetric (D : ℕ) : PositiveTemplateMetric D where
  matrix := _root_.HTGeometry.momentHankelMatrix normalizedCentralBinom D
  posDef := normalizedCentralBinom_momentHankelMatrix_posDef D

/-- Complete optimizer, volume, trace, and bias laws for every arcsine block. -/
theorem greedyBumpArcsine_laws (D : ℕ) (Q : PositiveSignal) :
    GreedyBumpMetricLaws Q (greedyBumpArcsineMetric D) :=
  greedyBumpMetricLaws_closed Q (greedyBumpArcsineMetric D)

/-- Signal scaling multiplies the arcsine Hankel volume determinant by `Q^D`. -/
theorem greedyBumpArcsineHessian_det (D : ℕ) (Q : PositiveSignal) :
    (greedyBumpHessian Q (greedyBumpArcsineMetric D)).det =
      (Q : ℝ) ^ D *
        (_root_.HTGeometry.momentHankelMatrix normalizedCentralBinom D).det :=
  greedyBumpHessian_det Q (greedyBumpArcsineMetric D)

/-- Arcsine trials volume scales by exactly `Q^(D/2)`. -/
theorem greedyBumpArcsineHessian_sqrt_det (D : ℕ) (Q : PositiveSignal) :
    Real.sqrt (greedyBumpHessian Q (greedyBumpArcsineMetric D)).det =
      (Q : ℝ) ^ ((D : ℝ) / 2) *
        Real.sqrt (_root_.HTGeometry.momentHankelMatrix normalizedCentralBinom D).det :=
  greedyBumpHessian_sqrt_det Q (greedyBumpArcsineMetric D)

/-- The arcsine Hankel metric has matched inverse-trace penalty `D/Q`. -/
theorem greedyBumpArcsine_tracePenalty (D : ℕ) (Q : PositiveSignal) :
    Matrix.trace
      ((greedyBumpHessian Q (greedyBumpArcsineMetric D))⁻¹ *
        (greedyBumpArcsineMetric D).matrix) =
      (D : ℝ) / (Q : ℝ) :=
  greedyBumpHessian_trace_inv_mul Q (greedyBumpArcsineMetric D)

/-- Profiling over `D` arcsine-moment directions contributes exact bias `D/(2Q)`. -/
theorem greedyBumpArcsine_bias (D : ℕ) (Q : PositiveSignal) :
    (1 / 2 : ℝ) * Matrix.trace
      ((greedyBumpHessian Q (greedyBumpArcsineMetric D))⁻¹ *
        (greedyBumpArcsineMetric D).matrix) =
      (D : ℝ) / (2 * (Q : ℝ)) :=
  greedyBump_matched_bias Q (greedyBumpArcsineMetric D)

/-- The normalized black-hole far-zone zeta jet defines a nondegenerate template metric. -/
def greedyBumpBlackHoleJetMetric (scaleLog : ℂ) (D : ℕ) : PositiveTemplateMetric D where
  matrix := _root_.HTGeometry.momentHankelMatrix
    (_root_.HTGeometry.normalizedBlackHoleFarZoneJet scaleLog) D
  posDef := _root_.HTGeometry.normalizedBlackHoleFarZoneJet_hankel_posDef scaleLog D

/-- Complete optimizer, volume, trace, and bias laws for every black-hole zeta-jet block. -/
theorem greedyBumpBlackHoleJet_laws (scaleLog : ℂ) (D : ℕ) (Q : PositiveSignal) :
    GreedyBumpMetricLaws Q (greedyBumpBlackHoleJetMetric scaleLog D) :=
  greedyBumpMetricLaws_closed Q (greedyBumpBlackHoleJetMetric scaleLog D)

/-- Signal scaling multiplies the black-hole jet Hankel determinant by `Q^D`. -/
theorem greedyBumpBlackHoleJetHessian_det (scaleLog : ℂ) (D : ℕ)
    (Q : PositiveSignal) :
    (greedyBumpHessian Q (greedyBumpBlackHoleJetMetric scaleLog D)).det =
      (Q : ℝ) ^ D *
        (_root_.HTGeometry.momentHankelMatrix
          (_root_.HTGeometry.normalizedBlackHoleFarZoneJet scaleLog) D).det :=
  greedyBumpHessian_det Q (greedyBumpBlackHoleJetMetric scaleLog D)

/-- Black-hole zeta-jet trials volume scales by exactly `Q^(D/2)`. -/
theorem greedyBumpBlackHoleJetHessian_sqrt_det (scaleLog : ℂ) (D : ℕ)
    (Q : PositiveSignal) :
    Real.sqrt (greedyBumpHessian Q (greedyBumpBlackHoleJetMetric scaleLog D)).det =
      (Q : ℝ) ^ ((D : ℝ) / 2) *
        Real.sqrt (_root_.HTGeometry.momentHankelMatrix
          (_root_.HTGeometry.normalizedBlackHoleFarZoneJet scaleLog) D).det :=
  greedyBumpHessian_sqrt_det Q (greedyBumpBlackHoleJetMetric scaleLog D)

/-- The black-hole zeta-jet metric has matched inverse-trace penalty `D/Q`. -/
theorem greedyBumpBlackHoleJet_tracePenalty (scaleLog : ℂ) (D : ℕ)
    (Q : PositiveSignal) :
    Matrix.trace
      ((greedyBumpHessian Q (greedyBumpBlackHoleJetMetric scaleLog D))⁻¹ *
        (greedyBumpBlackHoleJetMetric scaleLog D).matrix) =
      (D : ℝ) / (Q : ℝ) :=
  greedyBumpHessian_trace_inv_mul Q (greedyBumpBlackHoleJetMetric scaleLog D)

/-- Profiling over `D` black-hole zeta-jet directions contributes exact bias `D/(2Q)`. -/
theorem greedyBumpBlackHoleJet_bias (scaleLog : ℂ) (D : ℕ)
    (Q : PositiveSignal) :
    (1 / 2 : ℝ) * Matrix.trace
      ((greedyBumpHessian Q (greedyBumpBlackHoleJetMetric scaleLog D))⁻¹ *
        (greedyBumpBlackHoleJetMetric scaleLog D).matrix) =
      (D : ℝ) / (2 * (Q : ℝ)) :=
  greedyBump_matched_bias Q (greedyBumpBlackHoleJetMetric scaleLog D)

/-- Finite positive atomic design with enough distinct nodes for a strict Hankel section. -/
structure GreedyBumpAtomicDesign (N D : ℕ) where
  positiveDimension : 0 < D
  weight : Fin N → ℝ
  node : Fin N → ℝ
  weight_pos : ∀ r, 0 < weight r
  enoughNodes : D ≤ ((Finset.univ : Finset (Fin N)).image node).card

/-- An admissible atomic moment design, viewed as a nondegenerate template metric. -/
def GreedyBumpAtomicDesign.metric {N D : ℕ}
    (A : GreedyBumpAtomicDesign N D) : PositiveTemplateMetric D where
  matrix := atomicHankel A.weight A.node D
  posDef := atomicHankel_posDef A.positiveDimension A.weight A.node
    A.weight_pos A.enoughNodes

/-- Complete optimizer, volume, trace, and bias laws for every admissible atomic design. -/
theorem greedyBumpAtomic_laws {N D : ℕ} (A : GreedyBumpAtomicDesign N D)
    (Q : PositiveSignal) : GreedyBumpMetricLaws Q A.metric :=
  greedyBumpMetricLaws_closed Q A.metric

/-- Signal scaling multiplies every admissible atomic Hankel determinant by `Q^D`. -/
theorem greedyBumpAtomicHessian_det {N D : ℕ} (A : GreedyBumpAtomicDesign N D)
    (Q : PositiveSignal) :
    (greedyBumpHessian Q A.metric).det =
      (Q : ℝ) ^ D * (atomicHankel A.weight A.node D).det :=
  greedyBumpHessian_det Q A.metric

/-- Every admissible atomic trials volume scales by exactly `Q^(D/2)`. -/
theorem greedyBumpAtomicHessian_sqrt_det {N D : ℕ} (A : GreedyBumpAtomicDesign N D)
    (Q : PositiveSignal) :
    Real.sqrt (greedyBumpHessian Q A.metric).det =
      (Q : ℝ) ^ ((D : ℝ) / 2) *
        Real.sqrt (atomicHankel A.weight A.node D).det :=
  greedyBumpHessian_sqrt_det Q A.metric

/-- Every admissible atomic Hankel metric has matched inverse-trace penalty `D/Q`. -/
theorem greedyBumpAtomic_tracePenalty {N D : ℕ} (A : GreedyBumpAtomicDesign N D)
    (Q : PositiveSignal) :
    Matrix.trace ((greedyBumpHessian Q A.metric)⁻¹ * A.metric.matrix) =
      (D : ℝ) / (Q : ℝ) :=
  greedyBumpHessian_trace_inv_mul Q A.metric

/-- Profiling over an admissible `D`-direction atomic design contributes exact bias `D/(2Q)`. -/
theorem greedyBumpAtomic_bias {N D : ℕ} (A : GreedyBumpAtomicDesign N D)
    (Q : PositiveSignal) :
    (1 / 2 : ℝ) * Matrix.trace
      ((greedyBumpHessian Q A.metric)⁻¹ * A.metric.matrix) =
      (D : ℝ) / (2 * (Q : ℝ)) :=
  greedyBump_matched_bias Q A.metric

end

end GaloisForLFunctions.HTGeometry
