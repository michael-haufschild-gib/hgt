import GaloisForLFunctions.RHTower.XiJetFreeness
import GaloisForLFunctions.HTGeometry.ComplexHermitianRealification
import GaloisForLFunctions.HTGeometry.GreedyBumpLocalGeometry

/-!
# Greedy-bump laws for finite completed-Xi jet sampling

At every finite depth, completed-Xi initial derivatives admit both a strict complex evaluation Gram
and a strict tagged real-channel evaluation Gram.  Applying arXiv:2609.03581 to the two designs
shows exactly how retaining both complex channels doubles real profiling dimension and leading
bias.  These are unconditional finite sampling laws, not an RH criterion.
-/

namespace RHTower

open Matrix
open scoped ComplexOrder

noncomputable section

/-- Chosen distinct complex sample packet for initial completed-Xi jets. -/
def greedyBumpXiJetComplexPoints (n : ℕ) : Fin (n + 1) → ℂ :=
  Classical.choose (exists_injective_xiInitialJetEvaluationGram_posDef n)

/-- Chosen complex jet packet is collision-free. -/
theorem greedyBumpXiJetComplexPoints_injective (n : ℕ) :
    Function.Injective (greedyBumpXiJetComplexPoints n) :=
  (Classical.choose_spec (exists_injective_xiInitialJetEvaluationGram_posDef n)).1

/-- Chosen complex jet evaluation Gram is strictly positive. -/
theorem greedyBumpXiJetComplexGram_posDef (n : ℕ) :
    (xiInitialJetEvaluationGram n (greedyBumpXiJetComplexPoints n)).PosDef :=
  (Classical.choose_spec (exists_injective_xiInitialJetEvaluationGram_posDef n)).2

/-- Doubled-real complex jet evaluation Gram. -/
def greedyBumpXiJetComplexRealifiedMatrix (n : ℕ) :
    Matrix (Fin ((n + 1) + (n + 1))) (Fin ((n + 1) + (n + 1))) ℝ :=
  (GaloisForLFunctions.HTGeometry.complexMatrixRealification
      (xiInitialJetEvaluationGram n (greedyBumpXiJetComplexPoints n))).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm

/-- Complex completed-Xi jet sampling as a positive template metric. -/
def greedyBumpXiJetComplexMetric (n : ℕ) :
    GaloisForLFunctions.HTGeometry.PositiveTemplateMetric
      ((n + 1) + (n + 1)) where
  matrix := greedyBumpXiJetComplexRealifiedMatrix n
  posDef := (GaloisForLFunctions.HTGeometry.complexMatrixRealification_posDef
    (greedyBumpXiJetComplexGram_posDef n)).submatrix finSumFinEquiv.symm.injective

/-- Chosen tagged real/imaginary sample packet for initial completed-Xi jets. -/
def greedyBumpXiJetRealChannelNodes (n : ℕ) : Fin (n + 1) → ℂ × Bool :=
  Classical.choose (exists_injective_xiInitialJetRealChannelEvaluationGram_posDef n)

/-- Chosen tagged real-channel jet packet is collision-free. -/
theorem greedyBumpXiJetRealChannelNodes_injective (n : ℕ) :
    Function.Injective (greedyBumpXiJetRealChannelNodes n) :=
  (Classical.choose_spec
    (exists_injective_xiInitialJetRealChannelEvaluationGram_posDef n)).1

/-- Chosen tagged real-channel jet evaluation Gram is strictly positive. -/
theorem greedyBumpXiJetRealChannelGram_posDef (n : ℕ) :
    (xiInitialJetRealChannelEvaluationGram n
      (greedyBumpXiJetRealChannelNodes n)).PosDef :=
  (Classical.choose_spec
    (exists_injective_xiInitialJetRealChannelEvaluationGram_posDef n)).2

/-- Tagged real-channel completed-Xi jet sampling as a positive template metric. -/
def greedyBumpXiJetRealChannelMetric (n : ℕ) :
    GaloisForLFunctions.HTGeometry.PositiveTemplateMetric (n + 1) where
  matrix := xiInitialJetRealChannelEvaluationGram n
    (greedyBumpXiJetRealChannelNodes n)
  posDef := greedyBumpXiJetRealChannelGram_posDef n

/-- Complex jet sampling satisfies the complete local-search package. -/
theorem greedyBumpXiJetComplex_laws (n : ℕ)
    (Q : GaloisForLFunctions.HTGeometry.PositiveSignal) :
    GaloisForLFunctions.HTGeometry.GreedyBumpMetricLaws Q
      (greedyBumpXiJetComplexMetric n) :=
  GaloisForLFunctions.HTGeometry.greedyBumpMetricLaws_closed Q
    (greedyBumpXiJetComplexMetric n)

/-- Tagged real-channel jet sampling satisfies the complete local-search package. -/
theorem greedyBumpXiJetRealChannel_laws (n : ℕ)
    (Q : GaloisForLFunctions.HTGeometry.PositiveSignal) :
    GaloisForLFunctions.HTGeometry.GreedyBumpMetricLaws Q
      (greedyBumpXiJetRealChannelMetric n) :=
  GaloisForLFunctions.HTGeometry.greedyBumpMetricLaws_closed Q
    (greedyBumpXiJetRealChannelMetric n)

/-- Retaining both complex channels gives bias `(n+1)/Q`. -/
theorem greedyBumpXiJetComplex_bias (n : ℕ)
    (Q : GaloisForLFunctions.HTGeometry.PositiveSignal) :
    (1 / 2 : ℝ) * Matrix.trace
        ((GaloisForLFunctions.HTGeometry.greedyBumpHessian Q
          (greedyBumpXiJetComplexMetric n))⁻¹ *
          (greedyBumpXiJetComplexMetric n).matrix) =
      (n + 1 : ℕ) / (Q : ℝ) := by
  rw [GaloisForLFunctions.HTGeometry.greedyBump_matched_bias]
  push_cast
  field_simp [ne_of_gt Q.property]
  ring

/-- Selecting one tagged real channel gives bias `(n+1)/(2Q)`. -/
theorem greedyBumpXiJetRealChannel_bias (n : ℕ)
    (Q : GaloisForLFunctions.HTGeometry.PositiveSignal) :
    (1 / 2 : ℝ) * Matrix.trace
        ((GaloisForLFunctions.HTGeometry.greedyBumpHessian Q
          (greedyBumpXiJetRealChannelMetric n))⁻¹ *
          (greedyBumpXiJetRealChannelMetric n).matrix) =
      (n + 1 : ℕ) / (2 * (Q : ℝ)) :=
  GaloisForLFunctions.HTGeometry.greedyBump_matched_bias Q
    (greedyBumpXiJetRealChannelMetric n)

/-- Full complex sampling has exactly twice the real-channel leading bias. -/
theorem greedyBumpXiJetComplex_bias_eq_twice_realChannel (n : ℕ)
    (Q : GaloisForLFunctions.HTGeometry.PositiveSignal) :
    (1 / 2 : ℝ) * Matrix.trace
        ((GaloisForLFunctions.HTGeometry.greedyBumpHessian Q
          (greedyBumpXiJetComplexMetric n))⁻¹ *
          (greedyBumpXiJetComplexMetric n).matrix) =
      2 * ((1 / 2 : ℝ) * Matrix.trace
        ((GaloisForLFunctions.HTGeometry.greedyBumpHessian Q
          (greedyBumpXiJetRealChannelMetric n))⁻¹ *
          (greedyBumpXiJetRealChannelMetric n).matrix)) := by
  rw [greedyBumpXiJetComplex_bias, greedyBumpXiJetRealChannel_bias]
  ring

/-! ## Joint sample-point and Xi-jet dictionary -/

/-- Chosen distinct sample packet for the joint coordinate `(z, ξ, ξ′, …, ξ⁽ⁿ⁾)`. -/
def greedyBumpXiPointJetPoints (n : ℕ) : Fin (n + 2) → ℂ :=
  Classical.choose (exists_injective_xiPointInitialJetEvaluationGram_posDef n)

/-- Chosen joint point/jet evaluation Gram is strictly positive. -/
theorem greedyBumpXiPointJetGram_posDef (n : ℕ) :
    (GaloisForLFunctions.HTGeometry.finiteEvaluationGram
      (GaloisForLFunctions.pointJetFunctionTuple xi n)
      (greedyBumpXiPointJetPoints n)).PosDef :=
  (Classical.choose_spec
    (exists_injective_xiPointInitialJetEvaluationGram_posDef n)).2

/-- Doubled-real joint point/jet evaluation metric. -/
def greedyBumpXiPointJetMetric (n : ℕ) :
    GaloisForLFunctions.HTGeometry.PositiveTemplateMetric
      ((n + 2) + (n + 2)) where
  matrix := (GaloisForLFunctions.HTGeometry.complexMatrixRealification
      (GaloisForLFunctions.HTGeometry.finiteEvaluationGram
        (GaloisForLFunctions.pointJetFunctionTuple xi n)
        (greedyBumpXiPointJetPoints n))).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm
  posDef := (GaloisForLFunctions.HTGeometry.complexMatrixRealification_posDef
    (greedyBumpXiPointJetGram_posDef n)).submatrix finSumFinEquiv.symm.injective

/-- Joint point/jet sampling satisfies the complete local-search package. -/
theorem greedyBumpXiPointJet_laws (n : ℕ)
    (Q : GaloisForLFunctions.HTGeometry.PositiveSignal) :
    GaloisForLFunctions.HTGeometry.GreedyBumpMetricLaws Q
      (greedyBumpXiPointJetMetric n) :=
  GaloisForLFunctions.HTGeometry.greedyBumpMetricLaws_closed Q
    (greedyBumpXiPointJetMetric n)

/-- Joint point/jet sampling has exact bias `(n+2)/Q`. -/
theorem greedyBumpXiPointJet_bias (n : ℕ)
    (Q : GaloisForLFunctions.HTGeometry.PositiveSignal) :
    (1 / 2 : ℝ) * Matrix.trace
        ((GaloisForLFunctions.HTGeometry.greedyBumpHessian Q
          (greedyBumpXiPointJetMetric n))⁻¹ *
          (greedyBumpXiPointJetMetric n).matrix) =
      (n + 2 : ℕ) / (Q : ℝ) := by
  rw [GaloisForLFunctions.HTGeometry.greedyBump_matched_bias]
  push_cast
  field_simp [ne_of_gt Q.property]
  ring

/-- Adding the sample-point coordinate costs exactly one extra complex-direction bias `1/Q`. -/
theorem greedyBumpXiPointJet_bias_eq_jetBias_add_one_over_signal (n : ℕ)
    (Q : GaloisForLFunctions.HTGeometry.PositiveSignal) :
    (1 / 2 : ℝ) * Matrix.trace
        ((GaloisForLFunctions.HTGeometry.greedyBumpHessian Q
          (greedyBumpXiPointJetMetric n))⁻¹ *
          (greedyBumpXiPointJetMetric n).matrix) =
      (1 / 2 : ℝ) * Matrix.trace
        ((GaloisForLFunctions.HTGeometry.greedyBumpHessian Q
          (greedyBumpXiJetComplexMetric n))⁻¹ *
          (greedyBumpXiJetComplexMetric n).matrix) + 1 / (Q : ℝ) := by
  rw [greedyBumpXiPointJet_bias, greedyBumpXiJetComplex_bias]
  push_cast
  field_simp [ne_of_gt Q.property]
  ring

end

end RHTower
