import GaloisForLFunctions.HTGeometry.ConjugateReflectionRecovery
import GaloisForLFunctions.HTGeometry.GammaVerticalDecay
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaCompletionReflectionMultiplier

/-!
# Source-retaining reflection bounds for the actual eta Laplace partition

The completion multiplier controls a conjugate-linear reflection residual,
not a source-free modulus condition.  In logistic strip coordinates the
functional equation and conjugation law supply all analytic inputs.  The
resulting recovery identity and norm bounds remain valid at common zeros.
-/

namespace RiemannGaussian

open Complex GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate

noncomputable section

/-- A global coordinate covering the open critical strip. -/
def etaReflectionStripPoint (x b : ℝ) : ℂ := (sigmoid x : ℂ) + (b : ℂ) * I

theorem etaReflectionStripPoint_re_pos (x b : ℝ) :
    0 < (etaReflectionStripPoint x b).re := by
  simpa [etaReflectionStripPoint] using sigmoid_pos x

theorem etaReflectionStripPoint_re_lt_one (x b : ℝ) :
    (etaReflectionStripPoint x b).re < 1 := by
  simpa [etaReflectionStripPoint] using sigmoid_lt_one x

/-- The conjugate functional equation at the actual reflected source. -/
theorem pairedEtaLaplacePartition_mirror_logistic (x b : ℝ) :
    pairedEtaLaplacePartition (1 - conj (etaReflectionStripPoint x b)) =
      conj (pairedEtaLaplaceReflectionMultiplier (etaReflectionStripPoint x b)) *
        conj (pairedEtaLaplacePartition (etaReflectionStripPoint x b)) := by
  have hs := etaReflectionStripPoint_re_pos x b
  have ht := etaReflectionStripPoint_re_lt_one x b
  have hp : 0 < (1 - etaReflectionStripPoint x b).re := by simpa using sub_pos.mpr ht
  rw [show 1 - conj (etaReflectionStripPoint x b) =
      conj (1 - etaReflectionStripPoint x b) by simp,
    pairedEtaLaplacePartition_conj hp,
    pairedEtaLaplacePartition_one_sub hs ht, map_mul]

/-- The exact residual representation keeps the Laplace source visible. -/
theorem pairedEtaLaplacePartition_reflection_residual (x b : ℝ) :
    conjugateReflectionResidual 1
      (conj (pairedEtaLaplaceReflectionMultiplier (etaReflectionStripPoint x b)))
      (pairedEtaLaplacePartition (etaReflectionStripPoint x b)) =
        pairedEtaLaplacePartition (etaReflectionStripPoint x b) -
          pairedEtaLaplacePartition (1 - conj (etaReflectionStripPoint x b)) := by
  rw [pairedEtaLaplacePartition_mirror_logistic]
  simp [conjugateReflectionResidual]

/-- A modulus gap is multiplied by the actual source amplitude.  This is
the zero-safe replacement for cancelling that amplitude. -/
theorem pairedEtaLaplacePartition_reflection_gap (x b : ℝ) :
    |1 - ‖pairedEtaLaplaceReflectionMultiplier (etaReflectionStripPoint x b)‖| *
        ‖pairedEtaLaplacePartition (etaReflectionStripPoint x b)‖ ≤
      ‖pairedEtaLaplacePartition (etaReflectionStripPoint x b) -
        pairedEtaLaplacePartition (1 - conj (etaReflectionStripPoint x b))‖ := by
  have h := conjugateReflectionResidual_norm_lower 1
    (conj (pairedEtaLaplaceReflectionMultiplier (etaReflectionStripPoint x b)))
    (pairedEtaLaplacePartition (etaReflectionStripPoint x b))
  simpa only [norm_one, Complex.norm_conj,
    pairedEtaLaplacePartition_reflection_residual] using h

/-- The source can be reconstructed from the residual and its conjugate
after multiplication by the explicitly known real determinant. -/
theorem pairedEtaLaplacePartition_reflection_recovery (x b : ℝ) :
    let s := etaReflectionStripPoint x b
    let Δ := pairedEtaLaplacePartition s - pairedEtaLaplacePartition (1 - conj s)
    Δ + conj (pairedEtaLaplaceReflectionMultiplier s) * conj Δ =
      ((1 - Complex.normSq (pairedEtaLaplaceReflectionMultiplier s) : ℝ) : ℂ) *
        pairedEtaLaplacePartition s := by
  dsimp only
  have h := conjugateReflectionResidual_recovery 1
    (conj (pairedEtaLaplaceReflectionMultiplier (etaReflectionStripPoint x b)))
    (pairedEtaLaplacePartition (etaReflectionStripPoint x b))
  simpa only [map_one, one_mul, Complex.normSq_one, Complex.normSq_conj,
    pairedEtaLaplacePartition_reflection_residual] using h

/-- Exact common-zero-or-phase-matching classification for the literal
Laplace reflection equation. -/
theorem pairedEtaLaplacePartition_reflection_eq_iff (x b : ℝ) :
    let s := etaReflectionStripPoint x b
    pairedEtaLaplacePartition s = pairedEtaLaplacePartition (1 - conj s) ↔
      pairedEtaLaplacePartition s = 0 ∨
        (pairedEtaLaplacePartition s ≠ 0 ∧
          conj (pairedEtaLaplaceReflectionMultiplier s) =
            pairedEtaLaplacePartition s / conj (pairedEtaLaplacePartition s)) := by
  dsimp only
  have h := conjugateReflectionResidual_eq_zero_iff 1
    (conj (pairedEtaLaplaceReflectionMultiplier (etaReflectionStripPoint x b)))
    (pairedEtaLaplacePartition (etaReflectionStripPoint x b))
  simpa only [pairedEtaLaplacePartition_reflection_residual, sub_eq_zero, one_mul] using h

/-- The same source-retaining bound applies to eta itself, with the two
spectral factors restored. -/
theorem pairedEtaCore_reflection_source_gap (x b : ℝ) :
    let s := etaReflectionStripPoint x b
    |‖s‖ - ‖(1 - conj s) * conj (pairedEtaLaplaceReflectionMultiplier s)‖| *
        ‖pairedEtaLaplacePartition s‖ ≤
      ‖pairedEtaCore s - pairedEtaCore (1 - conj s)‖ := by
  dsimp only
  let s := etaReflectionStripPoint x b
  have hs := etaReflectionStripPoint_re_pos x b
  have ht := etaReflectionStripPoint_re_lt_one x b
  have hp : 0 < (1 - conj s).re := by
    simpa [s] using sub_pos.mpr ht
  rw [pairedEtaCore_eq_mul_laplacePartition hs,
    pairedEtaCore_eq_mul_laplacePartition hp,
    pairedEtaLaplacePartition_mirror_logistic]
  convert conjugateReflectionResidual_norm_lower s
    ((1 - conj s) * conj (pairedEtaLaplaceReflectionMultiplier s))
    (pairedEtaLaplacePartition s) using 1
  simp only [conjugateReflectionResidual, s, mul_assoc]

end

end RiemannGaussian
