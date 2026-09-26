import GaloisForLFunctions.RHTower.EtaHighHeightReflectionClassification
import GaloisForLFunctions.HTGeometry.ConjugateReflectionInverse

set_option autoImplicit false

/-!
# Recovering eta from its mirror difference

The functional equation identifies the weighted mirror difference with a
real-linear conjugate residual.  Its inverse recovers the original eta
value at every noncentral high-height point, including zeros.  The same
identity gives a quantitative lower bound before division by a possibly
small determinant.
-/

namespace RiemannGaussian

open Complex GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate

noncomputable section

theorem pairedEtaCore_elementary_reflection_conj (x b : ℝ) :
    let s := etaReflectionStripPoint x b
    conj (pairedEtaCore s) = conj (etaElementaryReflectionMultiplier s) *
      pairedEtaCore (1 - conj s) := by
  have h := congrArg conj (pairedEtaCore_elementary_reflection x b)
  dsimp only at h ⊢
  rw [map_mul, ← pairedEtaCore_conj (1 - etaReflectionStripPoint x b),
    map_sub, map_one] at h
  exact h

/-- The weighted mirror difference is exactly the generic conjugate
residual; no eta value has been cancelled. -/
theorem pairedEtaCore_elementary_reflection_residual (x b : ℝ) :
    let s := etaReflectionStripPoint x b
    conjugateReflectionResidual (conj (etaElementaryReflectionMultiplier s)) 1
      (pairedEtaCore s) = conj (etaElementaryReflectionMultiplier s) *
        (pairedEtaCore s - pairedEtaCore (1 - conj s)) := by
  dsimp only
  rw [conjugateReflectionResidual, one_mul, pairedEtaCore_elementary_reflection_conj]
  ring

/-- The multiplier's modulus gap controls the actual eta mirror
difference, with the source magnitude retained. -/
theorem pairedEtaCore_elementary_reflection_gap (x b : ℝ) :
    let s := etaReflectionStripPoint x b
    |‖etaElementaryReflectionMultiplier s‖ - 1| * ‖pairedEtaCore s‖ ≤
      ‖etaElementaryReflectionMultiplier s‖ *
        ‖pairedEtaCore s - pairedEtaCore (1 - conj s)‖ := by
  dsimp only
  have h := conjugateReflectionResidual_norm_lower
    (conj (etaElementaryReflectionMultiplier (etaReflectionStripPoint x b))) 1
    (pairedEtaCore (etaReflectionStripPoint x b))
  rw [pairedEtaCore_elementary_reflection_residual, norm_mul,
    Complex.norm_conj, norm_one] at h
  exact h

/-- At high heights the only singular reconstruction point is the
midline.  The totalized inverse returns zero there and the original eta
value everywhere else, without a nonvanishing assumption. -/
theorem pairedEtaCore_highHeight_reflection_recovery (x t : ℝ) :
    let s := etaReflectionStripPoint x (etaArchimedeanHeight t)
    conjugateReflectionInverse (conj (etaElementaryReflectionMultiplier s)) 1
      (conj (etaElementaryReflectionMultiplier s) *
        (pairedEtaCore s - pairedEtaCore (1 - conj s))) =
      if sigmoid x = 1 / 2 then 0 else pairedEtaCore s := by
  dsimp only
  let s := etaReflectionStripPoint x (etaArchimedeanHeight t)
  have hc : Complex.normSq (conj (etaElementaryReflectionMultiplier s)) =
      Complex.normSq 1 ↔ sigmoid x = 1 / 2 := by
    simp only [Complex.normSq_eq_norm_sq, Complex.norm_conj, norm_one, one_pow]
    constructor
    · intro h
      apply (norm_etaElementaryReflectionMultiplier_eq_one_iff x t).mp
      nlinarith [norm_nonneg (etaElementaryReflectionMultiplier s)]
    · intro h
      have hm := (norm_etaElementaryReflectionMultiplier_eq_one_iff x t).mpr h
      change ‖etaElementaryReflectionMultiplier s‖ = 1 at hm
      rw [hm]
      norm_num
  rw [← pairedEtaCore_elementary_reflection_residual,
    conjugateReflectionInverse_residual]
  change (if Complex.normSq (conj (etaElementaryReflectionMultiplier s)) =
    Complex.normSq 1 then 0 else pairedEtaCore s) = _
  simp only [hc]
  rfl

end

end RiemannGaussian
