import GaloisForLFunctions.HTGeometry.ConstitutiveFiniteEscortFormationProperness
import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.EscortLogit

/-!
# Annealed escort support and entropy tangent

The normalized power reweighting used by annealed gradient descent is a real escort flow.  In
log-odds coordinates it is scalar dilation.  On a finite positive law it is exactly
`w x ^ alpha / ∑ y, w y ^ alpha`; its derivative at physical exponent one is the centered
log-probability tangent.

Crucially, the exponential-tilt presentation proves an exact hard-support law: annealing amplifies
small positive coordinates but cannot create a coordinate whose source weight is zero.  Thus an
independent full-support carrier must be introduced before any hard projection if annealing is to
avoid literal subspace trapping.
-/

namespace HTGeometry.ConstraintFrameRelativity

/-- Real-exponent escort transport, corresponding to inverse temperature `alpha`. -/
noncomputable def realEscortMap (alpha q : ℝ) : ℝ :=
  oddsToProb ((probToOdds q) ^ alpha)

theorem realEscortMap_mem {q : ℝ} (h0 : 0 < q) (h1 : q < 1) (alpha : ℝ) :
    0 < realEscortMap alpha q ∧ realEscortMap alpha q < 1 := by
  exact oddsToProb_mem (Real.rpow_pos_of_pos (probToOdds_pos h0 h1) alpha)

theorem probToOdds_realEscortMap {q : ℝ} (h0 : 0 < q) (h1 : q < 1) (alpha : ℝ) :
    probToOdds (realEscortMap alpha q) = (probToOdds q) ^ alpha := by
  unfold realEscortMap
  exact probToOdds_oddsToProb (Real.rpow_pos_of_pos (probToOdds_pos h0 h1) alpha)

theorem realEscortMap_one {q : ℝ} (h1 : q < 1) :
    realEscortMap 1 q = q := by
  rw [realEscortMap, Real.rpow_one, oddsToProb_probToOdds h1]

/-- Real escort transport is exact scalar dilation of the coefficient-faithful log-odds clock. -/
theorem logitClock_realEscortMap {tau : ℝ} {q : ℝ}
    (h0 : 0 < q) (h1 : q < 1) (alpha : ℝ) :
    logitClock tau (realEscortMap alpha q) = alpha * logitClock tau q := by
  rw [logitClock, logitClock, probToOdds_realEscortMap h0 h1,
    Real.log_rpow (probToOdds_pos h0 h1)]
  ring

/-- A nontrivial real escort fixes only the balanced occupation. -/
theorem realEscortMap_eq_self_iff {q alpha : ℝ} (h0 : 0 < q) (h1 : q < 1) :
    realEscortMap alpha q = q ↔ alpha = 1 ∨ q = 1 / 2 := by
  constructor
  · intro hfix
    by_cases halpha : alpha = 1
    · exact Or.inl halpha
    · right
      have hclock := logitClock_realEscortMap (tau := 1) h0 h1 alpha
      rw [hfix] at hclock
      have hzero : logitClock 1 q = 0 := by
        have hmul : (alpha - 1) * logitClock 1 q = 0 := by linarith
        exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr halpha)
      have hinv := logitInv_logitClock (τ := 1) (by norm_num) h0 h1
      rw [hzero] at hinv
      norm_num [logitInv] at hinv
      exact hinv.symm
  · rintro (rfl | rfl)
    · exact realEscortMap_one h1
    · norm_num [realEscortMap, probToOdds, oddsToProb]

end HTGeometry.ConstraintFrameRelativity

namespace GaloisForLFunctions.HTGeometry

open Finset

variable {n : ℕ}

/-- Normalized annealed escort of a finite law.  This presentation retains exact zero support. -/
noncomputable def finiteAnnealedEscort (w : Fin n → ℝ) (alpha : ℝ) (x : Fin n) : ℝ :=
  finiteExponentialTilt w (fun y => Real.log (w y)) (alpha - 1) x

/-- Literal normalized power law used by annealed gradient descent. -/
noncomputable def finitePowerEscort (w : Fin n → ℝ) (alpha : ℝ) (x : Fin n) : ℝ :=
  w x ^ alpha / ∑ y, w y ^ alpha

/-- The exponential-family construction is exactly the normalized power escort on positive law. -/
theorem finiteAnnealedEscort_eq_finitePowerEscort {w : Fin n → ℝ}
    (hw : ∀ x, 0 < w x) (alpha : ℝ) (x : Fin n) :
    finiteAnnealedEscort w alpha x = finitePowerEscort w alpha x := by
  unfold finiteAnnealedEscort finitePowerEscort finiteExponentialTilt finiteExpPartition
  have hterm (y : Fin n) :
      w y * Real.exp ((alpha - 1) * Real.log (w y)) = w y ^ alpha := by
    calc
      w y * Real.exp ((alpha - 1) * Real.log (w y)) =
          Real.exp (Real.log (w y)) *
            Real.exp ((alpha - 1) * Real.log (w y)) := by rw [Real.exp_log (hw y)]
      _ = Real.exp (Real.log (w y) + (alpha - 1) * Real.log (w y)) := by
        rw [Real.exp_add]
      _ = Real.exp (Real.log (w y) * alpha) := by
        congr 1
        ring
      _ = w y ^ alpha := (Real.rpow_def_of_pos (hw y) alpha).symm
  rw [hterm]
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  exact hterm y

theorem finiteAnnealedEscort_sum {w : Fin n → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hsum : ∑ x, w x = 1) (alpha : ℝ) :
    ∑ x, finiteAnnealedEscort w alpha x = 1 := by
  exact finiteExponentialTilt_sum hw hsum (alpha - 1)

/-- Annealing preserves hard support exactly: no zero source coordinate can be resurrected. -/
theorem finiteAnnealedEscort_eq_zero_iff {w : Fin n → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hsum : ∑ x, w x = 1) (alpha : ℝ) (x : Fin n) :
    finiteAnnealedEscort w alpha x = 0 ↔ w x = 0 := by
  have hZ : finiteExpPartition w (fun y => Real.log (w y)) (alpha - 1) ≠ 0 :=
    (finiteExpPartition_pos hw hsum (alpha - 1)).ne'
  unfold finiteAnnealedEscort finiteExponentialTilt
  rw [div_eq_zero_iff, mul_eq_zero]
  simp [hZ, Real.exp_ne_zero]

/-- First variation at physical exponent one is the centered log-probability score. -/
theorem hasDerivAt_finiteAnnealedEscort_one {w : Fin n → ℝ}
    (hsum : ∑ x, w x = 1) (x : Fin n) :
    HasDerivAt (fun alpha => finiteAnnealedEscort w alpha x)
      (finiteExponentialTangent w (fun y => Real.log (w y)) x) 1 := by
  have houter := hasDerivAt_finiteExponentialTilt_zero
    (w := w) (r := fun y => Real.log (w y)) hsum x
  have houter' : HasDerivAt
      (fun t => finiteExponentialTilt w (fun y => Real.log (w y)) t x)
      (finiteExponentialTangent w (fun y => Real.log (w y)) x) (1 - 1) := by
    simpa using houter
  simpa [finiteAnnealedEscort] using
    (HasDerivAt.comp_sub_const
      (f := fun t => finiteExponentialTilt w (fun y => Real.log (w y)) t x)
      1 1 houter')

theorem finiteAnnealedEscort_tangent_eq_entropyCentered (w : Fin n → ℝ) (x : Fin n) :
    finiteExponentialTangent w (fun y => Real.log (w y)) x =
      w x * (Real.log (w x) - ∑ y, w y * Real.log (w y)) := by
  rfl

end GaloisForLFunctions.HTGeometry
