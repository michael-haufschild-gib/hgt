import GaloisForLFunctions.RHTower.Deninger.DeningerCriticalFloquetVonMangoldtWall
import GaloisForLFunctions.RHTower.XiMassDeningerCrossCurrentWeld

/-!
# Unconditional Deninger cross-current polarization

The diagonal critical Floquet/von-Mangoldt identity was stated under an exponential
autocorrelation bound.  The all-weight Meyer target already forces that bound.  This module closes
that implication, removes the analytic premise from the diagonal identity, and polarizes the
result to a genuinely non-diagonal cross current.

This is the source-side counterpart of the Xi-mass unequal-half factorization.  In particular,
the diagonal sign wall does not obstruct the algebraic Floquet identity after polarization; any
remaining obstruction is realization/annihilation of the specific mass cross pair.
-/

open Complex Real MeasureTheory

namespace RHTower

noncomputable section

/-- Every all-weight Meyer source has autocorrelation decay at every prescribed positive rate.
The proof retains one exponential factor for integrability instead of discarding both factors by
the triangle inequality. -/
theorem exists_deningerAutocorrelationExpBound
    (u : DeningerMeyerStrongLogTarget) {A : ℝ} (hA : 0 < A) :
    ∃ B : ℝ, 0 ≤ B ∧ DeningerAutocorrelationExpBound u A B := by
  obtain ⟨C, hC, hu⟩ :=
    deningerMeyerStrongLog_norm_le_exp_neg_abs u (2 * A)
  let J : ℝ := ∫ x : ℝ, Real.exp (-(A * |x|))
  let B : ℝ := C ^ (2 : ℕ) * J
  have hJint : Integrable (fun x : ℝ => Real.exp (-(A * |x|))) :=
    integrable_exp_neg_mul_abs_weightedEulerStripFourierAnalytic hA
  have hJ : 0 ≤ J := by
    dsimp only [J]
    exact integral_nonneg fun _ => Real.exp_nonneg _
  refine ⟨B, mul_nonneg (sq_nonneg C) hJ, fun a => ?_⟩
  have hleft :=
    (integrable_deningerMeyerStrongLogAutocorrelationIntegrand u a).norm
  have hright : Integrable (fun x : ℝ =>
      (C ^ (2 : ℕ) * Real.exp (-A * |a|)) * Real.exp (-(A * |x|))) :=
    hJint.const_mul _
  rw [deningerMeyerStrongLogAutocorrelation]
  calc
    ‖∫ x : ℝ, (u : ℝ → ℂ) x *
        (starRingEnd ℂ) ((u : ℝ → ℂ) (x + a))‖ ≤
        ∫ x : ℝ, ‖(u : ℝ → ℂ) x *
          (starRingEnd ℂ) ((u : ℝ → ℂ) (x + a))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ,
        (C ^ (2 : ℕ) * Real.exp (-A * |a|)) * Real.exp (-(A * |x|)) := by
      apply integral_mono hleft hright
      intro x
      change ‖(u : ℝ → ℂ) x *
          (starRingEnd ℂ) ((u : ℝ → ℂ) (x + a))‖ ≤ _
      rw [norm_mul, Complex.norm_conj]
      have hx := hu x
      have hxa := hu (x + a)
      have hprod :
          ‖(u : ℝ → ℂ) x‖ * ‖(u : ℝ → ℂ) (x + a)‖ ≤
            (C * Real.exp (-(2 * A) * |x|)) *
              (C * Real.exp (-(2 * A) * |x + a|)) :=
        mul_le_mul hx hxa (norm_nonneg _) (mul_nonneg hC (Real.exp_nonneg _))
      have htri : |a| ≤ |x| + |x + a| := by
        have h := abs_sub (x + a) x
        have heq : x + a - x = a := by ring
        rw [heq] at h
        simpa only [add_comm] using h
      have hsize : |a| + |x| ≤ 2 * (|x| + |x + a|) := by
        nlinarith [abs_nonneg x, abs_nonneg (x + a)]
      have hexponent :
          -(2 * A) * (|x| + |x + a|) ≤ -A * (|a| + |x|) := by
        nlinarith
      calc
        ‖(u : ℝ → ℂ) x‖ * ‖(u : ℝ → ℂ) (x + a)‖ ≤
            (C * Real.exp (-(2 * A) * |x|)) *
              (C * Real.exp (-(2 * A) * |x + a|)) := hprod
        _ = C ^ (2 : ℕ) * Real.exp (-(2 * A) * (|x| + |x + a|)) := by
          rw [show (C * Real.exp (-(2 * A) * |x|)) *
              (C * Real.exp (-(2 * A) * |x + a|)) =
              C ^ (2 : ℕ) * (Real.exp (-(2 * A) * |x|) *
                Real.exp (-(2 * A) * |x + a|)) by ring,
            ← Real.exp_add]
          apply congrArg (fun y : ℝ => C ^ (2 : ℕ) * Real.exp y)
          ring
        _ ≤ C ^ (2 : ℕ) * Real.exp (-A * (|a| + |x|)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (sq_nonneg C)
        _ = (C ^ (2 : ℕ) * Real.exp (-A * |a|)) * Real.exp (-(A * |x|)) := by
          rw [show -A * (|a| + |x|) = -A * |a| + -(A * |x|) by ring,
            Real.exp_add]
          ring
    _ = B * Real.exp (-A * |a|) := by
      rw [integral_const_mul]
      dsimp only [B, J]
      ring

/-- The diagonal Floquet/von-Mangoldt identity is unconditional on the literal all-weight Meyer
target; its former decay premise is a theorem of that target. -/
theorem deningerCriticalFloquetForm_eq_vonMangoldtAutocorrelationCurrent_unconditional
    (u : DeningerMeyerStrongLogTarget) :
    deningerCriticalFloquetForm u =
      deningerVonMangoldtAutocorrelationCurrent u := by
  obtain ⟨B, hB, hbound⟩ :=
    exists_deningerAutocorrelationExpBound u (A := 2) (by norm_num)
  exact deningerCriticalFloquetForm_eq_vonMangoldtAutocorrelationCurrent
    u (by norm_num) hB hbound

/-- Polarized critical Floquet form.  This is the sesquilinear cross term recovered from four
diagonal forms. -/
def deningerCriticalFloquetCrossForm
    (u v : DeningerMeyerStrongLogTarget) : ℂ :=
  (1 / 4 : ℂ) *
    (deningerCriticalFloquetForm (u + v) -
      deningerCriticalFloquetForm (u - v) +
      I * deningerCriticalFloquetForm (u + I • v) -
      I * deningerCriticalFloquetForm (u - I • v))

/-- Polarized natural-number von-Mangoldt cross current. -/
def deningerVonMangoldtCrossCurrent
    (u v : DeningerMeyerStrongLogTarget) : ℂ :=
  (1 / 4 : ℂ) *
    (deningerVonMangoldtAutocorrelationCurrent (u + v) -
      deningerVonMangoldtAutocorrelationCurrent (u - v) +
      I * deningerVonMangoldtAutocorrelationCurrent (u + I • v) -
      I * deningerVonMangoldtAutocorrelationCurrent (u - I • v))

/-- **C36 capstone: unconditional cross-current identity.**  Deninger's critical prime-circle
form extends exactly to the non-diagonal polarized source pair. -/
theorem deningerCriticalFloquetCrossForm_eq_vonMangoldtCrossCurrent
    (u v : DeningerMeyerStrongLogTarget) :
    deningerCriticalFloquetCrossForm u v =
      deningerVonMangoldtCrossCurrent u v := by
  simp only [deningerCriticalFloquetCrossForm, deningerVonMangoldtCrossCurrent]
  rw [deningerCriticalFloquetForm_eq_vonMangoldtAutocorrelationCurrent_unconditional,
    deningerCriticalFloquetForm_eq_vonMangoldtAutocorrelationCurrent_unconditional,
    deningerCriticalFloquetForm_eq_vonMangoldtAutocorrelationCurrent_unconditional,
    deningerCriticalFloquetForm_eq_vonMangoldtAutocorrelationCurrent_unconditional]

end

end RHTower
