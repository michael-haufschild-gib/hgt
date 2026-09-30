import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Quantitative stability of the central paired-eta quotient

A complete denominator with norm greater than `1 / 8` and value error at
most `1 / 16` gives a strict finite denominator floor of `1 / 16`. Keeping
the value and derivative errors separate gives the quotient error
`16 * δ1 + 2048 * δ0` when the complete derivative has norm at most `16`.

These are pointwise complex inequalities: the derivative values are arbitrary
complex inputs. The calibrated corollary substitutes the literal paired-eta
tail envelopes and retains the exact coefficient `6400 + 48 * log (2N+1)`.
It assumes those tail inequalities and has no dependency on their source proof.
-/

namespace RHTower

/-- A strict complete denominator floor survives the calibrated value error. -/
theorem liClockPairedEtaFinite_norm_gt_one_sixteenth
    {E EN : ℂ} {δ0 : ℝ}
    (hE : (1 / 8 : ℝ) < ‖E‖)
    (herror : ‖EN - E‖ ≤ δ0) (hsmall : δ0 ≤ 1 / 16) :
    (1 / 16 : ℝ) < ‖EN‖ := by
  have hnorm := norm_sub_norm_le E EN
  rw [norm_sub_rev E EN] at hnorm
  linarith

/-- Separate derivative and value errors give the exact central quotient bound. -/
theorem liClockPairedEtaQuotient_norm_sub_le
    {E Ederiv EN ENderiv : ℂ} {δ0 δ1 : ℝ}
    (hE : (1 / 8 : ℝ) < ‖E‖)
    (herror : ‖EN - E‖ ≤ δ0) (hsmall : δ0 ≤ 1 / 16)
    (hderiv : ‖Ederiv‖ ≤ 16) (hderror : ‖ENderiv - Ederiv‖ ≤ δ1) :
    ‖ENderiv / EN - Ederiv / E‖ ≤ 16 * δ1 + 2048 * δ0 := by
  have hEN := liClockPairedEtaFinite_norm_gt_one_sixteenth hE herror hsmall
  have hEpos : 0 < ‖E‖ := lt_trans (by norm_num) hE
  have hENpos : 0 < ‖EN‖ := lt_trans (by norm_num) hEN
  have hEne : E ≠ 0 := norm_pos_iff.mp hEpos
  have hENne : EN ≠ 0 := norm_pos_iff.mp hENpos
  have hδ0 : 0 ≤ δ0 := (norm_nonneg _).trans herror
  have hδ1 : 0 ≤ δ1 := (norm_nonneg _).trans hderror
  have herror' : ‖E - EN‖ ≤ δ0 := by
    rw [norm_sub_rev E EN]
    exact herror
  have hfirst : ‖ENderiv - Ederiv‖ / ‖EN‖ ≤ 16 * δ1 := by
    apply (div_le_iff₀ hENpos).2
    have hmul := mul_le_mul_of_nonneg_left hEN.le hδ1
    nlinarith
  have hprodpos : 0 < ‖EN‖ * ‖E‖ := mul_pos hENpos hEpos
  have hprod : (1 / 128 : ℝ) ≤ ‖EN‖ * ‖E‖ := by
    have h := mul_le_mul hEN.le hE.le (by norm_num) (norm_nonneg EN)
    norm_num at h ⊢
    exact h
  have hcoeff : 16 / (‖EN‖ * ‖E‖) ≤ (2048 : ℝ) := by
    apply (div_le_iff₀ hprodpos).2
    nlinarith
  have hsecond : ‖Ederiv‖ * ‖E - EN‖ / (‖EN‖ * ‖E‖) ≤ 2048 * δ0 := by
    calc
      ‖Ederiv‖ * ‖E - EN‖ / (‖EN‖ * ‖E‖) ≤
          (16 * δ0) / (‖EN‖ * ‖E‖) :=
        div_le_div_of_nonneg_right
          (mul_le_mul hderiv herror' (norm_nonneg _) (by norm_num)) hprodpos.le
      _ = δ0 * (16 / (‖EN‖ * ‖E‖)) := by ring
      _ ≤ δ0 * 2048 := mul_le_mul_of_nonneg_left hcoeff hδ0
      _ = 2048 * δ0 := by ring
  have hidentity : ENderiv / EN - Ederiv / E =
      (ENderiv - Ederiv) / EN + Ederiv * ((E - EN) / (EN * E)) := by
    field_simp [hEne, hENne]
    ring
  calc
    ‖ENderiv / EN - Ederiv / E‖ =
        ‖(ENderiv - Ederiv) / EN + Ederiv * ((E - EN) / (EN * E))‖ := by
      rw [hidentity]
    _ ≤ ‖(ENderiv - Ederiv) / EN‖ + ‖Ederiv * ((E - EN) / (EN * E))‖ :=
      norm_add_le _ _
    _ = ‖ENderiv - Ederiv‖ / ‖EN‖ +
        ‖Ederiv‖ * ‖E - EN‖ / (‖EN‖ * ‖E‖) := by
      rw [norm_div, norm_mul, norm_div, norm_mul]
      ring
    _ ≤ 16 * δ1 + 2048 * δ0 := add_le_add hfirst hsecond

/-- Substituting the literal eta tail bounds preserves the calibrated coefficient. -/
theorem liClockPairedEtaQuotient_norm_sub_le_calibrated
    {E Ederiv EN ENderiv : ℂ} (N : ℕ)
    (hE : (1 / 8 : ℝ) < ‖E‖)
    (herror : ‖EN - E‖ ≤ 3 * (((2 * N + 1 : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))))
    (hsmall : 3 * (((2 * N + 1 : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))) ≤ 1 / 16)
    (hderiv : ‖Ederiv‖ ≤ 16)
    (hderror : ‖ENderiv - Ederiv‖ ≤
      (16 + 3 * Real.log ((2 * N + 1 : ℕ) : ℝ)) *
        (((2 * N + 1 : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)))) :
    ‖ENderiv / EN - Ederiv / E‖ ≤
      (6400 + 48 * Real.log ((2 * N + 1 : ℕ) : ℝ)) *
        (((2 * N + 1 : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))) := by
  calc
    ‖ENderiv / EN - Ederiv / E‖ ≤
        16 * ((16 + 3 * Real.log ((2 * N + 1 : ℕ) : ℝ)) *
          (((2 * N + 1 : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)))) +
        2048 * (3 * (((2 * N + 1 : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)))) :=
      liClockPairedEtaQuotient_norm_sub_le hE herror hsmall hderiv hderror
    _ = _ := by ring

end RHTower
