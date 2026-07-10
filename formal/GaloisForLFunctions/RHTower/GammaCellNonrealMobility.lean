import GaloisForLFunctions.RHTower.DegreeZeroNonrealOffline
import GaloisForLFunctions.RHTower.GammaCellDegreeZeroAction
import GaloisForLFunctions.RHTower.ZetaRealStrip

/-!
# Real-zero-free nonreal mobility in the gamma-completed cell

The positive structural statement is that the zeta-bearing gamma cell realizes a nonreal off-line
mobility action while remaining zero-free on the real open strip.  Multiplying zeta by the positive
reciprocal quartic preserves the cell, introduces no real strip zero, and plants an explicit
nonreal off-line zero.  Thus the surviving research question is constructive: identify the extra
primitive-source constraint that is not preserved by this degree-zero action.
-/

open Complex

namespace RHTower

noncomputable section

private theorem dzoQuartic_gamma_fe (s : ℂ) :
    (16 : ℂ) ^ (2 * (1 - s) - 1) * dzoQuartic (1 - s) =
      (16 : ℂ) ^ (2 * s - 1) * dzoQuartic s := by
  have h16 : (16 : ℂ) ≠ 0 := by norm_num
  have hrefl : dzoQuartic (1 - s) =
      (16 : ℂ) ^ (4 * s - 2) * dzoQuartic s := by
    rw [dzoQuartic_fe s, ← mul_assoc, ← Complex.cpow_add _ _ h16,
      show (4 * s - 2) + (2 - 4 * s) = (0 : ℂ) by ring,
      Complex.cpow_zero, one_mul]
  rw [hrefl, ← mul_assoc, ← Complex.cpow_add _ _ h16]
  congr 2
  ring

/-- The positive reciprocal quartic belongs to the gamma-completed cell. -/
theorem dzoQuartic_mem_gammaFECell : GammaFECell dzoQuartic :=
  ⟨dzoQuarticCoeff, dzoQuarticCoeff_multiplicative, dzoQuarticCoeff_integral,
    fun s _ => dzoQuarticCoeff_summable s,
    fun s _ => (LSeries_dzoQuarticCoeff s).symm,
    fun s => (16 : ℂ) ^ (2 * s - 1),
    fun _ _ _ => Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num)),
    fun s _ _ => dzoQuartic_gamma_fe s⟩

/-- The gamma cell is closed under multiplication by the positive reciprocal quartic. -/
theorem gammaFECell_mul_dzoQuartic {f : ℂ → ℂ} (hf : GammaFECell f) :
    GammaFECell (fun s => f s * dzoQuartic s) :=
  gammaFECell_mul_integralFEClass_of_exists_ne_zero hf dzoQuartic_mem_class
    ⟨0, dzoQuartic_ofReal_ne_zero 0⟩

/-- The all-prime zeta-bearing witness. -/
def zetaDzoQuartic (s : ℂ) : ℂ := riemannZeta s * dzoQuartic s

theorem zetaDzoQuartic_mem_gammaFECell : GammaFECell zetaDzoQuartic :=
  gammaFECell_mul_dzoQuartic zeta_mem_gammaFECell

/-- The witness has an explicit nonreal off-line zero strictly inside the critical strip. -/
theorem zetaDzoQuartic_nonreal_offline_strip_zero :
    zetaDzoQuartic ρdzoQuartic = 0 ∧
      0 < ρdzoQuartic.re ∧ ρdzoQuartic.re < 1 ∧
      ρdzoQuartic.re ≠ 1 / 2 ∧ ρdzoQuartic.im ≠ 0 := by
  refine ⟨?_, by linarith [ρdzoQuartic_mem_right_strip.1],
    ρdzoQuartic_mem_right_strip.2, ?_, ρdzoQuartic_not_real⟩
  · rw [zetaDzoQuartic, dzoQuartic_ρ_eq_zero, mul_zero]
  · rw [ρdzoQuartic_re]
    norm_num

/-- The zeta-bearing witness has no zero on the real open critical strip. -/
theorem zetaDzoQuartic_real_strip_ne_zero {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    zetaDzoQuartic (σ : ℂ) ≠ 0 := by
  rw [zetaDzoQuartic]
  exact mul_ne_zero (riemannZeta_real_strip_ne_zero h0 h1)
    (dzoQuartic_ofReal_ne_zero σ)

/-- A class realizes real-zero-free nonreal strip mobility when it contains a member with no real
open-strip zero and with a nonreal off-line open-strip zero. -/
def RealZeroFreeNonrealStripMobility (C : (ℂ → ℂ) → Prop) : Prop :=
  ∃ f : ℂ → ℂ, ∃ ρ : ℂ, C f ∧
    (∀ σ : ℝ, 0 < σ → σ < 1 → f (σ : ℂ) ≠ 0) ∧
    0 < ρ.re ∧ ρ.re < 1 ∧ ρ.im ≠ 0 ∧ f ρ = 0 ∧ ρ.re ≠ 1 / 2

/-- **Positive mobility theorem.** The gamma-completed integral-multiplicative cell contains an
all-prime zeta-bearing member that is zero-free on the real strip and has an explicit nonreal
off-line strip zero. -/
theorem gammaFECell_real_zero_free_nonreal_strip_mobility :
    RealZeroFreeNonrealStripMobility GammaFECell := by
  refine ⟨zetaDzoQuartic, ρdzoQuartic, zetaDzoQuartic_mem_gammaFECell,
    (fun _ h0 h1 => zetaDzoQuartic_real_strip_ne_zero h0 h1),
    by linarith [ρdzoQuartic_mem_right_strip.1],
    ρdzoQuartic_mem_right_strip.2, ρdzoQuartic_not_real,
    zetaDzoQuartic_nonreal_offline_strip_zero.1, ?_⟩
  rw [ρdzoQuartic_re]
  norm_num

/-- Selector-language corollary of the positive mobility theorem. -/
theorem gammaFECell_real_zero_free_mobility_precludes_uniform_line_selection :
    ¬ (∀ f : ℂ → ℂ, GammaFECell f →
      (∀ σ : ℝ, 0 < σ → σ < 1 → f (σ : ℂ) ≠ 0) →
      ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → ρ.im ≠ 0 → f ρ = 0 → ρ.re = 1 / 2) := by
  intro hforce
  have hline := hforce zetaDzoQuartic zetaDzoQuartic_mem_gammaFECell
    (fun _ h0 h1 => zetaDzoQuartic_real_strip_ne_zero h0 h1)
    ρdzoQuartic
    (by linarith [ρdzoQuartic_mem_right_strip.1])
    ρdzoQuartic_mem_right_strip.2 ρdzoQuartic_not_real
    zetaDzoQuartic_nonreal_offline_strip_zero.1
  rw [ρdzoQuartic_re] at hline
  norm_num at hline

end

end RHTower
