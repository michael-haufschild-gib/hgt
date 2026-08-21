import GaloisForLFunctions.RHTower.ConnesPadicWeilKernel
import GaloisForLFunctions.RHTower.FieldOnePadicMultiplicativeHaarShellIntegral

/-!
# The local non-archimedean Weil integral as a sum over valuation shells

Appendix II (9)-(10) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

The local Weil term at a finite place is `∫_{k_v^*} f(u) |1-u|^{-1} d^*u`.  Off the unit
sphere the ultrametric equality `|1-u| = max(1,|u|)` makes the kernel *constant on each
valuation shell*, equal to `min(1, q^m)` on `|u| = q^{-m}`.  Combining this with the
multiplicative-Haar shell decomposition of `ℚ_p^*` turns the local integral into an explicit
series over `m ∈ ℤ`, which is the local factor `∑_n log p · p^{-n/2}` of the explicit formula.
-/

open MeasureTheory

namespace GaloisForLFunctions.RHTower

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- The valuation-unit chart is the explicit forward map `(m,u) ↦ p^m u`. -/
theorem fieldOnePadicValuationUnitContinuousMulEquiv_apply
    (z : Multiplicative ℤ × ℤ_[p]ˣ) :
    fieldOnePadicValuationUnitContinuousMulEquiv p z
      = fieldOnePadicValuationUnitForward p z := rfl

/-- The chart lands on the valuation shell `‖x‖ = p^{-m}`. -/
theorem connes_padic_shell_norm (m : ℤ) (u : ℤ_[p]ˣ) :
    ‖((fieldOnePadicValuationUnitContinuousMulEquiv p
        (Multiplicative.ofAdd m, u) : ℚ_[p]ˣ) : ℚ_[p])‖ = (p : ℝ) ^ (-m) := by
  have h0 : ((fieldOnePadicValuationUnitContinuousMulEquiv p
      (Multiplicative.ofAdd m, u) : ℚ_[p]ˣ) : ℚ_[p]) ≠ 0 := Units.ne_zero _
  rw [Padic.norm_eq_zpow_neg_valuation h0]
  congr 1
  rw [fieldOnePadicValuationUnitContinuousMulEquiv_apply]
  simpa using fieldOnePadic_valuation_forward p (Multiplicative.ofAdd m, u)

/-- **The Weil kernel is constant on every non-unit shell.** -/
theorem connes_padic_weilKernel_chart {m : ℤ} (hm : m ≠ 0) (u : ℤ_[p]ˣ) :
    ‖1 - ((fieldOnePadicValuationUnitContinuousMulEquiv p
        (Multiplicative.ofAdd m, u) : ℚ_[p]ˣ) : ℚ_[p])‖⁻¹ = min 1 ((p : ℝ) ^ m) :=
  connes_padic_weilKernel_shell hm (connes_padic_shell_norm p m u)

/-- **Integrability of the Weil-weighted one-shell function.** -/
theorem connes_padic_weil_integrable_singleShell
    (f : ℚ_[p]ˣ → ℂ) {m : ℤ} (hm : m ≠ 0) (g : ℤ_[p]ˣ → ℂ)
    (hg : Integrable g (fieldOnePadicUnitNormalizedHaar p))
    (hcoord : ∀ (k : ℤ) (u : ℤ_[p]ˣ),
      f (fieldOnePadicValuationUnitContinuousMulEquiv p
        (Multiplicative.ofAdd k, u)) = if k = m then g u else 0) :
    Integrable (fun a : ℚ_[p]ˣ => f a * ((‖1 - (a : ℚ_[p])‖⁻¹ : ℝ) : ℂ))
      (fieldOnePadicMultiplicativeHaar p) := by
  refine integrable_fieldOnePadicMultiplicativeHaar_of_singleShell p _ m
    (fun u => ((min 1 ((p : ℝ) ^ m) : ℝ) : ℂ) * g u) (hg.const_mul _) ?_
  intro k u
  by_cases hk : k = m
  · subst hk
    rw [hcoord k u, if_pos rfl, if_pos rfl, connes_padic_weilKernel_chart p hm u, mul_comm]
  · rw [hcoord k u, if_neg hk, if_neg hk, zero_mul]

/-- **Appendix II (9)/(10).**  The local Weil integral of a function carried by the single
valuation shell `‖u‖ = p^{-m}`, `m ≠ 0`, is the angular mass scaled by `min(1, p^m)`. -/
theorem connes_padic_weil_singleShell
    (f : ℚ_[p]ˣ → ℂ) {m : ℤ} (hm : m ≠ 0) (g : ℤ_[p]ˣ → ℂ)
    (hg : Integrable g (fieldOnePadicUnitNormalizedHaar p))
    (hcoord : ∀ (k : ℤ) (u : ℤ_[p]ˣ),
      f (fieldOnePadicValuationUnitContinuousMulEquiv p
        (Multiplicative.ofAdd k, u)) = if k = m then g u else 0) :
    ∫ a, f a * ((‖1 - (a : ℚ_[p])‖⁻¹ : ℝ) : ℂ) ∂fieldOnePadicMultiplicativeHaar p
      = ((min 1 ((p : ℝ) ^ m) : ℝ) : ℂ) * ∫ u, g u ∂fieldOnePadicUnitNormalizedHaar p := by
  have hshell := fieldOnePadicMultiplicativeHaar_integral_singleShell p
    (fun a : ℚ_[p]ˣ => f a * ((‖1 - (a : ℚ_[p])‖⁻¹ : ℝ) : ℂ)) m
    (fun u => ((min 1 ((p : ℝ) ^ m) : ℝ) : ℂ) * g u) (hg.const_mul _) ?_
  · rw [hshell, integral_const_mul]
  · intro k u
    by_cases hk : k = m
    · subst hk
      rw [hcoord k u, if_pos rfl, if_pos rfl, connes_padic_weilKernel_chart p hm u, mul_comm]
    · rw [hcoord k u, if_neg hk, if_neg hk, zero_mul]

/-- **The local Weil integral as a series over valuation shells.**  Every shell other than the
unit sphere contributes its angular mass times the constant `min(1, p^m)`; the unit sphere is
the shell where the kernel is singular and is governed by Connes' principal-value
normalization. -/
theorem connes_padic_weil_integral_eq_tsum (f : ℚ_[p]ˣ → ℂ)
    (hf : Integrable (fun a : ℚ_[p]ˣ => f a * ((‖1 - (a : ℚ_[p])‖⁻¹ : ℝ) : ℂ))
      (fieldOnePadicMultiplicativeHaar p)) :
    ∫ a, f a * ((‖1 - (a : ℚ_[p])‖⁻¹ : ℝ) : ℂ) ∂fieldOnePadicMultiplicativeHaar p
      = ∑' m : Multiplicative ℤ,
          if m.toAdd = 0 then
            ∫ u : ℤ_[p]ˣ,
              f (fieldOnePadicValuationUnitContinuousMulEquiv p (m, u)) *
                ((‖1 - ((fieldOnePadicValuationUnitContinuousMulEquiv p (m, u) :
                  ℚ_[p]ˣ) : ℚ_[p])‖⁻¹ : ℝ) : ℂ) ∂fieldOnePadicUnitNormalizedHaar p
          else
            ((min 1 ((p : ℝ) ^ m.toAdd) : ℝ) : ℂ) *
              ∫ u : ℤ_[p]ˣ, f (fieldOnePadicValuationUnitContinuousMulEquiv p (m, u))
                ∂fieldOnePadicUnitNormalizedHaar p := by
  rw [fieldOnePadicMultiplicativeHaar_integral_eq_tsum p _ hf]
  refine tsum_congr fun m => ?_
  by_cases hm : m.toAdd = 0
  · rw [if_pos hm]
  · rw [if_neg hm, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have hrep : m = Multiplicative.ofAdd m.toAdd := rfl
    rw [hrep]
    dsimp only
    rw [connes_padic_weilKernel_chart p hm u, mul_comm]
    rfl

end

end GaloisForLFunctions.RHTower
