import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# A power tail faster than the square-root threshold is square integrable

A profile bounded by `C L^{-p}` on a terminal ray has finite squared mass there exactly through
`p > 1/2`, because the square is `C² L^{-2p}` and `-2p < -1`.  Stated in the extended norm, so no
measurability or integrability hypothesis on the profile is needed: the bound alone gives the
conclusion.

This is what converts the decay rates of a grade-one profile — `L^{-3/2}` for the value and its
first derivative, `L^{-5/2}` for the second — into membership of `L²` and `H¹` on a terminal ray.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {A : Type*} [NormedAddCommGroup A]

/-- The squared power tail is integrable past any positive radius exactly through the square-root
threshold. -/
theorem integrableOn_sq_powerTail {p L₀ : ℝ} (hL₀ : 0 < L₀) (hp : 1 / 2 < p) :
    IntegrableOn (fun L : ℝ => L ^ (-(2 * p))) (Ioi L₀) volume :=
  (integrableOn_Ioi_rpow_iff hL₀).mpr (by linarith)

/-- **A power tail beyond the square-root threshold has finite squared mass.** -/
theorem lintegral_sq_powerTail_ne_top {f : ℝ → A} {C p L₀ : ℝ}
    (hL₀ : 0 < L₀) (hp : 1 / 2 < p)
    (hf : ∀ L ∈ Ioi L₀, ‖f L‖ ≤ C * L ^ (-p)) :
    (∫⁻ L in Ioi L₀, ‖f L‖ₑ ^ 2) ≠ ⊤ := by
  have hmaj : ∀ L ∈ Ioi L₀, ‖f L‖ₑ ^ 2 ≤ ENNReal.ofReal (C ^ 2 * L ^ (-(2 * p))) := by
    intro L hL
    have hLpos : (0 : ℝ) < L := lt_trans hL₀ hL
    have hsq : ‖f L‖ ^ 2 ≤ C ^ 2 * L ^ (-(2 * p)) := by
      have hbase := hf L hL
      have hnn : (0 : ℝ) ≤ C * L ^ (-p) := le_trans (norm_nonneg _) hbase
      have hstep : ‖f L‖ ^ 2 ≤ (C * L ^ (-p)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hbase 2
      refine hstep.trans (le_of_eq ?_)
      rw [mul_pow, ← Real.rpow_natCast (L ^ (-p)) 2, ← Real.rpow_mul hLpos.le]
      congr 2
      push_cast
      ring
    calc ‖f L‖ₑ ^ 2 = ENNReal.ofReal (‖f L‖ ^ 2) := by
          rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      _ ≤ ENNReal.ofReal (C ^ 2 * L ^ (-(2 * p))) := ENNReal.ofReal_le_ofReal hsq
  have hint : IntegrableOn (fun L : ℝ => C ^ 2 * L ^ (-(2 * p))) (Ioi L₀) volume :=
    (integrableOn_sq_powerTail hL₀ hp).const_mul (C ^ 2)
  have hfin : (∫⁻ L in Ioi L₀, ENNReal.ofReal (C ^ 2 * L ^ (-(2 * p)))) ≠ ⊤ := by
    have hnn : ∀ᵐ L ∂(volume.restrict (Ioi L₀)), 0 ≤ C ^ 2 * L ^ (-(2 * p)) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with L hL
      have hLpos : (0 : ℝ) < L := lt_trans hL₀ hL
      positivity
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
    exact ENNReal.ofReal_ne_top
  exact ne_top_of_le_ne_top hfin (setLIntegral_mono' measurableSet_Ioi hmaj)

end GaloisForLFunctions.HTGeometry
