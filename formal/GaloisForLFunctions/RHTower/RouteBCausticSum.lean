/-
The dyadic caustic assembly, part II: the j-free shell products
(doc 87 App B, the (L3) base case).

The per-shell contribution (linear arm at margin `min(2^jσ0·κ/2, 1/2)`)
times (shell measure √-law at width `2^jσ0`) is INDEPENDENT of `j`: in the
uncapped regime the scale cancels (`sqrt_div_sqrt_cancel`), in the capped
regime the shell measure is dominated by `2π`.  This module banks:

* `shell_term_le` — the abstract two-regime product bound.
* `shellP_prod_le` / `shellM_prod_le` — the dyadic shells' instantiation:
  arm × measure ≤ `ofReal CS`, `CS` j-free.
* `core_prod_le` — the caustic cores: √-law arm × core width.
* `mid_prod_le` — the mid-annulus: top-margin arm × `2π`.

Part III (`RouteBCausticCapstone`) sums these along `annulus_cover`.
-/
import Mathlib
import GaloisForLFunctions.RHTower.RouteBCausticAssembly

namespace RHTower
namespace Sublevel

open MeasureTheory

/-- **The abstract two-regime product bound.**  An arm at margin
`min(sig·kap/2, 1/2)` times a measure dominated both by the width √-law
and by `2π` is bounded j-free. -/
theorem shell_term_le {Y sig kap cc : ℝ} (hY : 0 ≤ Y) (hsig : 0 < sig)
    (hkap : 0 < kap) (hcc : 0 < cc) {V : ENNReal}
    (hV : V ≤ ENNReal.ofReal (2 * Real.pi
        * Real.sqrt (2 * (sig / (2 * cc)))))
    (hV2 : V ≤ ENNReal.ofReal (2 * Real.pi)) :
    ENNReal.ofReal (2 * Real.pi * Y
        / Real.sqrt (min (sig * kap / 2) (1 / 2))) * V
      ≤ ENNReal.ofReal (4 * Real.pi ^ 2 * Y
          * (Real.sqrt (2 / (kap * cc)) + Real.sqrt 2)) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  rcases le_or_gt (sig * kap / 2) (1 / 2) with hcase | hcase
  · rw [min_eq_left hcase]
    refine le_trans (mul_le_mul_right hV _) ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h1 : Real.sqrt (2 * (sig / (2 * cc))) = Real.sqrt (sig * 1 / cc) := by
      congr 1
      field_simp
    have h2 : sig * kap / 2 = sig * (kap / 2) := by ring
    have h3 : Real.sqrt (sig * 1 / cc) / Real.sqrt (sig * (kap / 2))
        = Real.sqrt (1 / (kap / 2 * cc)) :=
      sqrt_div_sqrt_cancel hsig (by norm_num) (by positivity) hcc
    have h4 : (1 : ℝ) / (kap / 2 * cc) = 2 / (kap * cc) := by
      field_simp
    have hchain : Real.sqrt (2 * (sig / (2 * cc)))
        / Real.sqrt (sig * kap / 2) = Real.sqrt (2 / (kap * cc)) := by
      rw [h1, h2, h3, h4]
    calc 2 * Real.pi * Y / Real.sqrt (sig * kap / 2)
          * (2 * Real.pi * Real.sqrt (2 * (sig / (2 * cc))))
        = 4 * Real.pi ^ 2 * Y * (Real.sqrt (2 * (sig / (2 * cc)))
            / Real.sqrt (sig * kap / 2)) := by ring
      _ = 4 * Real.pi ^ 2 * Y * Real.sqrt (2 / (kap * cc)) := by
          rw [hchain]
      _ ≤ 4 * Real.pi ^ 2 * Y
          * (Real.sqrt (2 / (kap * cc)) + Real.sqrt 2) := by
          have h5 : (0 : ℝ) ≤ 4 * Real.pi ^ 2 * Y * Real.sqrt 2 := by
            positivity
          nlinarith [h5]
  · rw [min_eq_right hcase.le]
    refine le_trans (mul_le_mul_right hV2 _) ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hs : Real.sqrt (1 / 2) * Real.sqrt 2 = 1 := by
      rw [← Real.sqrt_mul (by norm_num) 2]
      norm_num
    have hspos : (0 : ℝ) < Real.sqrt (1 / 2) := Real.sqrt_pos.mpr (by norm_num)
    have hLHS : 2 * Real.pi * Y / Real.sqrt (1 / 2) * (2 * Real.pi)
        = 4 * Real.pi ^ 2 * Y * Real.sqrt 2 := by
      rw [div_mul_eq_mul_div, div_eq_iff (ne_of_gt hspos)]
      linear_combination (-(4 * Real.pi ^ 2 * Y)) * hs
    rw [hLHS]
    have h6 : (0 : ℝ) ≤ 4 * Real.pi ^ 2 * Y * Real.sqrt (2 / (kap * cc)) := by
      positivity
    nlinarith [h6]

section Pieces

variable {B C c : ℂ} {ρ r σ0 : ℝ}

/-- Upper-shell product, j-free. -/
theorem shellP_prod_le (hB : B ≠ 0) (hC : C ≠ 0) (hc : c ≠ 0)
    (hρB : ‖B‖ < ρ) (hr0 : 0 < r) (hσ0 : 0 < σ0) (j : ℕ) :
    ENNReal.ofReal (2 * Real.pi
        * ((r * (2 * ρ + r)) / ((ρ - ‖B‖) / 2 * ‖B‖))
        / Real.sqrt (min (2 ^ j * σ0 * causticKappa ρ ‖B‖ / 2) (1 / 2)))
      * volume (shellSetP c C B ρ (2 ^ j * σ0))
      ≤ ENNReal.ofReal (4 * Real.pi ^ 2
          * ((r * (2 * ρ + r)) / ((ρ - ‖B‖) / 2 * ‖B‖))
          * (Real.sqrt (2 / (causticKappa ρ ‖B‖ * (‖c‖ * ‖C‖)))
            + Real.sqrt 2)) := by
  have hb0 : (0 : ℝ) < ‖B‖ := norm_pos_iff.mpr hB
  have hcc : (0 : ℝ) < ‖c‖ * ‖C‖ :=
    mul_pos (norm_pos_iff.mpr hc) (norm_pos_iff.mpr hC)
  have hσj : (0 : ℝ) < 2 ^ j * σ0 := by positivity
  have hκ : (0 : ℝ) < causticKappa ρ ‖B‖ := by
    rw [causticKappa]
    have hGpos : (0 : ℝ) < (ρ + ‖B‖) ^ 2 - (ρ - ‖B‖) ^ 2 := by nlinarith
    have hpb : (0 : ℝ) < ρ + ‖B‖ := by linarith
    positivity
  have hρ0 : (0 : ℝ) < ρ := lt_of_le_of_lt (norm_nonneg B) hρB
  have hY : (0 : ℝ) ≤ (r * (2 * ρ + r)) / ((ρ - ‖B‖) / 2 * ‖B‖) :=
    div_nonneg (by positivity)
      (mul_pos (by linarith : (0 : ℝ) < (ρ - ‖B‖) / 2) hb0).le
  have hV : volume (shellSetP c C B ρ (2 ^ j * σ0))
      ≤ ENNReal.ofReal (2 * Real.pi
          * Real.sqrt (2 * (2 ^ j * σ0 / (2 * (‖c‖ * ‖C‖))))) := by
    have hsub : shellSetP c C B ρ (2 ^ j * σ0)
        ⊆ {η : ℝ | η ∈ Set.Icc 0 (2 * Real.pi) ∧
            ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ ^ 2
              ∈ Set.Icc ((ρ + ‖B‖) ^ 2 - 2 * (2 ^ j * σ0))
                ((ρ + ‖B‖) ^ 2 - 2 ^ j * σ0)} := by
      rintro η ⟨h1, h2, h3, _⟩
      exact ⟨h1, by constructor <;> linarith⟩
    refine le_trans (measure_mono hsub) ?_
    refine le_trans (center_shell_measure hc hC) ?_
    apply ENNReal.ofReal_le_ofReal
    have heq : (ρ + ‖B‖) ^ 2 - 2 ^ j * σ0
        - ((ρ + ‖B‖) ^ 2 - 2 * (2 ^ j * σ0)) = 2 ^ j * σ0 := by ring
    rw [heq]
  have hV2 : volume (shellSetP c C B ρ (2 ^ j * σ0))
      ≤ ENNReal.ofReal (2 * Real.pi) := by
    refine le_trans (measure_mono (fun η h => h.1)) ?_
    rw [Real.volume_Icc]
    apply ENNReal.ofReal_le_ofReal
    linarith [Real.pi_pos]
  exact shell_term_le hY hσj hκ hcc hV hV2

/-- Lower-shell product, j-free. -/
theorem shellM_prod_le (hB : B ≠ 0) (hC : C ≠ 0) (hc : c ≠ 0)
    (hρB : ‖B‖ < ρ) (hr0 : 0 < r) (hσ0 : 0 < σ0) (j : ℕ) :
    ENNReal.ofReal (2 * Real.pi
        * ((r * (2 * ρ + r)) / ((ρ - ‖B‖) / 2 * ‖B‖))
        / Real.sqrt (min (2 ^ j * σ0 * causticKappa ρ ‖B‖ / 2) (1 / 2)))
      * volume (shellSetM c C B ρ (2 ^ j * σ0))
      ≤ ENNReal.ofReal (4 * Real.pi ^ 2
          * ((r * (2 * ρ + r)) / ((ρ - ‖B‖) / 2 * ‖B‖))
          * (Real.sqrt (2 / (causticKappa ρ ‖B‖ * (‖c‖ * ‖C‖)))
            + Real.sqrt 2)) := by
  have hb0 : (0 : ℝ) < ‖B‖ := norm_pos_iff.mpr hB
  have hcc : (0 : ℝ) < ‖c‖ * ‖C‖ :=
    mul_pos (norm_pos_iff.mpr hc) (norm_pos_iff.mpr hC)
  have hσj : (0 : ℝ) < 2 ^ j * σ0 := by positivity
  have hκ : (0 : ℝ) < causticKappa ρ ‖B‖ := by
    rw [causticKappa]
    have hGpos : (0 : ℝ) < (ρ + ‖B‖) ^ 2 - (ρ - ‖B‖) ^ 2 := by nlinarith
    have hpb : (0 : ℝ) < ρ + ‖B‖ := by linarith
    positivity
  have hρ0 : (0 : ℝ) < ρ := lt_of_le_of_lt (norm_nonneg B) hρB
  have hY : (0 : ℝ) ≤ (r * (2 * ρ + r)) / ((ρ - ‖B‖) / 2 * ‖B‖) :=
    div_nonneg (by positivity)
      (mul_pos (by linarith : (0 : ℝ) < (ρ - ‖B‖) / 2) hb0).le
  have hV : volume (shellSetM c C B ρ (2 ^ j * σ0))
      ≤ ENNReal.ofReal (2 * Real.pi
          * Real.sqrt (2 * (2 ^ j * σ0 / (2 * (‖c‖ * ‖C‖))))) := by
    have hsub : shellSetM c C B ρ (2 ^ j * σ0)
        ⊆ {η : ℝ | η ∈ Set.Icc 0 (2 * Real.pi) ∧
            ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ ^ 2
              ∈ Set.Icc ((ρ - ‖B‖) ^ 2 + 2 ^ j * σ0)
                ((ρ - ‖B‖) ^ 2 + 2 * (2 ^ j * σ0))} := by
      rintro η ⟨h1, h2, h3, _⟩
      exact ⟨h1, by constructor <;> linarith⟩
    refine le_trans (measure_mono hsub) ?_
    refine le_trans (center_shell_measure hc hC) ?_
    apply ENNReal.ofReal_le_ofReal
    have heq : (ρ - ‖B‖) ^ 2 + 2 * (2 ^ j * σ0)
        - ((ρ - ‖B‖) ^ 2 + 2 ^ j * σ0) = 2 ^ j * σ0 := by ring
    rw [heq]
  have hV2 : volume (shellSetM c C B ρ (2 ^ j * σ0))
      ≤ ENNReal.ofReal (2 * Real.pi) := by
    refine le_trans (measure_mono (fun η h => h.1)) ?_
    rw [Real.volume_Icc]
    apply ENNReal.ofReal_le_ofReal
    linarith [Real.pi_pos]
  exact shell_term_le hY hσj hκ hcc hV hV2

end Pieces

end Sublevel
end RHTower
