import GaloisForLFunctions.RHTower.CriticalPrimeFockArbitraryScaledRadiusWindow
import GaloisForLFunctions.RHTower.CriticalPrimeFockScaledAdaptedCellMass

/-!
# Schatten summability of scaled adapted-cell prime masses (arbitrary scale `s > 0`)

Extends `CriticalPrimeFockScaledAdaptedCellMass` from `0 < s ≤ 1` to every scale `s > 0`. The
prime-log mass of the window of radius `s r(x_n)` around the cell centre `x_n = n^(2/m)` is
asymptotic to its main term `s · 2 x_n r(x_n)`, and for `m > 4`, `q > 0` the masses are
`q`-summable iff `q > m/(m - 4)`.

## Main results

- `tendsto_criticalPrimeFockScaledAdaptedCellMass_div_main_of_pos`: for `m > 2`, `s > 0`,
  mass/main → 1.
- `summable_rpow_criticalPrimeFockScaledAdaptedCellMass_iff_main_of_pos`: for `m > 4`, `s > 0`,
  `q > 0`, masses and main terms are `q`-summable together.
- `summable_rpow_criticalPrimeFockScaledAdaptedCellMass_iff_of_pos`: for `m > 4`, `s > 0`,
  `q > 0`, `∑ mass_n^q < ∞ ↔ m/(m - 4) < q`.

## Hypotheses

Unconditional; only the parameter ranges are assumed.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- For `m > 2` and any `s > 0`, the scaled adapted-cell mass divided by its main term tends to `1`. -/
theorem tendsto_criticalPrimeFockScaledAdaptedCellMass_div_main_of_pos
    {m s : ℝ} (hm : 2 < m) (hs : 0 < s) :
    Tendsto (fun n : ℕ =>
      criticalPrimeFockScaledAdaptedCellMass m s n /
        criticalPrimeFockScaledAdaptedCellMain m s n) atTop (nhds 1) := by
  have h :=
    (tendsto_primeLogWindowMass_div_scaledCriticalPrimeFockModel_of_pos hm hs).comp
      (tendsto_criticalPrimeFockAdaptedCellCenter_atTop (by linarith : 0 < m))
  apply h.congr'
  filter_upwards [] with n
  dsimp [Function.comp_apply, criticalPrimeFockScaledAdaptedCellMass,
    criticalPrimeFockScaledAdaptedCellMain, criticalPrimeFockAdaptedCellMain,
    criticalPrimeFockWindowMain]
  congr 1
  ring

/-- For `m > 2` and any `s > 0`, eventually `1/2 ≤ mass/main ≤ 3/2`. -/
theorem eventually_criticalPrimeFockScaledAdaptedCellMass_ratio_bounds_of_pos
    {m s : ℝ} (hm : 2 < m) (hs : 0 < s) :
    ∀ᶠ n : ℕ in atTop,
      (1 / 2 : ℝ) ≤ criticalPrimeFockScaledAdaptedCellMass m s n /
          criticalPrimeFockScaledAdaptedCellMain m s n ∧
        criticalPrimeFockScaledAdaptedCellMass m s n /
          criticalPrimeFockScaledAdaptedCellMain m s n ≤ 3 / 2 := by
  have hratio := tendsto_criticalPrimeFockScaledAdaptedCellMass_div_main_of_pos hm hs
  filter_upwards [hratio.eventually (Ioo_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)
    (by norm_num : (1 : ℝ) < 3 / 2))] with n hn
  exact ⟨hn.1.le, hn.2.le⟩

/-- For `m > 4`, `s > 0`, `q > 0`, the `q`-th powers of scaled cell masses are summable iff those of the
main terms are. -/
theorem summable_rpow_criticalPrimeFockScaledAdaptedCellMass_iff_main_of_pos
    {m s q : ℝ} (hm : 4 < m) (hs : 0 < s) (hq : 0 < q) :
    Summable (fun n : ℕ => criticalPrimeFockScaledAdaptedCellMass m s n ^ q) ↔
      Summable (fun n : ℕ => criticalPrimeFockScaledAdaptedCellMain m s n ^ q) := by
  apply HTGeometry.summable_iff_of_eventually_nat_mul_le_of_le
    (fun n : ℕ => criticalPrimeFockScaledAdaptedCellMain m s n ^ q)
    (fun n : ℕ => criticalPrimeFockScaledAdaptedCellMass m s n ^ q)
    (fun n => Real.rpow_nonneg
      (criticalPrimeFockScaledAdaptedCellMain_nonneg hs.le m n) _)
    (fun n => Real.rpow_nonneg
      (criticalPrimeFockScaledAdaptedCellMass_nonneg hs.le m n) _)
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2) q)
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    eventually_criticalPrimeFockScaledAdaptedCellMass_ratio_bounds_of_pos
      (by linarith : 2 < m) hs] with n hn hratio
  have heq := rpow_criticalPrimeFockScaledAdaptedCellMass_eq_ratio_mul_main
    (m := m) (s := s) (q := q) (by linarith : 0 < m) hs hn
  have hmainnonneg : 0 ≤ criticalPrimeFockScaledAdaptedCellMain m s n ^ q :=
    Real.rpow_nonneg (criticalPrimeFockScaledAdaptedCellMain_pos
      (by linarith : 0 < m) hs hn).le q
  rw [heq]
  constructor
  · exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (by norm_num) hratio.1 hq.le) hmainnonneg
  · exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) hratio.1)
        hratio.2 hq.le) hmainnonneg

/-- Schatten threshold for every scale: for `m > 4`, `s > 0`, `q > 0`, the scaled adapted-cell masses are
`q`-summable iff `q > m/(m - 4)`. -/
theorem summable_rpow_criticalPrimeFockScaledAdaptedCellMass_iff_of_pos
    {m s q : ℝ} (hm : 4 < m) (hs : 0 < s) (hq : 0 < q) :
    Summable (fun n : ℕ => criticalPrimeFockScaledAdaptedCellMass m s n ^ q) ↔
      criticalPrimeFockSchattenThreshold m < q :=
  (summable_rpow_criticalPrimeFockScaledAdaptedCellMass_iff_main_of_pos hm hs hq).trans
    ((summable_rpow_criticalPrimeFockScaledAdaptedCellMain_iff hs).trans
      (summable_rpow_criticalPrimeFockAdaptedCellMain_iff hm hq))

end

end RHTower
