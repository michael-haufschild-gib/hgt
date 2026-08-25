import GaloisForLFunctions.RHTower.CriticalPrimeFockArbitraryScaledRadiusWindow
import GaloisForLFunctions.RHTower.CriticalPrimeFockScaledAdaptedCellMass

open Filter Topology

namespace RHTower

noncomputable section

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

theorem summable_rpow_criticalPrimeFockScaledAdaptedCellMass_iff_of_pos
    {m s q : ℝ} (hm : 4 < m) (hs : 0 < s) (hq : 0 < q) :
    Summable (fun n : ℕ => criticalPrimeFockScaledAdaptedCellMass m s n ^ q) ↔
      criticalPrimeFockSchattenThreshold m < q :=
  (summable_rpow_criticalPrimeFockScaledAdaptedCellMass_iff_main_of_pos hm hs hq).trans
    ((summable_rpow_criticalPrimeFockScaledAdaptedCellMain_iff hs).trans
      (summable_rpow_criticalPrimeFockAdaptedCellMain_iff hm hq))

end

end RHTower
