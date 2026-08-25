import GaloisForLFunctions.RHTower.CriticalPrimeFockScaledRadiusWindow
import GaloisForLFunctions.RHTower.CriticalPrimeFockAdaptedCellMass
import GaloisForLFunctions.HTGeometry.EventualPositiveSummabilityComparison

open Filter Topology

namespace RHTower

noncomputable section

def criticalPrimeFockScaledAdaptedCellMass (m s : ℝ) (n : ℕ) : ℝ :=
  let x := criticalPrimeFockAdaptedCellCenter m n
  primeLogWindowMass x (s * criticalPrimeFockRadius m x)

def criticalPrimeFockScaledAdaptedCellMain (m s : ℝ) (n : ℕ) : ℝ :=
  s * criticalPrimeFockAdaptedCellMain m n

theorem criticalPrimeFockScaledAdaptedCellMass_nonneg
    {s : ℝ} (hs : 0 ≤ s) (m : ℝ) (n : ℕ) :
    0 ≤ criticalPrimeFockScaledAdaptedCellMass m s n := by
  have hr : 0 ≤ s * criticalPrimeFockRadius m
      (criticalPrimeFockAdaptedCellCenter m n) := by
    exact mul_nonneg hs (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  unfold criticalPrimeFockScaledAdaptedCellMass
  dsimp only
  rw [primeLogWindowMass_eq_sum _ hr]
  exact Finset.sum_nonneg fun k _ => primeLogPowWeight_two_nonneg k

theorem criticalPrimeFockScaledAdaptedCellMain_pos
    {m s : ℝ} (hm : 0 < m) (hs : 0 < s) {n : ℕ} (hn : 0 < n) :
    0 < criticalPrimeFockScaledAdaptedCellMain m s n := by
  exact mul_pos hs (criticalPrimeFockAdaptedCellMain_pos hm hn)

theorem criticalPrimeFockAdaptedCellMain_nonneg (m : ℝ) (n : ℕ) :
    0 ≤ criticalPrimeFockAdaptedCellMain m n := by
  unfold criticalPrimeFockAdaptedCellMain criticalPrimeFockWindowMain
  exact mul_nonneg
    (mul_nonneg (by norm_num)
      (Real.rpow_nonneg (Nat.cast_nonneg n) (2 / m)))
    (Real.rpow_nonneg (Real.sqrt_nonneg _) _)

theorem criticalPrimeFockScaledAdaptedCellMain_nonneg
    {s : ℝ} (hs : 0 ≤ s) (m : ℝ) (n : ℕ) :
    0 ≤ criticalPrimeFockScaledAdaptedCellMain m s n := by
  exact mul_nonneg hs (criticalPrimeFockAdaptedCellMain_nonneg m n)

theorem rpow_criticalPrimeFockScaledAdaptedCellMass_eq_ratio_mul_main
    {m s q : ℝ} (hm : 0 < m) (hs : 0 < s) {n : ℕ} (hn : 0 < n) :
    criticalPrimeFockScaledAdaptedCellMass m s n ^ q =
      (criticalPrimeFockScaledAdaptedCellMass m s n /
        criticalPrimeFockScaledAdaptedCellMain m s n) ^ q *
          criticalPrimeFockScaledAdaptedCellMain m s n ^ q := by
  have hmain : 0 < criticalPrimeFockScaledAdaptedCellMain m s n :=
    criticalPrimeFockScaledAdaptedCellMain_pos hm hs hn
  rw [← Real.mul_rpow
      (div_nonneg (criticalPrimeFockScaledAdaptedCellMass_nonneg hs.le m n) hmain.le)
        hmain.le,
    div_mul_cancel₀ _ hmain.ne']

theorem tendsto_criticalPrimeFockScaledAdaptedCellMass_div_main
    {m s : ℝ} (hm : 2 < m) (hs : 0 < s) (hs1 : s ≤ 1) :
    Tendsto (fun n : ℕ =>
      criticalPrimeFockScaledAdaptedCellMass m s n /
        criticalPrimeFockScaledAdaptedCellMain m s n) atTop (nhds 1) := by
  have h :=
    (tendsto_primeLogWindowMass_div_scaledCriticalPrimeFockModel hm hs hs1).comp
      (tendsto_criticalPrimeFockAdaptedCellCenter_atTop (by linarith : 0 < m))
  apply h.congr'
  filter_upwards [] with n
  dsimp [Function.comp_apply, criticalPrimeFockScaledAdaptedCellMass,
    criticalPrimeFockScaledAdaptedCellMain, criticalPrimeFockAdaptedCellMain,
    criticalPrimeFockWindowMain]
  congr 1
  ring

theorem eventually_criticalPrimeFockScaledAdaptedCellMass_ratio_bounds
    {m s : ℝ} (hm : 2 < m) (hs : 0 < s) (hs1 : s ≤ 1) :
    ∀ᶠ n : ℕ in atTop,
      (1 / 2 : ℝ) ≤ criticalPrimeFockScaledAdaptedCellMass m s n /
          criticalPrimeFockScaledAdaptedCellMain m s n ∧
        criticalPrimeFockScaledAdaptedCellMass m s n /
          criticalPrimeFockScaledAdaptedCellMain m s n ≤ 3 / 2 := by
  have hratio := tendsto_criticalPrimeFockScaledAdaptedCellMass_div_main hm hs hs1
  filter_upwards [hratio.eventually (Ioo_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)
    (by norm_num : (1 : ℝ) < 3 / 2))] with n hn
  exact ⟨hn.1.le, hn.2.le⟩

theorem summable_rpow_criticalPrimeFockScaledAdaptedCellMain_iff
    {m s q : ℝ} (hs : 0 < s) :
    Summable (fun n : ℕ => criticalPrimeFockScaledAdaptedCellMain m s n ^ q) ↔
      Summable (fun n : ℕ => criticalPrimeFockAdaptedCellMain m n ^ q) := by
  have hfun : (fun n : ℕ => criticalPrimeFockScaledAdaptedCellMain m s n ^ q) =
      fun n : ℕ => s ^ q * criticalPrimeFockAdaptedCellMain m n ^ q := by
    funext n
    exact Real.mul_rpow hs.le (criticalPrimeFockAdaptedCellMain_nonneg m n)
  rw [hfun, summable_mul_left_iff (Real.rpow_pos_of_pos hs q).ne']

theorem summable_rpow_criticalPrimeFockScaledAdaptedCellMass_iff_main
    {m s q : ℝ} (hm : 4 < m) (hs : 0 < s) (hs1 : s ≤ 1) (hq : 0 < q) :
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
    eventually_criticalPrimeFockScaledAdaptedCellMass_ratio_bounds
      (by linarith : 2 < m) hs hs1] with n hn hratio
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

theorem summable_rpow_criticalPrimeFockScaledAdaptedCellMass_iff
    {m s q : ℝ} (hm : 4 < m) (hs : 0 < s) (hs1 : s ≤ 1) (hq : 0 < q) :
    Summable (fun n : ℕ => criticalPrimeFockScaledAdaptedCellMass m s n ^ q) ↔
      criticalPrimeFockSchattenThreshold m < q :=
  (summable_rpow_criticalPrimeFockScaledAdaptedCellMass_iff_main hm hs hs1 hq).trans
    ((summable_rpow_criticalPrimeFockScaledAdaptedCellMain_iff hs).trans
      (summable_rpow_criticalPrimeFockAdaptedCellMain_iff hm hq))

end

end RHTower

