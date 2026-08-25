import GaloisForLFunctions.RHTower.CriticalPrimeFockWindowPhaseTransition
import GaloisForLFunctions.RHTower.CriticalPrimeFockSchattenExponent
import GaloisForLFunctions.HTGeometry.PositiveSummabilityComparison

open Filter Topology

namespace RHTower

noncomputable section

/-- One point per unit cell of the polynomial-Fock adapted metric on the positive prime-log ray. -/
def criticalPrimeFockAdaptedCellCenter (m : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (2 / m)

/-- Exact prime-log mass in the adapted window centered at the `n`-th metric cell. -/
def criticalPrimeFockAdaptedCellMass (m : ℝ) (n : ℕ) : ℝ :=
  let x := criticalPrimeFockAdaptedCellCenter m n
  primeLogWindowMass x (criticalPrimeFockRadius m x)

/-- Main term for the exact prime-log mass in the `n`-th adapted cell. -/
def criticalPrimeFockAdaptedCellMain (m : ℝ) (n : ℕ) : ℝ :=
  criticalPrimeFockWindowMain m (criticalPrimeFockAdaptedCellCenter m n)

/-- Power-law exponent of the mass carried by one adapted metric cell. -/
def criticalPrimeFockAdaptedCellExponent (m : ℝ) : ℝ :=
  -(m - 4) / m

theorem tendsto_criticalPrimeFockAdaptedCellCenter_atTop
    {m : ℝ} (hm : 0 < m) :
    Tendsto (criticalPrimeFockAdaptedCellCenter m) atTop atTop := by
  unfold criticalPrimeFockAdaptedCellCenter
  exact (tendsto_rpow_atTop (div_pos (by norm_num) hm)).comp
    tendsto_natCast_atTop_atTop

theorem criticalPrimeFockAdaptedCellMain_eq_rpow
    {m : ℝ} (hm : 0 < m) {n : ℕ} (hn : 0 < n) :
    criticalPrimeFockAdaptedCellMain m n =
      2 * (n : ℝ) ^ criticalPrimeFockAdaptedCellExponent m := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hx : 0 < criticalPrimeFockAdaptedCellCenter m n := by
    exact Real.rpow_pos_of_pos hnR _
  rw [criticalPrimeFockAdaptedCellMain,
    criticalPrimeFockWindowMain_eq_rpow m hx]
  rw [criticalPrimeFockAdaptedCellCenter, ← Real.rpow_mul hnR.le]
  congr 2
  rw [criticalPrimeFockAdaptedCellExponent]
  field_simp
  ring

theorem criticalPrimeFockAdaptedCellMass_nonneg (m : ℝ) (n : ℕ) :
    0 ≤ criticalPrimeFockAdaptedCellMass m n := by
  have hr : 0 ≤ criticalPrimeFockRadius m (criticalPrimeFockAdaptedCellCenter m n) := by
    rw [criticalPrimeFockRadius]
    exact Real.rpow_nonneg (Real.sqrt_nonneg _) _
  unfold criticalPrimeFockAdaptedCellMass
  dsimp only
  rw [primeLogWindowMass_eq_sum _ hr]
  exact Finset.sum_nonneg fun k _ => primeLogPowWeight_two_nonneg k

theorem criticalPrimeFockAdaptedCellMain_pos
    {m : ℝ} (hm : 0 < m) {n : ℕ} (hn : 0 < n) :
    0 < criticalPrimeFockAdaptedCellMain m n := by
  rw [criticalPrimeFockAdaptedCellMain_eq_rpow hm hn]
  exact mul_pos (by norm_num) (Real.rpow_pos_of_pos (by exact_mod_cast hn) _)

theorem rpow_criticalPrimeFockAdaptedCellMass_eq_ratio_mul_main
    {m q : ℝ} (hm : 0 < m) {n : ℕ} (hn : 0 < n) :
    criticalPrimeFockAdaptedCellMass m n ^ q =
      (criticalPrimeFockAdaptedCellMass m n /
        criticalPrimeFockAdaptedCellMain m n) ^ q *
          criticalPrimeFockAdaptedCellMain m n ^ q := by
  have hmpos : 0 < criticalPrimeFockAdaptedCellMain m n :=
    criticalPrimeFockAdaptedCellMain_pos hm hn
  rw [← Real.mul_rpow
      (div_nonneg (criticalPrimeFockAdaptedCellMass_nonneg m n) hmpos.le) hmpos.le,
    div_mul_cancel₀ _ hmpos.ne']

theorem tendsto_criticalPrimeFockAdaptedCellMass_div_main
    {m : ℝ} (hm : 2 < m) :
    Tendsto (fun n : ℕ =>
      criticalPrimeFockAdaptedCellMass m n /
        criticalPrimeFockAdaptedCellMain m n) atTop (nhds 1) := by
  have h := (tendsto_primeLogWindowMass_div_criticalPrimeFockModel hm).comp
    (tendsto_criticalPrimeFockAdaptedCellCenter_atTop (by linarith : 0 < m))
  change Tendsto (fun n : ℕ =>
    primeLogWindowMass (criticalPrimeFockAdaptedCellCenter m n)
        (criticalPrimeFockRadius m (criticalPrimeFockAdaptedCellCenter m n)) /
      (2 * criticalPrimeFockAdaptedCellCenter m n *
        criticalPrimeFockRadius m (criticalPrimeFockAdaptedCellCenter m n)))
    atTop (nhds 1) at h
  simpa only [criticalPrimeFockAdaptedCellMass,
    criticalPrimeFockAdaptedCellMain, criticalPrimeFockWindowMain] using h

theorem summable_rpow_criticalPrimeFockAdaptedCellMain_iff
    {m q : ℝ} (hm : 4 < m) (hq : 0 < q) :
    Summable (fun n : ℕ => criticalPrimeFockAdaptedCellMain m n ^ q) ↔
      criticalPrimeFockSchattenThreshold m < q := by
  have hfun : (fun n : ℕ => criticalPrimeFockAdaptedCellMain m n ^ q) =
      fun n : ℕ => (2 : ℝ) ^ q *
        (n : ℝ) ^ (criticalPrimeFockAdaptedCellExponent m * q) := by
    funext n
    rcases n.eq_zero_or_pos with rfl | hn
    · have hexp : criticalPrimeFockAdaptedCellExponent m * q ≠ 0 := by
        have he : criticalPrimeFockAdaptedCellExponent m < 0 := by
          rw [criticalPrimeFockAdaptedCellExponent]
          exact div_neg_of_neg_of_pos (by linarith) (by linarith)
        exact (mul_neg_of_neg_of_pos he hq).ne
      have hcenterExp : 2 / m ≠ 0 := (div_pos (by norm_num) (by linarith)).ne'
      simp [criticalPrimeFockAdaptedCellMain, criticalPrimeFockAdaptedCellCenter,
        criticalPrimeFockWindowMain, criticalPrimeFockRadius, hcenterExp, hq.ne', hexp]
    · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      rw [criticalPrimeFockAdaptedCellMain_eq_rpow (by linarith : 0 < m) hn,
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.rpow_nonneg hnR.le _),
        ← Real.rpow_mul hnR.le]
  rw [hfun, summable_mul_left_iff (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) q).ne']
  rw [Real.summable_nat_rpow]
  rw [criticalPrimeFockAdaptedCellExponent,
    criticalPrimeFockSchattenThreshold]
  have hm0 : 0 < m := by linarith
  have hd : 0 < m - 4 := sub_pos.mpr hm
  rw [div_lt_iff₀ hd]
  rw [show -(m - 4) / m * q = (-(m - 4) * q) / m by ring,
    div_lt_iff₀ hm0]
  constructor <;> intro h <;> nlinarith

theorem eventually_criticalPrimeFockAdaptedCellMass_ratio_bounds
    {m : ℝ} (hm : 2 < m) :
    ∀ᶠ n : ℕ in atTop,
      (1 / 2 : ℝ) ≤ criticalPrimeFockAdaptedCellMass m n /
          criticalPrimeFockAdaptedCellMain m n ∧
        criticalPrimeFockAdaptedCellMass m n /
          criticalPrimeFockAdaptedCellMain m n ≤ 3 / 2 := by
  have hratio := tendsto_criticalPrimeFockAdaptedCellMass_div_main (by linarith : 2 < m)
  filter_upwards [hratio.eventually (Ioo_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)
    (by norm_num : (1 : ℝ) < 3 / 2))] with n hn
  exact ⟨hn.1.le, hn.2.le⟩

theorem exists_positive_criticalPrimeFockAdaptedCellMass_ratio_bounds
    {m : ℝ} (hm : 2 < m) :
    ∃ N : ℕ, 0 < N ∧ ∀ b : ℕ, N ≤ b →
      (1 / 2 : ℝ) ≤ criticalPrimeFockAdaptedCellMass m b /
          criticalPrimeFockAdaptedCellMain m b ∧
        criticalPrimeFockAdaptedCellMass m b /
          criticalPrimeFockAdaptedCellMain m b ≤ 3 / 2 := by
  obtain ⟨N0, hN0⟩ := eventually_atTop.1
    (eventually_criticalPrimeFockAdaptedCellMass_ratio_bounds hm)
  refine ⟨max N0 1,
    lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_right N0 1), fun b hb => ?_⟩
  exact hN0 b ((Nat.le_max_left N0 1).trans hb)

theorem summable_rpow_criticalPrimeFockAdaptedCellMass_add_iff_main_add
    {m q : ℝ} (hm : 4 < m) (hq : 0 < q) {N : ℕ} (hNpos : 0 < N)
    (hN : ∀ b : ℕ, N ≤ b →
      (1 / 2 : ℝ) ≤ criticalPrimeFockAdaptedCellMass m b /
          criticalPrimeFockAdaptedCellMain m b ∧
        criticalPrimeFockAdaptedCellMass m b /
          criticalPrimeFockAdaptedCellMain m b ≤ 3 / 2) :
    Summable (fun n : ℕ => criticalPrimeFockAdaptedCellMass m (n + N) ^ q) ↔
      Summable (fun n : ℕ => criticalPrimeFockAdaptedCellMain m (n + N) ^ q) := by
  have hf : ∀ n : ℕ, 0 ≤ criticalPrimeFockAdaptedCellMain m (n + N) ^ q := by
    intro n
    exact Real.rpow_nonneg
      (criticalPrimeFockAdaptedCellMain_pos (by linarith : 0 < m)
        (lt_of_lt_of_le hNpos (Nat.le_add_left N n))).le q
  have hwlower : ∀ n : ℕ, (1 / 2 : ℝ) ^ q ≤
      (criticalPrimeFockAdaptedCellMass m (n + N) /
        criticalPrimeFockAdaptedCellMain m (n + N)) ^ q := by
    intro n
    exact Real.rpow_le_rpow (by norm_num) (hN (n + N) (Nat.le_add_left N n)).1 hq.le
  have hwupper : ∀ n : ℕ,
      (criticalPrimeFockAdaptedCellMass m (n + N) /
        criticalPrimeFockAdaptedCellMain m (n + N)) ^ q ≤ (3 / 2 : ℝ) ^ q := by
    intro n
    exact Real.rpow_le_rpow
      (le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (hN (n + N) (Nat.le_add_left N n)).1)
      (hN (n + N) (Nat.le_add_left N n)).2 hq.le
  have hcomp := HTGeometry.summable_mul_iff_of_nonneg_of_uniform_pos_le_of_le
    (fun n : ℕ => criticalPrimeFockAdaptedCellMain m (n + N) ^ q)
    (fun n : ℕ => (criticalPrimeFockAdaptedCellMass m (n + N) /
      criticalPrimeFockAdaptedCellMain m (n + N)) ^ q)
    hf (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2) q)
    hwlower hwupper
  have hfactor : ∀ n : ℕ,
      criticalPrimeFockAdaptedCellMass m (n + N) ^ q =
        (criticalPrimeFockAdaptedCellMass m (n + N) /
          criticalPrimeFockAdaptedCellMain m (n + N)) ^ q *
            criticalPrimeFockAdaptedCellMain m (n + N) ^ q := by
    intro n
    have hnpos : 0 < n + N := lt_of_lt_of_le hNpos (Nat.le_add_left N n)
    exact rpow_criticalPrimeFockAdaptedCellMass_eq_ratio_mul_main
      (by linarith : 0 < m) hnpos
  have hfun : (fun n : ℕ => criticalPrimeFockAdaptedCellMass m (n + N) ^ q) =
      fun n : ℕ =>
        (criticalPrimeFockAdaptedCellMass m (n + N) /
          criticalPrimeFockAdaptedCellMain m (n + N)) ^ q *
            criticalPrimeFockAdaptedCellMain m (n + N) ^ q := funext hfactor
  rw [hfun]
  exact hcomp

theorem summable_rpow_criticalPrimeFockAdaptedCellMass_iff_main
    {m q : ℝ} (hm : 4 < m) (hq : 0 < q) :
    Summable (fun n : ℕ => criticalPrimeFockAdaptedCellMass m n ^ q) ↔
      Summable (fun n : ℕ => criticalPrimeFockAdaptedCellMain m n ^ q) := by
  obtain ⟨N, hNpos, hN⟩ :=
    exists_positive_criticalPrimeFockAdaptedCellMass_ratio_bounds (by linarith : 2 < m)
  have hshift :
      Summable (fun n : ℕ => criticalPrimeFockAdaptedCellMass m (n + N) ^ q) ↔
        Summable (fun n : ℕ => criticalPrimeFockAdaptedCellMain m (n + N) ^ q) :=
    summable_rpow_criticalPrimeFockAdaptedCellMass_add_iff_main_add
      hm hq hNpos hN
  have hmassTail :
      Summable (fun n : ℕ => criticalPrimeFockAdaptedCellMass m (n + N) ^ q) ↔
        Summable (fun n : ℕ => criticalPrimeFockAdaptedCellMass m n ^ q) :=
    summable_nat_add_iff (f := fun n : ℕ => criticalPrimeFockAdaptedCellMass m n ^ q) N
  have hmainTail :
      Summable (fun n : ℕ => criticalPrimeFockAdaptedCellMain m (n + N) ^ q) ↔
        Summable (fun n : ℕ => criticalPrimeFockAdaptedCellMain m n ^ q) :=
    summable_nat_add_iff (f := fun n : ℕ => criticalPrimeFockAdaptedCellMain m n ^ q) N
  exact hmassTail.symm.trans (hshift.trans hmainTail)

theorem summable_rpow_criticalPrimeFockAdaptedCellMass_iff
    {m q : ℝ} (hm : 4 < m) (hq : 0 < q) :
    Summable (fun n : ℕ => criticalPrimeFockAdaptedCellMass m n ^ q) ↔
      criticalPrimeFockSchattenThreshold m < q :=
  (summable_rpow_criticalPrimeFockAdaptedCellMass_iff_main hm hq).trans
    (summable_rpow_criticalPrimeFockAdaptedCellMain_iff hm hq)

end

end RHTower
