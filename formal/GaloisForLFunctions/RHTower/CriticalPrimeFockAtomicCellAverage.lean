import GaloisForLFunctions.RHTower.CriticalPrimeFockAdaptedCellMass
import GaloisForLFunctions.RHTower.PolynomialFockPrimeBallOverlap

open Filter Topology

namespace RHTower

noncomputable section

/-- The atomic Toeplitz measure's adapted average on the `n`-th positive-real metric cell. -/
def criticalPrimeFockAtomicCellAverage (m : ℝ) (n : ℕ) : ℝ :=
  let x := criticalPrimeFockAdaptedCellCenter m n
  let r := criticalPrimeFockRadius m x
  ∑ k ∈ Finset.Ioc ⌊Real.exp (x - r)⌋₊ ⌊Real.exp (x + r)⌋₊,
    primeLogPowWeight 2 k *
      (criticalPrimeFockRadius m (Real.log k) / r) ^ 2

theorem criticalPrimeFockRadius_two_mul
    {m x : ℝ} (hx : 0 ≤ x) :
    criticalPrimeFockRadius m (2 * x) =
      2 ^ (1 - m / 2) * criticalPrimeFockRadius m x := by
  rw [criticalPrimeFockRadius_eq_rpow (mul_nonneg (by norm_num) hx),
    criticalPrimeFockRadius_eq_rpow hx,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx]

theorem criticalPrimeFockRadius_ratio_sq_bounds_of_mem_window
    {m x : ℝ} (hm : 2 ≤ m) (hx : 2 ≤ x) {k : ℕ}
    (hk : k ∈ Finset.Ioc
      ⌊Real.exp (x - criticalPrimeFockRadius m x)⌋₊
      ⌊Real.exp (x + criticalPrimeFockRadius m x)⌋₊) :
    (2 ^ (1 - m / 2)) ^ 2 ≤
        (criticalPrimeFockRadius m (Real.log k) /
          criticalPrimeFockRadius m x) ^ 2 ∧
      (criticalPrimeFockRadius m (Real.log k) /
          criticalPrimeFockRadius m x) ^ 2 ≤
        (2 ^ (m / 2 - 1)) ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hr0 : 0 < criticalPrimeFockRadius m x := criticalPrimeFockRadius_pos hx0
  have hr1 : criticalPrimeFockRadius m x ≤ 1 :=
    criticalPrimeFockRadius_le_one hm (by linarith)
  have habs := abs_log_sub_le_of_mem_window hk
  have hkLower : x / 2 ≤ Real.log k := by
    have := (abs_le.mp habs).1
    linarith
  have hkUpper : Real.log k ≤ 2 * x := by
    have := (abs_le.mp habs).2
    linarith
  have hkpos : 0 < Real.log k := lt_of_lt_of_le (by linarith : 0 < x / 2) hkLower
  have hlower : criticalPrimeFockRadius m (2 * x) ≤
      criticalPrimeFockRadius m (Real.log k) :=
    criticalPrimeFockRadius_anti hm hkpos hkUpper
  have hupper : criticalPrimeFockRadius m (Real.log k) ≤
      criticalPrimeFockRadius m (x / 2) :=
    criticalPrimeFockRadius_anti hm (by linarith : 0 < x / 2) hkLower
  have hratioLower : 2 ^ (1 - m / 2) ≤
      criticalPrimeFockRadius m (Real.log k) /
        criticalPrimeFockRadius m x := by
    apply (le_div_iff₀ hr0).2
    calc
      2 ^ (1 - m / 2) * criticalPrimeFockRadius m x =
          criticalPrimeFockRadius m (2 * x) :=
        (criticalPrimeFockRadius_two_mul hx0.le).symm
      _ ≤ criticalPrimeFockRadius m (Real.log k) := hlower
  have hratioUpper : criticalPrimeFockRadius m (Real.log k) /
        criticalPrimeFockRadius m x ≤ 2 ^ (m / 2 - 1) := by
    apply (div_le_iff₀ hr0).2
    calc
      criticalPrimeFockRadius m (Real.log k) ≤
          criticalPrimeFockRadius m (x / 2) := hupper
      _ = 2 ^ (m / 2 - 1) * criticalPrimeFockRadius m x :=
        criticalPrimeFockRadius_half hx0.le
  have hconst0 : 0 ≤ (2 : ℝ) ^ (1 - m / 2) := Real.rpow_nonneg (by norm_num) _
  have hratio0 : 0 ≤ criticalPrimeFockRadius m (Real.log k) /
      criticalPrimeFockRadius m x := div_nonneg
        (criticalPrimeFockRadius_pos hkpos).le hr0.le
  exact ⟨sq_le_sq₀ hconst0 hratio0 |>.2 hratioLower,
    sq_le_sq₀ hratio0 (Real.rpow_nonneg (by norm_num) _) |>.2 hratioUpper⟩

theorem criticalPrimeFockAtomicCellAverage_nonneg (m : ℝ) (n : ℕ) :
    0 ≤ criticalPrimeFockAtomicCellAverage m n := by
  unfold criticalPrimeFockAtomicCellAverage
  dsimp only
  exact Finset.sum_nonneg fun k _ =>
    mul_nonneg (primeLogPowWeight_two_nonneg k) (sq_nonneg _)

theorem criticalPrimeFockAtomicCellAverage_bounds
    {m : ℝ} (hm : 4 < m) {n : ℕ}
    (hn : 2 ≤ criticalPrimeFockAdaptedCellCenter m n) :
    (2 ^ (1 - m / 2)) ^ 2 * criticalPrimeFockAdaptedCellMass m n ≤
        criticalPrimeFockAtomicCellAverage m n ∧
      criticalPrimeFockAtomicCellAverage m n ≤
        (2 ^ (m / 2 - 1)) ^ 2 * criticalPrimeFockAdaptedCellMass m n := by
  let x := criticalPrimeFockAdaptedCellCenter m n
  let r := criticalPrimeFockRadius m x
  let S := Finset.Ioc ⌊Real.exp (x - r)⌋₊ ⌊Real.exp (x + r)⌋₊
  have hr0 : 0 ≤ r := by dsimp [r]; exact Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hmass : criticalPrimeFockAdaptedCellMass m n =
      ∑ k ∈ S, primeLogPowWeight 2 k := by
    unfold criticalPrimeFockAdaptedCellMass
    dsimp only
    simpa [x, r, S] using primeLogWindowMass_eq_sum x hr0
  have hterm : ∀ k ∈ S,
      (2 ^ (1 - m / 2)) ^ 2 * primeLogPowWeight 2 k ≤
          primeLogPowWeight 2 k *
            (criticalPrimeFockRadius m (Real.log k) / r) ^ 2 ∧
        primeLogPowWeight 2 k *
            (criticalPrimeFockRadius m (Real.log k) / r) ^ 2 ≤
          (2 ^ (m / 2 - 1)) ^ 2 * primeLogPowWeight 2 k := by
    intro k hk
    have hb := criticalPrimeFockRadius_ratio_sq_bounds_of_mem_window
      (by linarith : 2 ≤ m) (by simpa [x] using hn) (by simpa [S, r, x] using hk)
    have hw := primeLogPowWeight_two_nonneg k
    exact ⟨by nlinarith [hb.1], by nlinarith [hb.2]⟩
  constructor
  · rw [hmass, Finset.mul_sum]
    exact Finset.sum_le_sum fun k hk => (hterm k hk).1
  · rw [hmass, Finset.mul_sum]
    unfold criticalPrimeFockAtomicCellAverage
    dsimp only
    simpa [x, r, S] using Finset.sum_le_sum fun k hk => (hterm k hk).2

theorem exists_criticalPrimeFockAtomicCellAverage_bounds
    {m : ℝ} (hm : 4 < m) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (2 ^ (1 - m / 2)) ^ 2 * criticalPrimeFockAdaptedCellMass m n ≤
          criticalPrimeFockAtomicCellAverage m n ∧
        criticalPrimeFockAtomicCellAverage m n ≤
          (2 ^ (m / 2 - 1)) ^ 2 * criticalPrimeFockAdaptedCellMass m n := by
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((tendsto_criticalPrimeFockAdaptedCellCenter_atTop (by linarith : 0 < m)).eventually_ge_atTop 2)
  exact ⟨N, fun n hn => criticalPrimeFockAtomicCellAverage_bounds hm (hN n hn)⟩

theorem summable_rpow_criticalPrimeFockAtomicCellAverage_add_iff_mass_add
    {m q : ℝ} (hq : 0 < q) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      (2 ^ (1 - m / 2)) ^ 2 * criticalPrimeFockAdaptedCellMass m n ≤
          criticalPrimeFockAtomicCellAverage m n ∧
        criticalPrimeFockAtomicCellAverage m n ≤
          (2 ^ (m / 2 - 1)) ^ 2 * criticalPrimeFockAdaptedCellMass m n) :
    Summable (fun n : ℕ => criticalPrimeFockAtomicCellAverage m (n + N) ^ q) ↔
      Summable (fun n : ℕ => criticalPrimeFockAdaptedCellMass m (n + N) ^ q) := by
  let c : ℝ := (2 ^ (1 - m / 2)) ^ 2
  let C : ℝ := (2 ^ (m / 2 - 1)) ^ 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hlower : ∀ n : ℕ,
      c ^ q * criticalPrimeFockAdaptedCellMass m (n + N) ^ q ≤
        criticalPrimeFockAtomicCellAverage m (n + N) ^ q := by
    intro n
    rw [← Real.mul_rpow hc.le (criticalPrimeFockAdaptedCellMass_nonneg m (n + N))]
    exact Real.rpow_le_rpow (mul_nonneg hc.le
      (criticalPrimeFockAdaptedCellMass_nonneg m (n + N)))
      (by simpa [c] using (hN (n + N) (Nat.le_add_left N n)).1) hq.le
  have hupper : ∀ n : ℕ,
      criticalPrimeFockAtomicCellAverage m (n + N) ^ q ≤
        C ^ q * criticalPrimeFockAdaptedCellMass m (n + N) ^ q := by
    intro n
    rw [← Real.mul_rpow hC.le (criticalPrimeFockAdaptedCellMass_nonneg m (n + N))]
    exact Real.rpow_le_rpow (criticalPrimeFockAtomicCellAverage_nonneg m (n + N))
      (by simpa [C] using (hN (n + N) (Nat.le_add_left N n)).2) hq.le
  constructor
  · intro hA
    have hscaled : Summable (fun n : ℕ =>
        c ^ q * criticalPrimeFockAdaptedCellMass m (n + N) ^ q) :=
      Summable.of_nonneg_of_le
        (fun n => mul_nonneg (Real.rpow_nonneg hc.le q)
          (Real.rpow_nonneg (criticalPrimeFockAdaptedCellMass_nonneg m (n + N)) q))
        hlower hA
    exact (summable_mul_left_iff (Real.rpow_pos_of_pos hc q).ne').mp hscaled
  · intro hM
    have hscaled : Summable (fun n : ℕ =>
        C ^ q * criticalPrimeFockAdaptedCellMass m (n + N) ^ q) :=
      hM.mul_left (C ^ q)
    exact Summable.of_nonneg_of_le
      (fun n => Real.rpow_nonneg (criticalPrimeFockAtomicCellAverage_nonneg m (n + N)) q)
      hupper hscaled

theorem summable_rpow_criticalPrimeFockAtomicCellAverage_iff_mass
    {m q : ℝ} (hm : 4 < m) (hq : 0 < q) :
    Summable (fun n : ℕ => criticalPrimeFockAtomicCellAverage m n ^ q) ↔
      Summable (fun n : ℕ => criticalPrimeFockAdaptedCellMass m n ^ q) := by
  obtain ⟨N, hN⟩ := exists_criticalPrimeFockAtomicCellAverage_bounds hm
  have hshift :
      Summable (fun n : ℕ => criticalPrimeFockAtomicCellAverage m (n + N) ^ q) ↔
        Summable (fun n : ℕ => criticalPrimeFockAdaptedCellMass m (n + N) ^ q) :=
    summable_rpow_criticalPrimeFockAtomicCellAverage_add_iff_mass_add hq hN
  have haverageTail :
      Summable (fun n : ℕ => criticalPrimeFockAtomicCellAverage m (n + N) ^ q) ↔
        Summable (fun n : ℕ => criticalPrimeFockAtomicCellAverage m n ^ q) :=
    summable_nat_add_iff
      (f := fun n : ℕ => criticalPrimeFockAtomicCellAverage m n ^ q) N
  have hmassTail :
      Summable (fun n : ℕ => criticalPrimeFockAdaptedCellMass m (n + N) ^ q) ↔
        Summable (fun n : ℕ => criticalPrimeFockAdaptedCellMass m n ^ q) :=
    summable_nat_add_iff
      (f := fun n : ℕ => criticalPrimeFockAdaptedCellMass m n ^ q) N
  exact haverageTail.symm.trans (hshift.trans hmassTail)

theorem summable_rpow_criticalPrimeFockAtomicCellAverage_iff
    {m q : ℝ} (hm : 4 < m) (hq : 0 < q) :
    Summable (fun n : ℕ => criticalPrimeFockAtomicCellAverage m n ^ q) ↔
      criticalPrimeFockSchattenThreshold m < q :=
  (summable_rpow_criticalPrimeFockAtomicCellAverage_iff_mass hm hq).trans
    (summable_rpow_criticalPrimeFockAdaptedCellMass_iff hm hq)

end

end RHTower
