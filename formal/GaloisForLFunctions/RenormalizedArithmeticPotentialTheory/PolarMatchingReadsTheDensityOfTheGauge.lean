import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheLiouvilleGaugeFlipsThePolarDivergence

/-!
# Polar matching reads the density of the gauge

The prime divergence of `ζ` at the horizon is matched to the archimedean polar direction with
coefficient `+1`; the Liouville twin's with `−1` (`TheLiouvilleGaugeFlipsThePolarDivergence`). This
file computes the coefficient for every real sign gauge and shows what it can and cannot see.

A **sign gauge** is a function `ε` with `ε(mn) = ε(m)ε(n)` and `ε(n)² = 1` on positive integers. Its
twisted Mertens sum is `A_ε(y) = Σ_{t ≤ y} ε(t)Λ(t)/t`.

* **The gauged rows** (`sum_weilPrimeKernel_gauge`, `primeBilinear_gaugeTrunc_eq`): for `v = ε u`,
  `(P v)_m = (A_ε(⌊N/m⌋) + D_ε(m)) v_m` with `D_ε(m) = Σ_{t ∣ m} ε(t)Λ(t)`.
* **The matching law** (`abs_primeBilinear_gaugeTrunc_sub_le`, `abs_gaugeForm_stepProfile_sub_le`):
  if `|A_ε(y) − κ log y| ≤ K` for all `y ≥ 1`, with `|κ| ≤ 1`, then on uniform step profiles
  `P(εx) = κ ℓ(x)² + O(|c|-mass)`. The coefficient `κ` is the **polar matching coefficient** of the
  gauge: the asymptotic density of unflipped minus flipped primes, weighted by `log p/p`.
* **Instances** (`euler_matching`, `liouville_matching`, `finiteFlip_matching`): the Euler gauge has
  `κ = 1`, Liouville's gauge `κ = −1`, and every gauge flipping the primes of a finite set `F` has
  `κ = 1`, with `K = log 4 + 4 + 2 Σ_{p ∈ F} log p/(p − 1)`.

So polar matching — the coupling of the prime divergence to the archimedean counterterm — reads the
density of the gauge and nothing else: a twin that differs from `ζ` at finitely many primes is
matched exactly as `ζ` is. Separation of `ζ` from such twins cannot come from the divergences of the
coupled renormalization; it must come from finite parts, where AES finds a margin of `2 log² p` in
the renormalized source at each flipped prime.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticFunction GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticElectrostatics

/-- A **real sign gauge**: completely multiplicative on positive integers with values `±1`. -/
structure IsSignGauge (ε : ℕ → ℝ) : Prop where
  mul : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → ε (m * n) = ε m * ε n
  mul_self : ∀ {n : ℕ}, n ≠ 0 → ε n * ε n = 1

variable {ε : ℕ → ℝ}

/-- The twisted Mertens sum `A_ε(y) = Σ_{t ≤ y} ε(t)Λ(t)/t`. -/
def gaugeMertensSum (ε : ℕ → ℝ) (y : ℕ) : ℝ := ∑ t ∈ Icc 1 y, ε t * Λ t / t

/-- The divisor part `D_ε(m) = Σ_{t ∣ m} ε(t)Λ(t)`. -/
def gaugeDivisorSum (ε : ℕ → ℝ) (m : ℕ) : ℝ := ∑ t ∈ m.divisors, ε t * Λ t

/-- The gauged pole vector `ε(n) n^{−1/2}`, truncated at `M`. -/
def gaugeTrunc (ε : ℕ → ℝ) (M n : ℕ) : ℝ := ε n * truncPole M n

theorem IsSignGauge.of_dvd (hε : IsSignGauge ε) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : m ∣ n) :
    ε n = ε m * ε (n / m) := by
  have hq : n / m ≠ 0 := fun h0 => hn (by rw [← Nat.mul_div_cancel' h, h0, mul_zero])
  rw [← hε.mul hm hq, Nat.mul_div_cancel' h]

/-- `ε(n) = ε(m) ε(m/n)` for `n ∣ m`. -/
theorem IsSignGauge.of_dvd' (hε : IsSignGauge ε) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (h : n ∣ m) : ε n = ε m * ε (m / n) := by
  have hq : m / n ≠ 0 := fun h0 => hm (by rw [← Nat.mul_div_cancel' h, h0, mul_zero])
  have h1 := hε.of_dvd hn hm h
  calc ε n = ε n * (ε (m / n) * ε (m / n)) := by rw [hε.mul_self hq, mul_one]
    _ = ε n * ε (m / n) * ε (m / n) := by ring
    _ = ε m * ε (m / n) := by rw [← h1]

/-! ### The gauged rows -/

theorem sum_up_gauge_eq {m N : ℕ} (hm : 0 < m) :
    ∑ n ∈ Icc 1 N, (if m ∣ n ∧ m ≠ n then ε (n / m) * Λ (n / m) / ((n / m : ℕ) : ℝ) else 0) =
      gaugeMertensSum ε (N / m) := by
  have hterm : ∀ n ∈ Icc 1 N, (if m ∣ n ∧ m ≠ n then
      ε (n / m) * Λ (n / m) / ((n / m : ℕ) : ℝ) else 0) =
      if m ∣ n then ε (n / m) * Λ (n / m) / ((n / m : ℕ) : ℝ) else 0 := by
    intro n _
    by_cases h : m ∣ n
    · by_cases h' : m = n
      · subst h'; simp [Nat.div_self hm]
      · rw [if_pos ⟨h, h'⟩, if_pos h]
    · rw [if_neg (fun h'' => h h''.1), if_neg h]
  rw [sum_congr rfl hterm, ← sum_filter, filter_dvd_Icc_eq_image hm,
    sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hm h, gaugeMertensSum]
  exact sum_congr rfl fun t _ => by rw [Nat.mul_div_cancel_left t hm]

theorem sum_down_gauge_eq {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    ∑ n ∈ Icc 1 N, (if n ∣ m ∧ n ≠ m then ε (m / n) * Λ (m / n) else 0) = gaugeDivisorSum ε m := by
  have hterm : ∀ n ∈ Icc 1 N, (if n ∣ m ∧ n ≠ m then ε (m / n) * Λ (m / n) else 0) =
      if n ∣ m then ε (m / n) * Λ (m / n) else 0 := by
    intro n _
    by_cases h : n ∣ m
    · by_cases h' : n = m
      · subst h'; simp [Nat.div_self hm]
      · rw [if_pos ⟨h, h'⟩, if_pos h]
    · rw [if_neg (fun h'' => h h''.1), if_neg h]
  rw [sum_congr rfl hterm, ← sum_filter, filter_Icc_dvd_eq_divisors hm hmN, gaugeDivisorSum]
  exact Nat.sum_div_divisors m (fun t => ε t * Λ t)

/-- **The gauged rows**: for `m ≤ M`, `Σ_{n ≤ M} P(m, n) ε(n) u_n = (A_ε(⌊M/m⌋) + D_ε(m)) ε(m) u_m`. -/
theorem sum_weilPrimeKernel_gauge (hε : IsSignGauge ε) {m M : ℕ} (hm : 0 < m) (hmM : m ≤ M) :
    ∑ n ∈ Icc 1 M, weilPrimeKernel m n * (ε n * poleVector n) =
      (gaugeMertensSum ε (M / m) + gaugeDivisorSum ε m) * (ε m * poleVector m) := by
  have hterm : ∀ n ∈ Icc 1 M, weilPrimeKernel m n * (ε n * poleVector n) =
      ε m * poleVector m *
        ((if m ∣ n ∧ m ≠ n then ε (n / m) * Λ (n / m) / ((n / m : ℕ) : ℝ) else 0) +
          (if n ∣ m ∧ n ≠ m then ε (m / n) * Λ (m / n) else 0)) := by
    intro n hn
    have hn0 := pos_of_mem_Icc' hn
    have hstep : weilPrimeKernel m n * (ε n * poleVector n) =
        ε n * (poleVector m * (weilPrimeKernel m n * Real.sqrt ((m : ℝ) / n))) := by
      rw [← weilPrimeKernel_mul_poleVector hm hn0]; ring
    rw [hstep, weilPrimeKernel_mul_sqrt_ratio hm hn0]
    by_cases h1 : m ∣ n ∧ m ≠ n
    · have h2 : ¬ (n ∣ m ∧ n ≠ m) := fun h => h1.2 (Nat.dvd_antisymm h1.1 h.1)
      rw [if_pos h1, if_neg h2, if_pos h1, if_neg h2, hε.of_dvd hm.ne' hn0.ne' h1.1]
      ring
    · by_cases h2 : n ∣ m ∧ n ≠ m
      · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2, hε.of_dvd' hm.ne' hn0.ne' h2.1]
        ring
      · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]
        ring
  rw [sum_congr rfl hterm, ← mul_sum, sum_add_distrib, sum_up_gauge_eq hm, sum_down_gauge_eq hm hmM]
  ring

/-- **The gauged pole Gram**: `⟨εu^{(M)}, P εu^{(M')}⟩ = Σ_{m ≤ M} (A_ε(⌊M'/m⌋) + D_ε(m))/m`. -/
theorem primeBilinear_gaugeTrunc_eq (hε : IsSignGauge ε) {M M' N : ℕ} (hMM' : M ≤ M')
    (hM'N : M' ≤ N) :
    primeBilinear N (gaugeTrunc ε M) (gaugeTrunc ε M') =
      ∑ m ∈ Icc 1 M, (gaugeMertensSum ε (M' / m) + gaugeDivisorSum ε m) / m := by
  unfold primeBilinear
  have hrow : ∀ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, gaugeTrunc ε M m * gaugeTrunc ε M' n *
      weilPrimeKernel m n = if m ≤ M then
        (gaugeMertensSum ε (M' / m) + gaugeDivisorSum ε m) / m else 0 := by
    intro m hm
    have hm0 := pos_of_mem_Icc' hm
    unfold gaugeTrunc truncPole
    split_ifs with hmM
    · have hinner : ∑ n ∈ Icc 1 N, ε m * poleVector m *
          (ε n * if n ≤ M' then poleVector n else 0) * weilPrimeKernel m n =
          ε m * poleVector m * ∑ n ∈ Icc 1 M', weilPrimeKernel m n * (ε n * poleVector n) := by
        rw [mul_sum, ← sum_truncate hM'N]
        refine sum_congr rfl fun n _ => ?_
        split_ifs <;> ring
      rw [hinner, sum_weilPrimeKernel_gauge hε hm0 (hmM.trans hMM')]
      have h1 : ε m * ε m = 1 := hε.mul_self hm0.ne'
      have h2 : poleVector m * poleVector m = 1 / m := by rw [← sq, poleVector_sq]
      calc ε m * poleVector m * ((gaugeMertensSum ε (M' / m) + gaugeDivisorSum ε m) *
            (ε m * poleVector m))
          = (ε m * ε m) * (poleVector m * poleVector m) *
            (gaugeMertensSum ε (M' / m) + gaugeDivisorSum ε m) := by ring
        _ = (gaugeMertensSum ε (M' / m) + gaugeDivisorSum ε m) / m := by rw [h1, h2]; ring
    · simp
  rw [sum_congr rfl hrow, sum_truncate (hMM'.trans hM'N)]

/-! ### The matching law -/

/-- The divisor part averages to the Mertens part. -/
theorem sum_gaugeDivisorSum_div (ε : ℕ → ℝ) (M : ℕ) :
    ∑ m ∈ Icc 1 M, gaugeDivisorSum ε m / m = ∑ k ∈ Icc 1 M, gaugeMertensSum ε (M / k) / k := by
  have h := sum_divisors_div_swap (fun t => ε t * Λ t) M
  simpa only [gaugeDivisorSum, gaugeMertensSum, mul_div_assoc] using h

/-- A Mertens-weighted harmonic sum with matching coefficient `κ`: for `M ≤ X`,
`|Σ_{m ≤ M} A_ε(⌊X/m⌋)/m − κ (H_M log X − Σ_{m ≤ M} log m/m)| ≤ (K + log 2) H_M`. -/
theorem abs_sum_gaugeMertens_div_sub_le {κ K : ℝ} (hκ : |κ| ≤ 1)
    (hA : ∀ y : ℕ, 1 ≤ y → |gaugeMertensSum ε y - κ * Real.log y| ≤ K) {M X : ℕ} (hMX : M ≤ X) :
    |∑ m ∈ Icc 1 M, gaugeMertensSum ε (X / m) / m -
        κ * (harmonicSum M * Real.log X - ∑ m ∈ Icc 1 M, Real.log m / m)| ≤
      (K + Real.log 2) * harmonicSum M := by
  have hexp : κ * (harmonicSum M * Real.log X - ∑ m ∈ Icc 1 M, Real.log m / m) =
      ∑ m ∈ Icc 1 M, κ * (Real.log X - Real.log m) / m := by
    rw [harmonicSum, sum_mul, ← sum_sub_distrib, mul_sum]
    exact sum_congr rfl fun m _ => by ring
  rw [hexp, ← sum_sub_distrib, harmonicSum, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m hm => ?_)
  have hm0 : 0 < m := (mem_Icc.mp hm).1
  have hmX := (mem_Icc.mp hm).2.trans hMX
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
  have hq : 1 ≤ X / m := (Nat.le_div_iff_mul_le hm0).mpr (by linarith)
  have h1 := hA (X / m) hq
  have h2 := log_div_add_log_le hm0 hmX
  have h3 := log_le_log_div_add_log hm0 hmX
  -- `|κ (log ⌊X/m⌋ − (log X − log m))| ≤ log 2`
  have h4 : |κ * (Real.log ((X / m : ℕ) : ℝ) - (Real.log X - Real.log m))| ≤ Real.log 2 := by
    rw [abs_mul]
    have : |Real.log ((X / m : ℕ) : ℝ) - (Real.log X - Real.log m)| ≤ Real.log 2 := by
      rw [abs_le]; constructor <;> linarith
    calc |κ| * |Real.log ((X / m : ℕ) : ℝ) - (Real.log X - Real.log m)|
        ≤ 1 * Real.log 2 := mul_le_mul hκ this (abs_nonneg _) zero_le_one
      _ = Real.log 2 := one_mul _
  rw [← sub_div, abs_div, abs_of_pos hm', mul_one_div]
  refine div_le_div_of_nonneg_right ?_ hm'.le
  calc |gaugeMertensSum ε (X / m) - κ * (Real.log X - Real.log m)|
      = |(gaugeMertensSum ε (X / m) - κ * Real.log ((X / m : ℕ) : ℝ)) +
          κ * (Real.log ((X / m : ℕ) : ℝ) - (Real.log X - Real.log m))| := by ring_nf
    _ ≤ K + Real.log 2 := (abs_add_le _ _).trans (add_le_add h1 h4)

/-- **The matching law, pole Gram.** If `|A_ε(y) − κ log y| ≤ K` for `y ≥ 1` and `|κ| ≤ 1`, then for
`1 ≤ M ≤ M' ≤ N`, `|⟨εu^{(M)}, P εu^{(M')}⟩ − κ H_M H_{M'}| ≤ (2K + 2 log 2 + 4) H_M`. -/
theorem abs_primeBilinear_gaugeTrunc_sub_le (hε : IsSignGauge ε) {κ K : ℝ} (hκ : |κ| ≤ 1)
    (hA : ∀ y : ℕ, 1 ≤ y → |gaugeMertensSum ε y - κ * Real.log y| ≤ K) {M M' N : ℕ}
    (hM : 1 ≤ M) (hMM' : M ≤ M') (hM'N : M' ≤ N) :
    |primeBilinear N (gaugeTrunc ε M) (gaugeTrunc ε M') - κ * harmonicSum M * harmonicSum M'| ≤
      (2 * K + 2 * Real.log 2 + 4) * harmonicSum M := by
  rw [primeBilinear_gaugeTrunc_eq hε hMM' hM'N]
  have hsplit : ∑ m ∈ Icc 1 M, (gaugeMertensSum ε (M' / m) + gaugeDivisorSum ε m) / m =
      ∑ m ∈ Icc 1 M, gaugeMertensSum ε (M' / m) / m +
        ∑ k ∈ Icc 1 M, gaugeMertensSum ε (M / k) / k := by
    rw [← sum_gaugeDivisorSum_div, ← sum_add_distrib]
    exact sum_congr rfl fun m _ => by ring
  rw [hsplit]
  have hE1 := abs_sum_gaugeMertens_div_sub_le hκ hA hMM'
  have hE2 := abs_sum_gaugeMertens_div_sub_le hκ hA (le_refl M)
  set S := ∑ m ∈ Icc 1 M, Real.log m / m
  have hS1 := sum_log_div_le M
  have hS2 := sum_log_div_ge hM
  have hH1 := one_le_harmonicSum hM
  have hHle := harmonicSum_le M
  have hHge := log_le_harmonicSum M
  have hH'le := harmonicSum_le M'
  have hH'ge := log_le_harmonicSum M'
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM)
  have hlogM1 : Real.log M ≤ Real.log (M + 1) :=
    Real.log_le_log (by exact_mod_cast hM) (by linarith)
  -- the main term `κ (H_M (log M + log M') − 2S)` is `κ H_M H_{M'}` up to `4 H_M`
  have hmain : |κ * (harmonicSum M * Real.log M' - S + (harmonicSum M * Real.log M - S)) -
      κ * harmonicSum M * harmonicSum M'| ≤ 4 * harmonicSum M := by
    have hsq1 : Real.log M ^ 2 ≤ harmonicSum M * Real.log M := by nlinarith
    have hsq2 : harmonicSum M * Real.log M ≤ Real.log M + Real.log (M + 1) ^ 2 := by
      nlinarith [pow_le_pow_left₀ hlogM hlogM1 2]
    have hinner : |harmonicSum M * Real.log M' - S + (harmonicSum M * Real.log M - S) -
        harmonicSum M * harmonicSum M'| ≤ 4 * harmonicSum M := by
      rw [abs_le]; constructor <;> nlinarith
    calc |κ * (harmonicSum M * Real.log M' - S + (harmonicSum M * Real.log M - S)) -
          κ * harmonicSum M * harmonicSum M'|
        = |κ| * |harmonicSum M * Real.log M' - S + (harmonicSum M * Real.log M - S) -
            harmonicSum M * harmonicSum M'| := by rw [← abs_mul]; ring_nf
      _ ≤ 1 * (4 * harmonicSum M) := mul_le_mul hκ hinner (abs_nonneg _) zero_le_one
      _ = 4 * harmonicSum M := one_mul _
  calc |∑ m ∈ Icc 1 M, gaugeMertensSum ε (M' / m) / m +
        ∑ k ∈ Icc 1 M, gaugeMertensSum ε (M / k) / k - κ * harmonicSum M * harmonicSum M'|
      = |(∑ m ∈ Icc 1 M, gaugeMertensSum ε (M' / m) / m - κ * (harmonicSum M * Real.log M' - S)) +
          (∑ k ∈ Icc 1 M, gaugeMertensSum ε (M / k) / k - κ * (harmonicSum M * Real.log M - S)) +
          (κ * (harmonicSum M * Real.log M' - S + (harmonicSum M * Real.log M - S)) -
            κ * harmonicSum M * harmonicSum M')| := by ring_nf
    _ ≤ (K + Real.log 2) * harmonicSum M + (K + Real.log 2) * harmonicSum M +
          4 * harmonicSum M :=
        (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add hE1 hE2)) hmain)
    _ = (2 * K + 2 * Real.log 2 + 4) * harmonicSum M := by ring

/-- **The matching law on uniform profiles.** For a sign gauge with matching coefficient `κ`
(`|A_ε(y) − κ log y| ≤ K`, `|κ| ≤ 1`) and every uniform step profile with all `M_i ≥ 1`,
`|P_N(εx) − κ ℓ(x)²| ≤ (2K + 2 log 2 + 4) Σ_{i,j} |c_i| |c_j| H_{min(M_i, M_j)}`. -/
theorem abs_gaugeForm_stepProfile_sub_le (hε : IsSignGauge ε) {κ K : ℝ} (hκ : |κ| ≤ 1)
    (hA : ∀ y : ℕ, 1 ≤ y → |gaugeMertensSum ε y - κ * Real.log y| ≤ K) {k N : ℕ}
    (c : Fin k → ℝ) (M : Fin k → ℕ) (hM : ∀ i, M i ≤ N) (hM1 : ∀ i, 1 ≤ M i) :
    |atomicWeilForm N (fun n => ε n * stepProfile c M n) -
        κ * polarFunctional N (stepProfile c M) ^ 2| ≤
      (2 * K + 2 * Real.log 2 + 4) * ∑ i, ∑ j, |c i| * |c j| * harmonicSum (min (M i) (M j)) := by
  have hL : ∀ y, primeBilinear N (fun n => ε n * stepProfile c M n) y =
      ∑ i, c i * primeBilinear N (gaugeTrunc ε (M i)) y := by
    intro y
    have h := primeBilinear_sum_left N c (fun i => gaugeTrunc ε (M i)) y
    rw [← h]
    congr 1
    funext n
    rw [stepProfile, mul_sum]
    exact sum_congr rfl fun i _ => by rw [gaugeTrunc]; ring
  have hexp : atomicWeilForm N (fun n => ε n * stepProfile c M n) =
      ∑ i, ∑ j, c i * c j * primeBilinear N (gaugeTrunc ε (M i)) (gaugeTrunc ε (M j)) := by
    rw [atomicWeilForm_eq_primeBilinear, hL]
    refine sum_congr rfl fun i _ => ?_
    rw [primeBilinear_comm, hL, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [primeBilinear_comm]
    ring
  have hpair : ∀ i j, |primeBilinear N (gaugeTrunc ε (M i)) (gaugeTrunc ε (M j)) -
      κ * harmonicSum (M i) * harmonicSum (M j)| ≤
        (2 * K + 2 * Real.log 2 + 4) * harmonicSum (min (M i) (M j)) := by
    intro i j
    rcases le_total (M i) (M j) with h | h
    · rw [min_eq_left h]
      exact abs_primeBilinear_gaugeTrunc_sub_le hε hκ hA (hM1 i) h (hM j)
    · rw [min_eq_right h, primeBilinear_comm, mul_assoc, mul_comm (harmonicSum (M i)), ← mul_assoc]
      exact abs_primeBilinear_gaugeTrunc_sub_le hε hκ hA (hM1 j) h (hM i)
  rw [hexp, polarFunctional_stepProfile c M hM, sq, sum_mul_sum, mul_sum, ← sum_sub_distrib]
  simp_rw [mul_sum, ← sum_sub_distrib]
  rw [mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  rw [mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
  have hrw : c i * c j * primeBilinear N (gaugeTrunc ε (M i)) (gaugeTrunc ε (M j)) -
      κ * (c i * harmonicSum (M i) * (c j * harmonicSum (M j))) =
      (c i * c j) * (primeBilinear N (gaugeTrunc ε (M i)) (gaugeTrunc ε (M j)) -
        κ * harmonicSum (M i) * harmonicSum (M j)) := by ring
  rw [hrw, abs_mul, abs_mul]
  calc |c i| * |c j| * |primeBilinear N (gaugeTrunc ε (M i)) (gaugeTrunc ε (M j)) -
        κ * harmonicSum (M i) * harmonicSum (M j)|
      ≤ |c i| * |c j| * ((2 * K + 2 * Real.log 2 + 4) * harmonicSum (min (M i) (M j))) :=
        mul_le_mul_of_nonneg_left (hpair i j) (by positivity)
    _ = (2 * K + 2 * Real.log 2 + 4) * (|c i| * |c j| * harmonicSum (min (M i) (M j))) := by ring

/-! ### Instances -/

/-- **The Euler gauge has matching coefficient `1`.** -/
theorem euler_matching :
    IsSignGauge (fun _ => 1) ∧ ∀ y : ℕ, 1 ≤ y →
      |gaugeMertensSum (fun _ => 1) y - 1 * Real.log y| ≤ Real.log 4 + 4 := by
  refine ⟨⟨fun _ _ => by ring, fun _ => by ring⟩, fun y hy => ?_⟩
  have h := RHTower.Mertens.mertens_first y hy
  simpa [gaugeMertensSum] using h

/-- **Liouville's gauge has matching coefficient `−1`.** -/
theorem liouville_matching :
    IsSignGauge liouvilleSign ∧ ∀ y : ℕ, 1 ≤ y →
      |gaugeMertensSum liouvilleSign y - (-1) * Real.log y| ≤ Real.log 4 + 4 + tameConstant := by
  refine ⟨⟨fun hm hn => liouvilleSign_mul hm hn, fun _ => liouvilleSign_mul_self _⟩,
    fun y hy => ?_⟩
  have h1 := liouvilleMertensSum_le hy
  have h2 := neg_le_liouvilleMertensSum hy
  have hK := tameConstant_nonneg
  have : gaugeMertensSum liouvilleSign y = liouvilleMertensSum y := rfl
  rw [this, abs_le]
  constructor <;> linarith

/-- The gauge flipping exactly the primes of a finite set `F`: `ε_F(n) = Π_{p ∈ F} (−1)^{v_p(n)}`. -/
def finiteFlip (F : Finset ℕ) (n : ℕ) : ℝ := ∏ p ∈ F, (-1 : ℝ) ^ (n.factorization p)

theorem finiteFlip_isSignGauge (F : Finset ℕ) : IsSignGauge (finiteFlip F) := by
  refine ⟨fun hm hn => ?_, fun _ => ?_⟩
  · rw [finiteFlip, finiteFlip, finiteFlip, ← prod_mul_distrib]
    refine prod_congr rfl fun p _ => ?_
    rw [Nat.factorization_mul hm hn, Finsupp.add_apply, pow_add]
  · rw [finiteFlip, ← prod_mul_distrib]
    refine prod_eq_one fun p _ => ?_
    rw [← pow_add, ← two_mul, pow_mul]; norm_num

/-- Away from the prime powers of `F`, the finite flip is `1`. -/
theorem finiteFlip_eq_one_of_coprime {F : Finset ℕ} {t : ℕ} (h : ∀ p ∈ F, ¬ p ∣ t) :
    finiteFlip F t = 1 := by
  refine prod_eq_one fun p hp => ?_
  rw [Nat.factorization_eq_zero_of_not_dvd (h p hp), pow_zero]

theorem abs_finiteFlip_sub_one_le (F : Finset ℕ) (t : ℕ) : |finiteFlip F t - 1| ≤ 2 := by
  have : |finiteFlip F t| = 1 := by
    rw [finiteFlip, abs_prod]
    exact prod_eq_one fun p _ => by rw [abs_pow, abs_neg, abs_one, one_pow]
  have h1 := abs_sub (finiteFlip F t) 1
  rw [this, abs_one] at h1
  linarith

/-- **Finitely many flips are invisible to polar matching**: the gauge flipping the primes of a
finite set `F` of primes has matching coefficient `1`, with
`|A_{ε_F}(y) − log y| ≤ log 4 + 4 + 2 Σ_{p ∈ F} log p/(p − 1)`. -/
theorem finiteFlip_matching {F : Finset ℕ} (hF : ∀ p ∈ F, p.Prime) :
    IsSignGauge (finiteFlip F) ∧ ∀ y : ℕ, 1 ≤ y →
      |gaugeMertensSum (finiteFlip F) y - 1 * Real.log y| ≤
        Real.log 4 + 4 + 2 * ∑ p ∈ F, Real.log p / ((p : ℝ) - 1) := by
  refine ⟨finiteFlip_isSignGauge F, fun y hy => ?_⟩
  have hmert := RHTower.Mertens.mertens_first y hy
  -- `A_ε − A = Σ_t (ε(t) − 1)Λ(t)/t`, supported on the prime powers of `F`
  have hdiff : |gaugeMertensSum (finiteFlip F) y - ∑ t ∈ Icc 1 y, Λ t / t| ≤
      2 * ∑ p ∈ F, Real.log p / ((p : ℝ) - 1) := by
    have hrw : gaugeMertensSum (finiteFlip F) y - ∑ t ∈ Icc 1 y, Λ t / t =
        ∑ t ∈ Icc 1 y, (finiteFlip F t - 1) * Λ t / t := by
      rw [gaugeMertensSum, ← sum_sub_distrib]
      exact sum_congr rfl fun t _ => by ring
    rw [hrw]
    have hterm : ∀ t ∈ Icc 1 y, |(finiteFlip F t - 1) * Λ t / t| ≤
        2 * ∑ p ∈ F, (if p ∣ t then Λ t / t else 0) := by
      intro t ht
      have ht0 : (0 : ℝ) < t := by exact_mod_cast (mem_Icc.mp ht).1
      by_cases hcop : ∀ p ∈ F, ¬ p ∣ t
      · rw [finiteFlip_eq_one_of_coprime hcop, sub_self, zero_mul, zero_div, abs_zero]
        exact mul_nonneg (by norm_num) (sum_nonneg fun p _ => by
          split_ifs
          · exact div_nonneg vonMangoldt_nonneg ht0.le
          · exact le_rfl)
      · push Not at hcop
        obtain ⟨p, hp, hpt⟩ := hcop
        have hle : Λ t / t ≤ ∑ p ∈ F, (if p ∣ t then Λ t / t else 0) := by
          rw [← sum_erase_add _ _ hp, if_pos hpt]
          have : 0 ≤ ∑ q ∈ F.erase p, (if q ∣ t then Λ t / t else 0) :=
            sum_nonneg fun q _ => by
              split_ifs
              · exact div_nonneg vonMangoldt_nonneg ht0.le
              · exact le_rfl
          linarith
        rw [mul_div_assoc, abs_mul, abs_of_nonneg (div_nonneg vonMangoldt_nonneg ht0.le)]
        exact mul_le_mul (abs_finiteFlip_sub_one_le F t) hle (div_nonneg vonMangoldt_nonneg ht0.le)
          (by norm_num)
    calc |∑ t ∈ Icc 1 y, (finiteFlip F t - 1) * Λ t / t|
        ≤ ∑ t ∈ Icc 1 y, |(finiteFlip F t - 1) * Λ t / t| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ t ∈ Icc 1 y, 2 * ∑ p ∈ F, (if p ∣ t then Λ t / t else 0) := sum_le_sum hterm
      _ = 2 * ∑ p ∈ F, ∑ t ∈ Icc 1 y, (if p ∣ t then Λ t / t else 0) := by
          rw [← mul_sum, sum_comm]
      _ ≤ 2 * ∑ p ∈ F, Real.log p / ((p : ℝ) - 1) :=
          mul_le_mul_of_nonneg_left (sum_le_sum fun p hp =>
            sum_dvd_vonMangoldt_div_le (hF p hp) _) (by norm_num)
  rw [one_mul, abs_le]
  rw [abs_le] at hmert hdiff
  constructor <;> linarith

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
