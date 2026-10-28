import GaloisForLFunctions.ArithmeticLorentzianGeometry.WeilsFormIsPositiveOnEveryTestNearTheLogarithms

/-!
# The archimedean cross energy is one-sided

The cross energy of a window test enters the Markov form through the pair windows
`[log(n/m) − w, log(n/m) + w]` of the Lévy density on `(0, ∞)`. The bound used so far charges every
ordered pair with `2w(1/|log(n/m)| + 1)` and the rows with `e²`. Its sharp form:

* **One-sidedness** (`window_integral_eq_zero_of_neg`, `window_integral_le_of_pos`): only the
  pairs `m < n` meet at positive shifts. Their window carries at most `2w ω(log(n/m) − w)`, since
  `ω` decreases.
* **Sharp rows** (`sum_inv_abs_log_sub_le`): `Σ_{n ≠ m} 1/|log(n/m)| ≤ 2m(1 + log(N + 1)) + N`,
  from `log(1 + u) ≥ u/(1 + u)`.
* **The top atoms with a parameter** (`sum_top_le_poleDefect_param`): for `λ > 0`,
  `Σ (n/N) log n · x_n² ≤ (1 + 1/λ) D_N(x) + (1 + λ) B_ψ |x|²` with `B_ψ = log 4 + 4/e`
  (`psi_le_psiConstant`).
* **The cross penalty** (`levyEnergy_windowTest_ge_sharp`): at `w ≤ κ δ_N`, `κ < 1`,
  `levyEnergy f ≥ Σ levyEnergy G_m − wN [(2(1 + 1/λ)/(1 − κ)) D_N(y) + L_λ,κ |y|²]` with
  `L_λ,κ = (2(1 + λ)B_ψ + 2(1 + log 2) + 1)/(1 − κ) + 2`. The constants that limited the stability
  regime to `K★ ≈ 6·10⁻⁴` were `236` and `1517`; here they are about `6.7` and `16` at `λ = 1/2`,
  `κ = 1/10`.
-/

noncomputable section

open MeasureTheory Finset RHTower
open scoped ArithmeticFunction.vonMangoldt

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

open GaloisForLFunctions.SpacingScaleHarmonicAnalysis GaloisForLFunctions.ArithmeticElectrostatics
  GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

/-! ### One-sided windows -/

/-- A pair window to the left of the origin carries no Lévy mass on `(0, ∞)`. -/
theorem window_integral_eq_zero_of_neg {s w : ℝ} (hw0 : 0 < w) (hs : s ≤ -(2 * w)) :
    ∫ t in Set.Ioi 0, (Set.Icc (s - w) (s + w)).indicator archLevyDensity t = 0 :=
  setIntegral_eq_zero_of_forall_eq_zero fun t ht => Set.indicator_of_notMem
    (fun h => by have := h.2; have : (0 : ℝ) < t := ht; linarith) _

/-- A pair window to the right carries at most `2w ω(s − w)`: `ω` decreases on `(0, ∞)`. -/
theorem window_integral_le_of_pos {s w : ℝ} (hw0 : 0 < w) (hs : 2 * w ≤ s) :
    ∫ t in Set.Ioi 0, (Set.Icc (s - w) (s + w)).indicator archLevyDensity t ≤
      2 * w * archLevyDensity (s - w) := by
  have hsub : Set.Icc (s - w) (s + w) ⊆ Set.Ioi 0 := fun t ht => by
    have := ht.1; show (0 : ℝ) < t; linarith
  rw [setIntegral_indicator measurableSet_Icc, Set.inter_eq_right.mpr hsub]
  have hcont : ContinuousOn archLevyDensity (Set.Icc (s - w) (s + w)) :=
    continuousOn_archLevyDensity_Ioi.mono hsub
  have hle : ∫ t in Set.Icc (s - w) (s + w), archLevyDensity t ≤
      ∫ t in Set.Icc (s - w) (s + w), archLevyDensity (s - w) :=
    setIntegral_mono_on hcont.integrableOn_Icc (integrableOn_const (by simp)) measurableSet_Icc
      fun t ht => archLevyDensity_antitoneOn (show (0 : ℝ) < s - w by linarith)
        (show (0 : ℝ) < t by linarith [ht.1]) ht.1
  rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul] at hle
  linarith

/-! ### Sharp rows -/

/-- `1/log(n/m) ≤ 1 + m/(n − m)` for `n > m` and `1/log(m/n) ≤ m/(m − n)` for `n < m`: so
`1/|log n − log m| ≤ m/|n − m| + 1`. -/
theorem inv_abs_log_sub_le {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : m ≠ n) :
    1 / |Real.log n - Real.log m| ≤ m / |(n : ℝ) - m| + 1 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · have hlt' : (m : ℝ) < n := by exact_mod_cast hlt
    -- `log(n/m) ≥ 1 − m/n = (n − m)/n`
    have hlog : ((n : ℝ) - m) / n ≤ Real.log n - Real.log m := by
      have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < n / m by positivity)
      rw [Real.log_div hn0.ne' hm0.ne', inv_div] at h
      have : 1 - (m : ℝ) / n = ((n : ℝ) - m) / n := by field_simp
      linarith
    have hpos : 0 < ((n : ℝ) - m) / n := div_pos (by linarith) hn0
    rw [abs_of_pos (hpos.trans_le hlog), abs_of_pos (by linarith : (0 : ℝ) < n - m)]
    calc 1 / (Real.log n - Real.log m) ≤ 1 / (((n : ℝ) - m) / n) :=
          one_div_le_one_div_of_le hpos hlog
      _ = m / ((n : ℝ) - m) + 1 := by field_simp; ring
  · have hgt' : (n : ℝ) < m := by exact_mod_cast hgt
    have hlog : ((m : ℝ) - n) / m ≤ Real.log m - Real.log n := by
      have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < m / n by positivity)
      rw [Real.log_div hm0.ne' hn0.ne', inv_div] at h
      have : 1 - (n : ℝ) / m = ((m : ℝ) - n) / m := by field_simp
      linarith
    have hpos : 0 < ((m : ℝ) - n) / m := div_pos (by linarith) hm0
    rw [abs_sub_comm, abs_of_pos (hpos.trans_le hlog), abs_sub_comm,
      abs_of_pos (by linarith : (0 : ℝ) < m - n)]
    calc 1 / (Real.log m - Real.log n) ≤ 1 / (((m : ℝ) - n) / m) :=
          one_div_le_one_div_of_le hpos hlog
      _ = m / ((m : ℝ) - n) := by field_simp
      _ ≤ m / ((m : ℝ) - n) + 1 := by linarith

/-- **Sharp rows**: `Σ_{n ≠ m} 1/|log n − log m| ≤ 2m(1 + log(N + 1)) + N`. -/
theorem sum_inv_abs_log_sub_le {N m : ℕ} (hm : m ∈ Icc 1 N) :
    ∑ n ∈ Icc 1 N, (if m = n then 0 else 1 / |Real.log n - Real.log m|) ≤
      2 * m * (1 + Real.log (N + 1)) + N := by
  obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
  have hterm : ∀ n ∈ Icc 1 N, (if m = n then 0 else 1 / |Real.log n - Real.log m|) ≤
      (if n = m then 0 else (m : ℝ) * (1 / |(n : ℝ) - m|)) + 1 := by
    intro n hn
    by_cases hmn : m = n
    · subst hmn; simp
    rw [if_neg hmn, if_neg (Ne.symm hmn)]
    have := inv_abs_log_sub_le hm1 (Finset.mem_Icc.mp hn).1 hmn
    rw [mul_one_div]; exact this
  have hsub : (Icc 1 N).erase m ⊆ (range (N + 1)).erase m := fun n hn => by
    rw [mem_erase] at hn ⊢
    exact ⟨hn.1, mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hn.2).2)⟩
  have hrow := RHTower.Sieve.sum_inv_abs_int_dist_le (N := N + 1) (m := m) (by omega)
  push_cast at hrow
  have hharm : ∑ n ∈ Icc 1 N, (if n = m then 0 else (m : ℝ) * (1 / |(n : ℝ) - m|)) ≤
      m * (2 * (1 + Real.log (N + 1))) := by
    calc ∑ n ∈ Icc 1 N, (if n = m then 0 else (m : ℝ) * (1 / |(n : ℝ) - m|))
        = ∑ n ∈ (Icc 1 N).erase m, (m : ℝ) * (1 / |(n : ℝ) - m|) := by
          rw [← sum_erase_add _ _ hm, if_pos rfl, add_zero]
          exact sum_congr rfl fun n hn => if_neg (ne_of_mem_erase hn)
      _ ≤ ∑ n ∈ (range (N + 1)).erase m, (m : ℝ) * (1 / |(n : ℝ) - m|) :=
          sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ = m * ∑ n ∈ (range (N + 1)).erase m, 1 / |(n : ℝ) - m| := by rw [mul_sum]
      _ ≤ m * (2 * (1 + Real.log (N + 1))) :=
          mul_le_mul_of_nonneg_left hrow (by positivity)
  have hconst : ∑ n ∈ Icc 1 N, (1 : ℝ) = N := by
    rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
  calc ∑ n ∈ Icc 1 N, (if m = n then 0 else 1 / |Real.log n - Real.log m|)
      ≤ ∑ n ∈ Icc 1 N, ((if n = m then 0 else (m : ℝ) * (1 / |(n : ℝ) - m|)) + 1) :=
        sum_le_sum hterm
    _ = ∑ n ∈ Icc 1 N, (if n = m then 0 else (m : ℝ) * (1 / |(n : ℝ) - m|)) + N := by
        rw [sum_add_distrib, hconst]
    _ ≤ 2 * m * (1 + Real.log (N + 1)) + N := by linarith

/-! ### The top atoms with a parameter -/

/-- The Chebyshev constant `B_ψ = log 4 + 4/e`. -/
def psiConstant : ℝ := Real.log 4 + 4 / Real.exp 1

theorem psiConstant_pos : 0 < psiConstant := by
  unfold psiConstant
  have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
  positivity

/-- `log y ≤ y/e` for `y > 0`. -/
theorem log_le_div_exp_one {y : ℝ} (hy : 0 < y) : Real.log y ≤ y / Real.exp 1 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < y / Real.exp 1 by positivity)
  rw [Real.log_div hy.ne' (Real.exp_pos 1).ne', Real.log_exp] at h
  linarith

/-- **Chebyshev's bound** `ψ(q) ≤ (log 4 + 4/e) q` for `q ≥ 1`: `2√q log q ≤ 4q/e`. -/
theorem psi_le_psiConstant {q : ℝ} (hq : 1 ≤ q) : Chebyshev.psi q ≤ psiConstant * q := by
  have h := Chebyshev.psi_le hq
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr (by linarith)
  have hlog : Real.log q ≤ 2 * Real.sqrt q / Real.exp 1 := by
    have h1 := log_le_div_exp_one hs
    have h2 : Real.log q = 2 * Real.log (Real.sqrt q) := by
      rw [← Real.log_rpow hs, Real.rpow_two, Real.sq_sqrt (by linarith)]
    rw [h2]; linarith
  have hsq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt (by linarith)
  have he := Real.exp_pos 1
  have : 2 * Real.sqrt q * Real.log q ≤ 4 / Real.exp 1 * q := by
    calc 2 * Real.sqrt q * Real.log q ≤ 2 * Real.sqrt q * (2 * Real.sqrt q / Real.exp 1) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = 4 / Real.exp 1 * q := by rw [← hsq]; field_simp; ring
  unfold psiConstant
  linarith

/-- **The defect pays the top atoms, with a parameter**: for `λ > 0`,
`Σ_n (n/N) log n · x_n² ≤ (1 + 1/λ) D_N(x) + (1 + λ) B_ψ |x|²`. On each edge
`a² ≤ (1 + 1/λ)(a − b)² + (1 + λ) b²` with `a = x_{mt}`, `b = x_m/√t`. -/
theorem sum_top_le_poleDefect_param (N : ℕ) (x : ℕ → ℝ) {lam : ℝ} (hlam : 0 < lam) :
    ∑ n ∈ Icc 1 N, (n : ℝ) / N * Real.log n * x n ^ 2 ≤
      (1 + 1 / lam) * poleDefect N x + (1 + lam) * psiConstant * ∑ n ∈ Icc 1 N, x n ^ 2 := by
  have hedge : ∑ n ∈ Icc 1 N, (n : ℝ) / N * Real.log n * x n ^ 2 =
      ∑ m ∈ Icc 1 N, ∑ t ∈ Icc 1 (N / m), ((m * t : ℕ) : ℝ) / N * Λ t * x (m * t) ^ 2 := by
    have h := sum_edges_eq_sum_divisors N (fun n t => (n : ℝ) / N * Λ t * x n ^ 2)
    rw [h]
    exact sum_congr rfl fun n _ => by
      rw [← sum_mul, ← mul_sum, ArithmeticFunction.vonMangoldt_sum]
  have hpt : ∀ m ∈ Icc 1 N, ∀ t ∈ Icc 1 (N / m),
      ((m * t : ℕ) : ℝ) / N * Λ t * x (m * t) ^ 2 ≤
        (1 + 1 / lam) * (Λ t * (x (m * t) - x m / Real.sqrt t) ^ 2) +
          (1 + lam) * ((m : ℝ) / N * Λ t * x m ^ 2) := by
    intro m hm t ht
    have hm1 := (Finset.mem_Icc.mp hm).1
    have ht1 := (Finset.mem_Icc.mp ht).1
    have htm := (Finset.mem_Icc.mp ht).2
    have hN0 : (0 : ℝ) < N := by
      exact_mod_cast (show 0 < N by have := (Finset.mem_Icc.mp hm).2; omega)
    have ht0 : (0 : ℝ) < t := by exact_mod_cast ht1
    have hmtN : ((m * t : ℕ) : ℝ) ≤ N := by
      have : m * t ≤ N := by rw [Nat.le_div_iff_mul_le hm1] at htm; linarith [Nat.mul_comm t m]
      exact_mod_cast this
    have hr0 : 0 ≤ ((m * t : ℕ) : ℝ) / N := by positivity
    have hr1 : ((m * t : ℕ) : ℝ) / N ≤ 1 := (div_le_one hN0).mpr hmtN
    have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := t)
    set a := x (m * t)
    set b := x m / Real.sqrt t
    have hb : b ^ 2 = x m ^ 2 / t := by simp only [b]; rw [div_pow, Real.sq_sqrt ht0.le]
    -- `a² ≤ (1 + 1/λ)(a − b)² + (1 + λ) b²`
    have hsq : a ^ 2 ≤ (1 + 1 / lam) * (a - b) ^ 2 + (1 + lam) * b ^ 2 := by
      have hk : (1 + 1 / lam) * (a - b) ^ 2 + (1 + lam) * b ^ 2 - a ^ 2 =
          ((a - b) - lam * b) ^ 2 / lam := by field_simp; ring
      have : 0 ≤ ((a - b) - lam * b) ^ 2 / lam := div_nonneg (sq_nonneg _) hlam.le
      linarith
    have hcast : ((m * t : ℕ) : ℝ) / N * (x m ^ 2 / t) = (m : ℝ) / N * x m ^ 2 := by
      push_cast; field_simp
    have hD : 0 ≤ Λ t * (a - b) ^ 2 := mul_nonneg hΛ (sq_nonneg _)
    have h1 : 0 ≤ 1 + 1 / lam := by positivity
    calc ((m * t : ℕ) : ℝ) / N * Λ t * a ^ 2
        ≤ ((m * t : ℕ) : ℝ) / N * Λ t * ((1 + 1 / lam) * (a - b) ^ 2 + (1 + lam) * b ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (mul_nonneg hr0 hΛ)
      _ = (1 + 1 / lam) * (((m * t : ℕ) : ℝ) / N * (Λ t * (a - b) ^ 2)) +
            (1 + lam) * (Λ t * (((m * t : ℕ) : ℝ) / N * (x m ^ 2 / t))) := by rw [hb]; ring
      _ ≤ (1 + 1 / lam) * (Λ t * (a - b) ^ 2) +
            (1 + lam) * ((m : ℝ) / N * Λ t * x m ^ 2) := by
          rw [hcast]
          have := mul_le_mul_of_nonneg_right hr1 hD
          nlinarith [mul_le_mul_of_nonneg_left (this.trans_eq (one_mul _)) h1]
  have hrow : ∀ m ∈ Icc 1 N, ∑ t ∈ Icc 1 (N / m), (m : ℝ) / N * Λ t * x m ^ 2 ≤
      psiConstant * x m ^ 2 := by
    intro m hm
    have hm1 := (Finset.mem_Icc.mp hm).1
    have hmN := (Finset.mem_Icc.mp hm).2
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have hq1 : (1 : ℝ) ≤ ((N / m : ℕ) : ℝ) := by exact_mod_cast Nat.div_pos hmN hm1
    have hqm : (m : ℝ) * ((N / m : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.mul_div_le N m
    rw [show ∑ t ∈ Icc 1 (N / m), (m : ℝ) / N * Λ t * x m ^ 2 =
        (m : ℝ) / N * (∑ t ∈ Icc 1 (N / m), Λ t) * x m ^ 2 by rw [mul_sum, sum_mul],
      sum_vonMangoldt_Icc_eq_psi]
    have hψ := psi_le_psiConstant hq1
    have hfac : (m : ℝ) / N * Chebyshev.psi ((N / m : ℕ) : ℝ) ≤ psiConstant := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hN0]
      nlinarith [mul_le_mul_of_nonneg_left hψ hm0.le, psiConstant_pos]
    exact mul_le_mul_of_nonneg_right hfac (sq_nonneg _)
  rw [hedge, poleDefect, mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun m hm => ?_
  calc ∑ t ∈ Icc 1 (N / m), ((m * t : ℕ) : ℝ) / N * Λ t * x (m * t) ^ 2
      ≤ ∑ t ∈ Icc 1 (N / m), ((1 + 1 / lam) * (Λ t * (x (m * t) - x m / Real.sqrt t) ^ 2) +
          (1 + lam) * ((m : ℝ) / N * Λ t * x m ^ 2)) := sum_le_sum fun t ht => hpt m hm t ht
    _ = (1 + 1 / lam) * ∑ t ∈ Icc 1 (N / m), Λ t * (x (m * t) - x m / Real.sqrt t) ^ 2 +
          (1 + lam) * ∑ t ∈ Icc 1 (N / m), (m : ℝ) / N * Λ t * x m ^ 2 := by
        rw [sum_add_distrib, mul_sum, mul_sum]
    _ ≤ (1 + 1 / lam) * ∑ t ∈ Icc 1 (N / m), Λ t * (x (m * t) - x m / Real.sqrt t) ^ 2 +
          (1 + lam) * psiConstant * x m ^ 2 := by
        have := hrow m hm
        nlinarith

end GaloisForLFunctions.ArithmeticLorentzianGeometry
