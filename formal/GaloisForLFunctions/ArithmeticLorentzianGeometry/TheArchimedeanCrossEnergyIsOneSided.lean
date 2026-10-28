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
      _ = m / ((n : ℝ) - m) + 1 := by
          have hnm : (n : ℝ) - m ≠ 0 := by linarith
          rw [one_div_div, div_add_one hnm]; congr 1; ring
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
      _ = m / ((m : ℝ) - n) := by rw [one_div_div]
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
    rw [h2, show 2 * Real.sqrt q / Real.exp 1 = 2 * (Real.sqrt q / Real.exp 1) by ring]
    linarith
  have hsq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt (by linarith)
  have he := Real.exp_pos 1
  have : 2 * Real.sqrt q * Real.log q ≤ 4 / Real.exp 1 * q := by
    calc 2 * Real.sqrt q * Real.log q ≤ 2 * Real.sqrt q * (2 * Real.sqrt q / Real.exp 1) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = 4 / Real.exp 1 * q := by
          rw [show 2 * Real.sqrt q * (2 * Real.sqrt q / Real.exp 1) =
            4 / Real.exp 1 * (Real.sqrt q * Real.sqrt q) by ring, hsq]
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
  rw [hedge, poleDefect, mul_sum, mul_sum, ← sum_add_distrib]
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

/-! ### The sharp cross penalty -/

/-- `u(c + log(1/u)) ≤ c` for `0 < u ≤ 1`, `c ≥ 1`: in particular
`(m/N)(1 + log(N + 1)) ≤ (m/N) log m + 1 + log 2`. -/
theorem div_mul_one_add_log_le {N m : ℕ} (hm1 : 1 ≤ m) (hmN : m ≤ N) :
    (m : ℝ) / N * (1 + Real.log (N + 1)) ≤ (m : ℝ) / N * Real.log m + (1 + Real.log 2) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmN' : (m : ℝ) ≤ N := by exact_mod_cast hmN
  set u := (m : ℝ) / N with hu
  have hu0 : 0 < u := by positivity
  have hu1 : u ≤ 1 := (div_le_one hN0).mpr hmN'
  -- `log(N + 1) − log m ≤ log 2 + log(1/u)`
  have hlog : Real.log (N + 1) - Real.log m ≤ Real.log 2 + Real.log (1 / u) := by
    rw [← Real.log_mul (by norm_num) (by positivity), ← Real.log_div (by positivity) hm0.ne']
    refine Real.log_le_log (by positivity) ?_
    have : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    rw [hu, one_div_div, show (2 : ℝ) * (N / m) = 2 * N / m by ring]
    exact div_le_div_of_nonneg_right (by linarith) hm0.le
  -- `u log(1/u) ≤ 1 − u`
  have hent : u * Real.log (1 / u) ≤ 1 - u := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 1 / u by positivity)
    have : u * Real.log (1 / u) ≤ u * (1 / u - 1) := mul_le_mul_of_nonneg_left h hu0.le
    rw [mul_sub, mul_one_div_cancel hu0.ne', mul_one] at this
    exact this
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have : u * (1 + Real.log (N + 1)) = u * Real.log m + u * (1 + Real.log (N + 1) - Real.log m) := by
    ring
  rw [this]
  have h2 : u * (1 + Real.log (N + 1) - Real.log m) ≤ u * (1 + Real.log 2 + Real.log (1 / u)) :=
    mul_le_mul_of_nonneg_left (by linarith) hu0.le
  nlinarith

/-- The cross constant `L_λ,κ = (2(1 + λ)B_ψ + 2(1 + log 2) + 1)/(1 − κ) + 2`. -/
def crossConstant (lam κ : ℝ) : ℝ :=
  (2 * (1 + lam) * psiConstant + 2 * (1 + Real.log 2) + 1) / (1 - κ) + 2

/-- **The sharp cross penalty.** For a window test at `w ≤ κ δ_N`, `0 ≤ κ ≤ 1/2`, and `λ > 0`,
`levyEnergy f ≥ Σ_m levyEnergy G_m − wN [(2(1 + 1/λ)/(1 − κ)) D_N(y) + L_λ,κ |y|²]`. -/
theorem levyEnergy_windowTest_ge_sharp (hG : ∀ n, ContDiff ℝ 2 (G n))
    (hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 2) (hwκ : w ≤ κ * atomSpacing N) {lam : ℝ}
    (hlam : 0 < lam) :
    ∑ m ∈ Icc 1 N, levyEnergy (G m) -
        w * N * (2 * (1 + 1 / lam) / (1 - κ) * poleDefect N (windowNorm G) +
          crossConstant lam κ * ∑ n ∈ Icc 1 N, windowNorm G n ^ 2) ≤
      levyEnergy (windowTest N G) := by
  have hδ := atomSpacing_pos hN
  have hw2 : w ≤ atomSpacing N / 2 := by nlinarith
  have hmaster := levyEnergy_windowTest_ge_windows hG hGsupp hN hw0 hw2
  set y := windowNorm G
  have hy0 : ∀ n, 0 ≤ y n := windowNorm_nonneg G
  have hκ1 : 0 < 1 - κ := by linarith
  set W : ℕ → ℕ → ℝ := fun m n => ∫ t in Set.Ioi 0,
    (Set.Icc (Real.log n - Real.log m - w) (Real.log n - Real.log m + w)).indicator
      archLevyDensity t
  -- the symmetric kernel `k_mn = 2w(1/(2(1 − κ)|log(n/m)|) + 1)`
  set k : ℕ → ℕ → ℝ := fun m n =>
    2 * w * (1 / (2 * (1 - κ) * |Real.log n - Real.log m|) + 1)
  have hk0 : ∀ m n, 0 ≤ k m n := fun m n =>
    mul_nonneg (by positivity) (add_nonneg (one_div_nonneg.mpr
      (mul_nonneg (mul_nonneg two_pos.le hκ1.le) (abs_nonneg _))) zero_le_one)
  have hks : ∀ m n, k n m = k m n := fun m n => by simp only [k, abs_sub_comm]
  -- `W_mn + W_nm ≤ k_mn`: one of the two windows lies left of the origin
  have hWW : ∀ m ∈ Icc 1 N, ∀ n ∈ Icc 1 N, m ≠ n → W m n + W n m ≤ k m n := by
    intro m hm n hn hmn
    have hsep := atomSpacing_le_abs_logGap hm hn hmn
    simp only [logGap] at hsep
    have hwsep : w ≤ κ * |Real.log n - Real.log m| :=
      hwκ.trans (mul_le_mul_of_nonneg_left hsep hκ0)
    have hpos : ∀ s : ℝ, 2 * w ≤ s → w ≤ κ * s →
        2 * w * archLevyDensity (s - w) ≤ 2 * w * (1 / (2 * (1 - κ) * s) + 1) := by
      intro s hs hws
      have hsw : 0 < s - w := by linarith
      have h1 := archLevyDensity_le_inv_add_one hsw
      have h2 : 1 / (2 * (s - w)) ≤ 1 / (2 * (1 - κ) * s) :=
        one_div_le_one_div_of_le (mul_pos (mul_pos two_pos hκ1) (by linarith)) (by nlinarith)
      nlinarith
    have hs2 : 2 * w ≤ |Real.log n - Real.log m| := by linarith
    rcases le_or_gt (Real.log n - Real.log m) 0 with hneg | hposs
    · -- `n < m`: the window of `(m, n)` is left of the origin, that of `(n, m)` right
      have e : |Real.log n - Real.log m| = Real.log m - Real.log n := by
        rw [abs_of_nonpos hneg]; ring
      rw [e] at hwsep hs2
      have h1 : W m n = 0 := window_integral_eq_zero_of_neg hw0 (by linarith)
      have h2 : W n m ≤ 2 * w * archLevyDensity (Real.log m - Real.log n - w) :=
        window_integral_le_of_pos hw0 hs2
      have h3 := hpos (Real.log m - Real.log n) hs2 hwsep
      show W m n + W n m ≤ 2 * w * (1 / (2 * (1 - κ) * |Real.log n - Real.log m|) + 1)
      rw [e]
      linarith
    · have e : |Real.log n - Real.log m| = Real.log n - Real.log m := abs_of_pos hposs
      rw [e] at hwsep hs2
      have h1 : W n m = 0 := window_integral_eq_zero_of_neg hw0 (by linarith)
      have h2 : W m n ≤ 2 * w * archLevyDensity (Real.log n - Real.log m - w) :=
        window_integral_le_of_pos hw0 hs2
      have h3 := hpos (Real.log n - Real.log m) hs2 hwsep
      show W m n + W n m ≤ 2 * w * (1 / (2 * (1 - κ) * |Real.log n - Real.log m|) + 1)
      rw [e]
      linarith
  -- symmetrize the window sum
  set S := ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then 0 else |y m| * |y n| * W m n)
  have hswap : S = ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then 0 else |y m| * |y n| * W n m) := by
    simp only [S]
    rw [sum_comm]
    refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => ?_
    by_cases h : n = m
    · simp [h]
    · rw [if_neg h, if_neg (Ne.symm h), mul_comm |y n|]
  have hS : 2 * S ≤ ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then 0 else |y m| * |y n| * k m n) := by
    have : 2 * S = ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        (if m = n then 0 else |y m| * |y n| * (W m n + W n m)) := by
      rw [two_mul]
      nth_rewrite 2 [hswap]
      simp only [S, ← sum_add_distrib]
      refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => ?_
      split_ifs <;> ring
    rw [this]
    refine sum_le_sum fun m hm => sum_le_sum fun n hn => ?_
    split_ifs with h
    · exact le_rfl
    · exact mul_le_mul_of_nonneg_left (hWW m hm n hn h) (by positivity)
  have hschur := RenormalizedArithmeticPotentialTheory.sum_abs_mul_sym_le N y k hk0 hks
  -- the rows
  have hrow : ∀ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then 0 else k m n) ≤
      w / (1 - κ) * (2 * m * (1 + Real.log (N + 1)) + N) + 2 * w * N := by
    intro m hm
    have hr := sum_inv_abs_log_sub_le hm
    have e : ∀ n ∈ Icc 1 N, (if m = n then 0 else k m n) ≤
        w / (1 - κ) * (if m = n then 0 else 1 / |Real.log n - Real.log m|) + 2 * w := by
      intro n _
      split_ifs
      · positivity
      · simp only [k]
        have : 2 * w * (1 / (2 * (1 - κ) * |Real.log n - Real.log m|)) =
            w / (1 - κ) * (1 / |Real.log n - Real.log m|) := by
          field_simp
        nlinarith
    have hconst : ∑ n ∈ Icc 1 N, (2 * w) = 2 * w * N := by
      rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
    calc ∑ n ∈ Icc 1 N, (if m = n then 0 else k m n)
        ≤ ∑ n ∈ Icc 1 N, (w / (1 - κ) * (if m = n then 0 else 1 / |Real.log n - Real.log m|) +
            2 * w) := sum_le_sum e
      _ = w / (1 - κ) * ∑ n ∈ Icc 1 N, (if m = n then 0 else 1 / |Real.log n - Real.log m|) +
            2 * w * N := by rw [sum_add_distrib, ← mul_sum, hconst]
      _ ≤ w / (1 - κ) * (2 * m * (1 + Real.log (N + 1)) + N) + 2 * w * N := by
          gcongr
  -- assemble: rows, top atoms, defect
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hrow' : ∀ m ∈ Icc 1 N, y m ^ 2 * ∑ n ∈ Icc 1 N, (if m = n then 0 else k m n) ≤
      w * N / (1 - κ) * (2 * ((m : ℝ) / N * Real.log m * y m ^ 2) +
        (2 * (1 + Real.log 2) + 1) * y m ^ 2) + 2 * w * N * y m ^ 2 := by
    intro m hm
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
    have h1 := hrow m hm
    have h2 := div_mul_one_add_log_le hm1 hmN
    have hym := sq_nonneg (y m)
    have e : w / (1 - κ) * (2 * m * (1 + Real.log (N + 1)) + N) =
        w * N / (1 - κ) * (2 * ((m : ℝ) / N * (1 + Real.log (N + 1))) + 1) := by
      field_simp
    calc y m ^ 2 * ∑ n ∈ Icc 1 N, (if m = n then 0 else k m n)
        ≤ y m ^ 2 * (w / (1 - κ) * (2 * m * (1 + Real.log (N + 1)) + N) + 2 * w * N) :=
          mul_le_mul_of_nonneg_left h1 hym
      _ = w * N / (1 - κ) * (2 * ((m : ℝ) / N * (1 + Real.log (N + 1))) + 1) * y m ^ 2 +
            2 * w * N * y m ^ 2 := by rw [e]; ring
      _ ≤ w * N / (1 - κ) * (2 * ((m : ℝ) / N * Real.log m + (1 + Real.log 2)) + 1) * y m ^ 2 +
            2 * w * N * y m ^ 2 := by gcongr
      _ = _ := by ring
  have htop := sum_top_le_poleDefect_param N y hlam
  have hsum : ∑ m ∈ Icc 1 N, y m ^ 2 * ∑ n ∈ Icc 1 N, (if m = n then 0 else k m n) ≤
      w * N / (1 - κ) * (2 * ∑ n ∈ Icc 1 N, (n : ℝ) / N * Real.log n * y n ^ 2 +
        (2 * (1 + Real.log 2) + 1) * ∑ n ∈ Icc 1 N, y n ^ 2) +
        2 * w * N * ∑ n ∈ Icc 1 N, y n ^ 2 := by
    refine (sum_le_sum hrow').trans (le_of_eq ?_)
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_add_distrib, ← mul_sum, ← mul_sum]
  have habs : ∀ m n, |y m| * |y n| = y m * y n := fun m n => by
    rw [abs_of_nonneg (hy0 m), abs_of_nonneg (hy0 n)]
  have hcoef : 0 ≤ w * N / (1 - κ) := by positivity
  have hD := poleDefect_nonneg N y
  have hX : 0 ≤ ∑ n ∈ Icc 1 N, y n ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hfin : 2 * S ≤ w * N * (2 * (1 + 1 / lam) / (1 - κ) * poleDefect N y +
      crossConstant lam κ * ∑ n ∈ Icc 1 N, y n ^ 2) := by
    have h1 := hS.trans hschur
    have h2 := h1.trans hsum
    have h3 : w * N / (1 - κ) * (2 * ∑ n ∈ Icc 1 N, (n : ℝ) / N * Real.log n * y n ^ 2) ≤
        w * N / (1 - κ) * (2 * ((1 + 1 / lam) * poleDefect N y +
          (1 + lam) * psiConstant * ∑ n ∈ Icc 1 N, y n ^ 2)) :=
      mul_le_mul_of_nonneg_left (by linarith) hcoef
    have e : w * N * (2 * (1 + 1 / lam) / (1 - κ) * poleDefect N y +
        crossConstant lam κ * ∑ n ∈ Icc 1 N, y n ^ 2) =
        w * N / (1 - κ) * (2 * ((1 + 1 / lam) * poleDefect N y +
          (1 + lam) * psiConstant * ∑ n ∈ Icc 1 N, y n ^ 2)) +
        w * N / (1 - κ) * ((2 * (1 + Real.log 2) + 1) * ∑ n ∈ Icc 1 N, y n ^ 2) +
        2 * w * N * ∑ n ∈ Icc 1 N, y n ^ 2 := by
      unfold crossConstant; field_simp; ring
    rw [e]
    nlinarith
  linarith

/-! ### The Markov form at the sharp cross penalty -/

/-- The self-energy of a window with its shape term:
`levyEnergy G ≥ (log(1/w) + 2c_∞ − (e^{1/2}/2) w) ‖G‖² + β(G)`. -/
theorem levyEnergy_profile_ge_shape {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw0 : 0 < w) (hw1 : w ≤ 1) :
    (Real.log (1 / w) + archRobinConstant - Real.exp (1 / 2) / 2 * w) * (∫ u, g u ^ 2) +
      bumpRobin g w ≤ levyEnergy g := by
  have hgc : HasCompactSupport g := HasCompactSupport.intro isCompact_Icc hgsupp
  obtain ⟨C, hC⟩ := hg.lipschitzWith_of_hasCompactSupport hgc two_ne_zero
  have hK : ∀ u v, |g u - g v| ≤ (C : ℝ) * |u - v| := fun u v => by
    simpa [Real.dist_eq] using hC.dist_le_mul u v
  have h := abs_levyEnergy_atom_sub_le hg hgc hgsupp hw0 hw1 hK
  have := (abs_le.mp h).1
  linarith

/-- **The Markov form of a window test at the sharp cross penalty.** For `ε > 0`, `0 ≤ κ ≤ 1/2`,
`λ > 0`, eventually in `N`: every window test at `w ≤ κ δ_N` whose profiles have shape term
`β(G_n) ≥ β ‖G_n‖²` satisfies `M(f) ≥ φ₀ |y|² + c₀ D_N(y)` with
`φ₀ = 2θ′(0) + log(1/(wN)) + 2c_∞ + β + γ − ε − (e^{1/2}/2) w − L_λ,κ wN` and
`c₀ = 1 − ε − (2(1 + 1/λ)/(1 − κ)) wN`. -/
theorem eventually_markovEnergy_windowTest_ge_sharp {ε : ℝ} (hε : 0 < ε) {κ : ℝ} (hκ0 : 0 ≤ κ)
    (hκ : κ ≤ 1 / 2) {lam : ℝ} (hlam : 0 < lam) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ w : ℝ, 0 < w → w ≤ κ * atomSpacing N →
      ∀ G : ℕ → ℝ → ℝ, (∀ n, ContDiff ℝ 2 (G n)) → (∀ n u, u ∉ Set.Icc 0 w → G n u = 0) →
      ∀ β : ℝ, (∀ n, β * ∫ u, G n u ^ 2 ≤ bumpRobin (G n) w) →
        (2 * gammaHardyPhaseRate 0 + Real.log (1 / (w * N)) + archRobinConstant + β +
            Real.eulerMascheroniConstant - ε - Real.exp (1 / 2) / 2 * w -
            crossConstant lam κ * (w * N)) * (∑ n ∈ Icc 1 N, windowNorm G n ^ 2) +
          (1 - ε - 2 * (1 + 1 / lam) / (1 - κ) * (w * N)) * poleDefect N (windowNorm G) ≤
          markovEnergy (fun u => (windowTest N G u : ℂ)) := by
  obtain ⟨N₁, hN₁⟩ := eventually_atomicWeilForm_add_poleDefect_le hε
  refine ⟨max N₁ 1, fun N hN w hw0 hw G hG hGsupp β hβ => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hδ := atomSpacing_pos hN1
  have hδ1 := atomSpacing_le_one hN1
  have hw2 : w ≤ atomSpacing N / 2 := by nlinarith
  have hw' : w < atomSpacing N := by linarith
  have hw1 : w ≤ 1 := by linarith
  have hf := contDiff_windowTest hG N
  have hfc := hasCompactSupport_windowTest hGsupp N
  rw [markovEnergy_ofReal_eq_archForm_sub_primeSum hf hfc, archForm_eq_levyEnergy hf hfc,
    integral_windowTest_sq hG hGsupp hw']
  have hy : ∑ n ∈ Icc 1 N, ∫ u, G n u ^ 2 = ∑ n ∈ Icc 1 N, windowNorm G n ^ 2 :=
    sum_congr rfl fun n _ => (windowNorm_sq G n).symm
  rw [hy]
  have hlevy := levyEnergy_windowTest_ge_sharp hG hGsupp hN1 hw0 hκ0 hκ hw hlam
  have hP := hN₁ N (le_trans (le_max_left _ _) hN) (windowNorm G)
  have hprime := primeSum_windowTest_le hG hGsupp hw'
  have hself : (Real.log (1 / w) + archRobinConstant + β - Real.exp (1 / 2) / 2 * w) *
      (∑ n ∈ Icc 1 N, windowNorm G n ^ 2) ≤ ∑ m ∈ Icc 1 N, levyEnergy (G m) := by
    rw [mul_sum]
    refine sum_le_sum fun n _ => ?_
    rw [windowNorm_sq]
    have h1 := levyEnergy_profile_ge_shape (hG n) (hGsupp n) hw0 hw1
    have h2 := hβ n
    nlinarith
  have hlog : Real.log (1 / (w * N)) = Real.log (1 / w) - Real.log N := by
    rw [one_div, Real.log_inv, Real.log_mul hw0.ne' hN0.ne', one_div, Real.log_inv]; ring
  rw [hlog]
  nlinarith

end GaloisForLFunctions.ArithmeticLorentzianGeometry
