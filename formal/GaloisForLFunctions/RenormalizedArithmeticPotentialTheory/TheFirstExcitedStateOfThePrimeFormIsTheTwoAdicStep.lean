import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheSpectralGapOfThePrimeFormIsTwoLogTwo

/-!
# The first excited state of the prime form is the 2-adic step

Below its pole `n^{−1/2}`, Weil's atomic prime form `P_N` has top spectrum
`log N − γ − 2 log 2 + o(1)`, and the 2-adic step realizes it.

* **The 2-adic step** (`twoAdicStep`): `x_n = (1_{2∣n} − E_N/H_N)/√n`, with `H_N = Σ_{n ≤ N} 1/n` and
  `E_N = Σ_{n ≤ N, 2∣n} 1/n`, is orthogonal to the pole, and `|x|² = E_N − E_N²/H_N`.
* **Its defect is exactly the even mass** (`poleDefect_twoAdicStep`): `D_N(x) = log 2 · E_N`. In the
  pole gauge only the edges `m → m 2^k` with `m` odd move the parity, and `Σ_{m odd} Σ_k 1/(m 2^k)`
  is `E_N` by the 2-adic ladders. Since `E_N ≤ H_N/2`, `D_N(x) ≤ 2 log 2 |x|²` for every `N`
  (`poleDefect_twoAdicStep_le`): the Poincaré constant of the multiplicative walk is at most `2 log 2`.
* **Sharpness** (`eventually_exists_atomicWeilForm_ge`): by the ground-state identity and Mertens'
  theorem on the rows, `P_N(x) ≥ (log N − γ − 2 log 2 − ε)|x|²` eventually.
* **The two-sided law** (`eventually_atomicWeilForm_below_pole_two_log_two`): with
  `eventually_atomicWeilForm_le_two_log_two`, the largest eigenvalue of `P_N` on the hyperplane
  orthogonal to its pole is `log N − γ − 2 log 2 + o(1)`.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open GaloisForLFunctions.ArithmeticElectrostatics ArithmeticFunction

local notation "γ" => Real.eulerMascheroniConstant

/-! ### 1. Parity and the even mass -/

/-- The parity indicator `1_{2 ∣ n}`. -/
def parity (n : ℕ) : ℝ := if 2 ∣ n then 1 else 0

/-- The harmonic mass `H_N = Σ_{n ≤ N} 1/n`. -/
def harmonicMass (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, 1 / (n : ℝ)

/-- The even harmonic mass `E_N = Σ_{n ≤ N, 2 ∣ n} 1/n`. -/
def evenMass (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, parity n / n

theorem parity_sq (n : ℕ) : parity n ^ 2 = parity n := by
  unfold parity; split_ifs <;> norm_num

theorem parity_of_dvd {m : ℕ} (hm : 2 ∣ m) : parity m = 1 := if_pos hm

theorem parity_of_not_dvd {m : ℕ} (hm : ¬ 2 ∣ m) : parity m = 0 := if_neg hm

theorem parity_mul_of_dvd {m : ℕ} (hm : 2 ∣ m) (t : ℕ) : parity (m * t) = 1 :=
  if_pos (dvd_mul_of_dvd_left hm t)

theorem parity_mul_of_not_dvd {m : ℕ} (hm : ¬ 2 ∣ m) (t : ℕ) : parity (m * t) = parity t := by
  unfold parity
  by_cases ht : 2 ∣ t
  · rw [if_pos (dvd_mul_of_dvd_right ht m), if_pos ht]
  · rw [if_neg ht, if_neg fun h => ((Nat.Prime.dvd_mul Nat.prime_two).mp h).elim hm ht]

theorem parity_two_pow {k : ℕ} (hk : 1 ≤ k) : parity (2 ^ k) = 1 :=
  if_pos (dvd_pow_self 2 (by omega))

theorem harmonicMass_nonneg (N : ℕ) : 0 ≤ harmonicMass N := sum_nonneg fun _ _ => by positivity

theorem harmonicMass_pos {N : ℕ} (hN : 1 ≤ N) : 0 < harmonicMass N := by
  have h := single_le_sum (f := fun n : ℕ => 1 / (n : ℝ)) (fun _ _ => by positivity)
    (mem_Icc.mpr ⟨le_rfl, hN⟩ : 1 ∈ Icc 1 N)
  simp only [Nat.cast_one, div_one] at h
  exact lt_of_lt_of_le one_pos h

/-- `E_N = (1/2) H_{⌊N/2⌋}`. -/
theorem evenMass_eq (N : ℕ) : evenMass N = 1 / 2 * ∑ j ∈ Icc 1 (N / 2), 1 / (j : ℝ) := by
  have h1 : evenMass N = ∑ n ∈ (Icc 1 N).filter (fun n => 2 ∣ n), 1 / (n : ℝ) := by
    rw [evenMass, sum_filter]
    exact sum_congr rfl fun n _ => by unfold parity; split_ifs <;> simp
  rw [h1, filter_dvd_Icc_eq_image (by norm_num : 0 < 2),
    sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) h, mul_sum]
  exact sum_congr rfl fun j _ => by push_cast; ring

theorem evenMass_nonneg (N : ℕ) : 0 ≤ evenMass N := by
  rw [evenMass_eq]
  exact mul_nonneg (by norm_num) (sum_nonneg fun _ _ => by positivity)

/-- The even mass is at most half the harmonic mass. -/
theorem evenMass_le (N : ℕ) : evenMass N ≤ harmonicMass N / 2 := by
  rw [evenMass_eq, harmonicMass]
  have : ∑ j ∈ Icc 1 (N / 2), 1 / (j : ℝ) ≤ ∑ n ∈ Icc 1 N, 1 / (n : ℝ) :=
    sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl (Nat.div_le_self N 2))
      fun _ _ _ => by positivity
  linarith

theorem log_le_evenMass (N : ℕ) : Real.log (((N / 2 : ℕ) : ℝ) + 1) / 2 ≤ evenMass N := by
  rw [evenMass_eq]
  have h := log_add_one_le_harmonic (N / 2)
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  have h' : Real.log (((N / 2 : ℕ) : ℝ) + 1) ≤ ∑ j ∈ Icc 1 (N / 2), 1 / (j : ℝ) := by
    simpa [one_div] using h
  linarith

/-! ### 2. The 2-adic step -/

/-- The 2-adic step `x_n = (1_{2∣n} − E_N/H_N)/√n`. -/
def twoAdicStep (N n : ℕ) : ℝ := (parity n - evenMass N / harmonicMass N) / Real.sqrt n

theorem twoAdicStep_div_sqrt {N n : ℕ} (hn : 1 ≤ n) :
    twoAdicStep N n / Real.sqrt n = (parity n - evenMass N / harmonicMass N) * (1 / (n : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [twoAdicStep, div_div, Real.mul_self_sqrt hn0.le]
  ring

/-- The 2-adic step is orthogonal to the pole. -/
theorem sum_twoAdicStep_div_sqrt (N : ℕ) : ∑ n ∈ Icc 1 N, twoAdicStep N n / Real.sqrt n = 0 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hH := harmonicMass_pos hN
  rw [sum_congr rfl fun n hn => twoAdicStep_div_sqrt (mem_Icc.mp hn).1]
  have e : ∑ n ∈ Icc 1 N, (parity n - evenMass N / harmonicMass N) * (1 / (n : ℝ)) =
      evenMass N - evenMass N / harmonicMass N * harmonicMass N := by
    rw [evenMass, harmonicMass, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun n _ => by ring
  rw [e, div_mul_cancel₀ _ hH.ne', sub_self]

theorem twoAdicStep_sq {N n : ℕ} (hn : 1 ≤ n) :
    twoAdicStep N n ^ 2 = (parity n - evenMass N / harmonicMass N) ^ 2 * (1 / (n : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [twoAdicStep, div_pow, Real.sq_sqrt hn0.le]
  ring

/-- `|x|² = E_N − E_N²/H_N`. -/
theorem sum_twoAdicStep_sq (N : ℕ) :
    ∑ n ∈ Icc 1 N, twoAdicStep N n ^ 2 = evenMass N - evenMass N ^ 2 / harmonicMass N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [evenMass]
  have hH := harmonicMass_pos hN
  rw [sum_congr rfl fun n hn => twoAdicStep_sq (mem_Icc.mp hn).1]
  set c := evenMass N / harmonicMass N
  have e : ∀ n : ℕ, (parity n - c) ^ 2 * (1 / (n : ℝ)) =
      parity n / n - 2 * c * (parity n / n) + c ^ 2 * (1 / (n : ℝ)) := fun n => by
    rw [sub_sq, parity_sq]; ring
  rw [sum_congr rfl fun n _ => e n, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum]
  rw [show ∑ n ∈ Icc 1 N, parity n / n = evenMass N from rfl,
    show ∑ n ∈ Icc 1 N, 1 / (n : ℝ) = harmonicMass N from rfl]
  simp only [c]
  field_simp
  ring

theorem twoAdicStep_sq_le {N n : ℕ} (hn : 1 ≤ n) : twoAdicStep N n ^ 2 ≤ 1 / (n : ℝ) := by
  rw [twoAdicStep_sq hn]
  have hc0 : 0 ≤ evenMass N / harmonicMass N :=
    div_nonneg (evenMass_nonneg N) (harmonicMass_nonneg N)
  have hc1 : evenMass N / harmonicMass N ≤ 1 := by
    rcases eq_or_lt_of_le (harmonicMass_nonneg N) with h | h
    · rw [← h, div_zero]; norm_num
    · rw [div_le_one h]; linarith [evenMass_le N, evenMass_nonneg N]
  have hp : (parity n - evenMass N / harmonicMass N) ^ 2 ≤ 1 := by
    unfold parity; split_ifs <;> nlinarith
  calc (parity n - evenMass N / harmonicMass N) ^ 2 * (1 / (n : ℝ)) ≤ 1 * (1 / (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hp (by positivity)
    _ = 1 / (n : ℝ) := one_mul _

/-- `|x|² ≥ E_N/2`. -/
theorem half_evenMass_le_sum_twoAdicStep_sq (N : ℕ) :
    evenMass N / 2 ≤ ∑ n ∈ Icc 1 N, twoAdicStep N n ^ 2 := by
  rw [sum_twoAdicStep_sq]
  rcases eq_or_lt_of_le (harmonicMass_nonneg N) with h | h
  · rw [← h, div_zero, sub_zero]; linarith [evenMass_nonneg N]
  · have hE := evenMass_le N
    have hE0 := evenMass_nonneg N
    have : evenMass N ^ 2 / harmonicMass N ≤ evenMass N / 2 := by
      rw [div_le_iff₀ h]; nlinarith
    linarith

/-! ### 3. The defect of the 2-adic step -/

/-- **The defect of the 2-adic step is `log 2` times the even mass.** -/
theorem poleDefect_twoAdicStep (N : ℕ) : poleDefect N (twoAdicStep N) = Real.log 2 * evenMass N := by
  rw [← walkEnergy_small_add_large 3 N (twoAdicStep N)]
  set c := evenMass N / harmonicMass N
  set y := poleGauge (twoAdicStep N)
  have hy : ∀ n, 1 ≤ n → y n = parity n - c := fun n hn => by
    have hs : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hn)).ne'
    simp only [y, poleGauge, twoAdicStep, c]
    field_simp
  -- the large primes are odd and keep the parity
  have hL : walkEnergy N (fun t => 3 ≤ t.minFac) y = 0 := by
    refine sum_eq_zero fun m hm => sum_eq_zero fun t ht => ?_
    have hm1 := (mem_Icc.mp hm).1
    have ht1 := (mem_Icc.mp ht).1
    split_ifs with h3
    · have hodd : ¬ 2 ∣ t := fun h2 => by
        have := Nat.minFac_le_of_dvd le_rfl h2; omega
      rw [hy (m * t) (Nat.mul_pos hm1 ht1), hy m hm1, mul_comm m t, parity_mul_of_not_dvd hodd m]
      simp
    · rfl
  -- the small primes: only `2`, and only from odd `m`
  have hP : (range 3).filter Nat.Prime = {2} := by
    ext p
    simp only [mem_filter, mem_range, mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      interval_cases p
      · exact absurd h2 Nat.not_prime_zero
      · exact absurd h2 Nat.not_prime_one
      · rfl
    · rintro rfl; exact ⟨by norm_num, Nat.prime_two⟩
  have hedge : ∀ m ∈ Icc 1 N, smallEdge 3 N y m = if 2 ∣ m then 0 else Real.log 2 *
      ∑ k ∈ range (N + 1), if 1 ≤ k ∧ m * 2 ^ k ≤ N then 1 / ((m * 2 ^ k : ℕ) : ℝ) else 0 := by
    intro m hm
    have hm1 := (mem_Icc.mp hm).1
    rw [smallEdge, hP, sum_singleton]
    split_ifs with h2
    · refine sum_eq_zero fun k _ => ?_
      split_ifs with hk
      · rw [hy _ (Nat.mul_pos hm1 (pow_pos two_pos k)), hy m hm1, parity_mul_of_dvd h2,
          parity_of_dvd h2]
        simp
      · rfl
    · rw [mul_sum]
      refine sum_congr rfl fun k _ => ?_
      split_ifs with hk
      · rw [hy _ (Nat.mul_pos hm1 (pow_pos two_pos k)), hy m hm1, parity_mul_of_not_dvd h2,
          parity_two_pow hk.1, parity_of_not_dvd h2]
        push_cast
        ring
      · rw [mul_zero]
  have hS : walkEnergy N (fun t => t.minFac < 3) y = Real.log 2 * evenMass N := by
    rw [← sum_smallEdge_eq, sum_congr rfl hedge]
    have hsplit := sum_filter_add_sum_filter_not (Icc 1 N) (fun m => 2 ∣ m)
      (fun m => if 2 ∣ m then (0 : ℝ) else Real.log 2 * ∑ k ∈ range (N + 1),
        if 1 ≤ k ∧ m * 2 ^ k ≤ N then 1 / ((m * 2 ^ k : ℕ) : ℝ) else 0)
    have h0 : ∑ m ∈ (Icc 1 N).filter (fun m => 2 ∣ m), (if 2 ∣ m then (0 : ℝ) else
        Real.log 2 * ∑ k ∈ range (N + 1),
          if 1 ≤ k ∧ m * 2 ^ k ≤ N then 1 / ((m * 2 ^ k : ℕ) : ℝ) else 0) = 0 :=
      sum_eq_zero fun m hm => if_pos (mem_filter.mp hm).2
    rw [← hsplit, h0, zero_add, evenMass, sum_Icc_eq_sum_ladders Nat.prime_two N, mul_sum]
    refine sum_congr rfl fun u hu => ?_
    have hu2 := (mem_filter.mp hu).2
    rw [if_neg hu2]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    by_cases hj : 1 ≤ j
    · have hp : parity (u * 2 ^ j) = 1 := by rw [parity_mul_of_not_dvd hu2, parity_two_pow hj]
      by_cases hjN : u * 2 ^ j ≤ N
      · rw [if_pos ⟨hj, hjN⟩, if_pos hjN, hp]
      · rw [if_neg fun h => hjN h.2, if_neg hjN]
    · have hj0 : j = 0 := by omega
      subst hj0
      rw [if_neg fun h => hj h.1]
      split_ifs
      · rw [pow_zero, mul_one, parity_of_not_dvd hu2, zero_div]
      · rfl
  rw [hS, hL, add_zero]

/-- **The Poincaré constant of the multiplicative walk is at most `2 log 2`**: for every `N`,
`D_N(x) ≤ 2 log 2 |x|²` at the 2-adic step. -/
theorem poleDefect_twoAdicStep_le (N : ℕ) :
    poleDefect N (twoAdicStep N) ≤ 2 * Real.log 2 * ∑ n ∈ Icc 1 N, twoAdicStep N n ^ 2 := by
  rw [poleDefect_twoAdicStep]
  have h := half_evenMass_le_sum_twoAdicStep_sq N
  have hl := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
  nlinarith

/-! ### 4. The rows from below -/

/-- **Mertens on the rows, from below**: for `ε > 0` there is `R` such that every row with
`⌊N/n⌋ ≥ R` has `A(⌊N/n⌋) + log n ≥ log N − γ − ε`. -/
theorem exists_row_ge {ε : ℝ} (hε : 0 < ε) : ∃ R : ℕ, 1 ≤ R ∧ ∀ N n : ℕ, 1 ≤ n → R ≤ N / n →
    Real.log N - γ - ε ≤ mertensSum (N / n) + Real.log n := by
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp
    (tendsto_mertensSum_sub_log.eventually (lt_mem_nhds (by linarith : -γ - ε / 2 < -γ)))
  refine ⟨max (max R₀ 1) (⌈2 / ε⌉₊ + 1), le_trans (le_max_right _ _) (le_max_left _ _),
    fun N n hn hR => ?_⟩
  set k := N / n
  have hk0 : R₀ ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR
  have hk1 : 1 ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hR
  have hkε : 2 / ε < k := by
    have := Nat.le_ceil (2 / ε)
    have h' : ((⌈2 / ε⌉₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast le_trans (le_max_right _ _) hR
    push_cast at h'
    linarith
  have hM := hR₀ k hk0
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hN : (N : ℝ) ≤ n * (k + 1) := by
    have := Nat.lt_mul_div_succ N hn
    exact_mod_cast this.le
  have h1 : Real.log N ≤ Real.log n + Real.log (k + 1) := by
    rcases Nat.eq_zero_or_pos N with h0 | hNpos
    · rw [h0, Nat.cast_zero, Real.log_zero]
      have := Real.log_nonneg (show (1 : ℝ) ≤ n by exact_mod_cast hn)
      have := Real.log_nonneg (show (1 : ℝ) ≤ k + 1 by linarith)
      linarith
    · rw [← Real.log_mul hn0.ne' (by positivity)]
      exact Real.log_le_log (by exact_mod_cast hNpos) hN
  have h2 : Real.log (k + 1) ≤ Real.log k + 1 / k := by
    have := Real.log_le_sub_one_of_pos (show 0 < ((k : ℝ) + 1) / k by positivity)
    rw [Real.log_div (by positivity) hkpos.ne'] at this
    have e : ((k : ℝ) + 1) / k - 1 = 1 / k := by field_simp; ring
    linarith
  have h3 : 1 / (k : ℝ) ≤ ε / 2 := by
    rw [div_le_iff₀ hkpos]
    have := (div_lt_iff₀ hε).mp hkε
    linarith
  linarith

/-- The rows, from below: `(log N − γ − ε)|x|² ≤ Σ (A(⌊N/n⌋) + log n) x_n² + log R · Σ_{n > N/R} x_n²`. -/
theorem sum_row_mul_sq_ge {ε : ℝ} {R N : ℕ} (hR1 : 1 ≤ R) (hεγ : 0 ≤ γ + ε)
    (hrow : ∀ n : ℕ, 1 ≤ n → R ≤ N / n → Real.log N - γ - ε ≤ mertensSum (N / n) + Real.log n)
    (x : ℕ → ℝ) :
    (Real.log N - γ - ε) * ∑ n ∈ Icc 1 N, x n ^ 2 ≤
      ∑ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) * x n ^ 2 +
        Real.log R * ∑ n ∈ (Icc 1 N).filter (fun n => N / R < n), x n ^ 2 := by
  rw [sum_filter, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun n hn => ?_
  have hn1 := (mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlR := Real.log_natCast_nonneg R
  have hx := sq_nonneg (x n)
  have hA : 0 ≤ mertensSum (N / n) :=
    sum_nonneg fun t _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)
  by_cases hb : R ≤ N / n
  · have h := mul_le_mul_of_nonneg_right (hrow n hn1 hb) hx
    have : 0 ≤ Real.log R * (if N / R < n then x n ^ 2 else 0) := by
      split_ifs
      · exact mul_nonneg hlR hx
      · rw [mul_zero]
    linarith
  · have hlt : N / n < R := not_le.mp hb
    have hNR : N < R * n := (Nat.div_lt_iff_lt_mul hn1).mp hlt
    have hnR : N / R < n := (Nat.div_lt_iff_lt_mul hR1).mpr (by rw [mul_comm]; exact hNR)
    rw [if_pos hnR]
    have hlog : Real.log N ≤ Real.log R + Real.log n := by
      rcases Nat.eq_zero_or_pos N with h0 | hNpos
      · rw [h0, Nat.cast_zero, Real.log_zero]
        have := Real.log_nonneg (show (1 : ℝ) ≤ n by exact_mod_cast hn1)
        linarith
      · rw [← Real.log_mul (by positivity) hn0.ne']
        exact Real.log_le_log (by exact_mod_cast hNpos) (by exact_mod_cast hNR.le)
    have h : Real.log N - γ - ε ≤ mertensSum (N / n) + Real.log n + Real.log R := by linarith
    nlinarith [mul_le_mul_of_nonneg_right h hx]

/-! ### 5. Sharpness and the two-sided law -/

/-- **The 2-adic step reaches `log N − γ − 2 log 2`.** For every `ε > 0`, eventually in `N`, some
`x ≠ 0` orthogonal to the pole has `P_N(x) ≥ (log N − γ − 2 log 2 − ε)|x|²`. -/
theorem eventually_exists_atomicWeilForm_ge {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ x : ℕ → ℝ, ∑ n ∈ Icc 1 N, x n / Real.sqrt n = 0 ∧
      0 < ∑ n ∈ Icc 1 N, x n ^ 2 ∧
      (Real.log N - γ - 2 * Real.log 2 - ε) * ∑ n ∈ Icc 1 N, x n ^ 2 ≤ atomicWeilForm N x := by
  obtain ⟨R, hR1, hrow⟩ := exists_row_ge (show 0 < ε / 2 by linarith)
  have hlR := Real.log_natCast_nonneg R
  set B := Real.log R * (1 + Real.log R)
  have hB : 0 ≤ B := by positivity
  set T := ⌈Real.exp (4 * (2 * B / ε + 1))⌉₊
  refine ⟨2 * T + 2, fun N hN => ⟨twoAdicStep N, sum_twoAdicStep_div_sqrt N, ?_⟩⟩
  set S := ∑ n ∈ Icc 1 N, twoAdicStep N n ^ 2
  -- the step is long: `|x|² ≥ E_N/2 ≥ log(N/2 + 1)/4 ≥ 2B/ε + 1`
  have hS : 2 * B / ε + 1 ≤ S := by
    have h1 := half_evenMass_le_sum_twoAdicStep_sq N
    have h2 := log_le_evenMass N
    have h3 : Real.exp (4 * (2 * B / ε + 1)) ≤ ((N / 2 : ℕ) : ℝ) + 1 := by
      have := Nat.le_ceil (Real.exp (4 * (2 * B / ε + 1)))
      have h4 : ((T + 1 : ℕ) : ℝ) ≤ ((N / 2 : ℕ) : ℝ) := by
        exact_mod_cast (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
      push_cast at h4
      linarith
    have h5 : 4 * (2 * B / ε + 1) ≤ Real.log (((N / 2 : ℕ) : ℝ) + 1) := by
      calc _ = Real.log (Real.exp (4 * (2 * B / ε + 1))) := (Real.log_exp _).symm
        _ ≤ _ := Real.log_le_log (Real.exp_pos _) h3
    linarith
  have hS0 : 0 < S := lt_of_lt_of_le (by positivity) hS
  refine ⟨hS0, ?_⟩
  have hBS : B ≤ ε / 2 * S := by
    have := (div_le_iff₀ hε).mp (show 2 * B / ε ≤ S by linarith)
    linarith
  -- the top rows carry little mass
  have htop : ∑ n ∈ (Icc 1 N).filter (fun n => N / R < n), twoAdicStep N n ^ 2 ≤
      1 + Real.log R := by
    calc _ ≤ ∑ n ∈ (Icc 1 N).filter (fun n => N / R < n), 1 / (n : ℝ) :=
          sum_le_sum fun n hn => twoAdicStep_sq_le (mem_Icc.mp (mem_filter.mp hn).1).1
      _ = roughHarmonic 0 N - roughHarmonic 0 (N / R) := by
          rw [roughHarmonic_sub_eq (Nat.div_le_self N R), roughInterval_zero]
      _ ≤ 1 + Real.log R := roughHarmonic_sub_div_le 0 N hR1
  have hrows := sum_row_mul_sq_ge hR1 (by
    have := (by norm_num : (0 : ℝ) < 1 / 2).trans Real.one_half_lt_eulerMascheroniConstant
    linarith) (fun n hn hb => hrow N n hn hb) (twoAdicStep N)
  have hid := atomicWeilForm_add_poleDefect N (twoAdicStep N)
  have hD := poleDefect_twoAdicStep_le N
  have htop' := mul_le_mul_of_nonneg_left htop hlR
  linarith

/-- **The prime form below its pole: the top is `log N − γ − 2 log 2`.** For every `ε > 0`,
eventually in `N`: every `x` orthogonal to `n^{−1/2}` has `P_N(x) ≤ (log N − γ − 2 log 2 + ε)|x|²`,
and some `x ≠ 0` orthogonal to it has `P_N(x) ≥ (log N − γ − 2 log 2 − ε)|x|²`. -/
theorem eventually_atomicWeilForm_below_pole_two_log_two {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
      (∀ x : ℕ → ℝ, ∑ n ∈ Icc 1 N, x n / Real.sqrt n = 0 →
        atomicWeilForm N x ≤ (Real.log N - γ - 2 * Real.log 2 + ε) * ∑ n ∈ Icc 1 N, x n ^ 2) ∧
      ∃ x : ℕ → ℝ, ∑ n ∈ Icc 1 N, x n / Real.sqrt n = 0 ∧ 0 < ∑ n ∈ Icc 1 N, x n ^ 2 ∧
        (Real.log N - γ - 2 * Real.log 2 - ε) * ∑ n ∈ Icc 1 N, x n ^ 2 ≤ atomicWeilForm N x := by
  obtain ⟨N₁, h₁⟩ := eventually_atomicWeilForm_le_two_log_two hε
  obtain ⟨N₂, h₂⟩ := eventually_exists_atomicWeilForm_ge hε
  exact ⟨max N₁ N₂, fun N hN => ⟨h₁ N (le_of_max_le_left hN), h₂ N (le_of_max_le_right hN)⟩⟩

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
