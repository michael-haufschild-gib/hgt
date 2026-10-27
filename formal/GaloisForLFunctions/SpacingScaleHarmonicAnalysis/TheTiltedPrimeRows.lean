import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCovariantCountertermIsTheAnomaly

/-!
# The tilted rows of Weil's prime form

The Schur rows of the atomic Weil prime form `P_N` with weights `n^{−1/2}` are exactly
`A(⌊N/m⌋) + log m`: Mertens' sum up the tower, `Σ_{k ∣ m} Λ(k) = log m` down it (RAPT `row_eq`).
Their maximum `log N + O(1)` is the covariant counterterm, and it is attained at **every** row: the
top rows `m ≈ N` carry all of `log N` in their down tower.

A Schur weight tilted across scales moves part of that charge. With `r(n) = 1 + n/N` the
Schur-weighted row at `m` becomes
`Σ_{k ≤ N/m} (Λ(k)/k) r(mk)/r(m) + Σ_{k ∣ m} Λ(k) r(m/k)/r(m)`.

* **Tilted Schur test** (`atomicWeilForm_le_of_tiltedRow`): for positive weights `r`,
  `P_N(x) ≤ Σ_m x_m² Σ_n P(m, n) √(m/n) r(n)/r(m)`.
* **Up the tower the tilt costs a constant** (`sum_up_tilt_le`): `r(mk)/r(m) ≤ 1 + mk/N`, and
  `(m/N) Σ_{k ≤ N/m} Λ(k) ≤ log 4 + 4` by Chebyshev's bound (`sum_vonMangoldt_Icc_le`).
* **Down the tower the tilt saves a fraction of `log m`** (`sum_down_tilt_le`): every proper divisor
  lies at most half way down, `r(m/k) ≤ 1 + m/(2N)`, so the down row is at most
  `((1 + m/2N)/(1 + m/N)) log m`.
* **The tilted rows** (`tiltedRow_le`, `atomicWeilForm_le_tilted`):
  `P_N(x) ≤ Σ_m x_m² (log N + 2(log 4 + 4) − (m/4N) log m)`.

The saving `(m/4N) log m` is proportional to the relative position `m/N` of the atom times `log N`:
exactly the shape of the archimedean cross-kernel row at the spacing scale
(`TheArchimedeanCrossKernel`). Power weights `n^α` cannot produce it — at an `m` with many small
prime factors every divisor `m/k` is close to `m` on a logarithmic scale — but a weight that
separates `m` from `m/2` does.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis

open ArithmeticFunction GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticElectrostatics GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

/-! ### The tilted Schur test -/

/-- **Tilted Schur test**: for weights `r > 0` on `[1, N]`,
`P_N(x) ≤ Σ_m x_m² Σ_n P(m, n) √(m/n) r(n)/r(m)`. -/
theorem atomicWeilForm_le_of_tiltedRow {N : ℕ} (r : ℕ → ℝ) (hr : ∀ n ∈ Icc 1 N, 0 < r n)
    (x : ℕ → ℝ) :
    atomicWeilForm N x ≤ ∑ m ∈ Icc 1 N, x m ^ 2 *
      ∑ n ∈ Icc 1 N, weilPrimeKernel m n * Real.sqrt ((m : ℝ) / n) * (r n / r m) := by
  set S := Icc 1 N
  have hpos : ∀ n ∈ S, 0 < n := fun n hn => (mem_Icc.mp hn).1
  -- `2 x_m x_n ≤ x_m² a + x_n² a⁻¹` with `a = √(m/n) r(n)/r(m)`
  have hpair : ∀ m ∈ S, ∀ n ∈ S, x m * x n * weilPrimeKernel m n ≤
      (x m ^ 2 * (weilPrimeKernel m n * Real.sqrt ((m : ℝ) / n) * (r n / r m)) +
        x n ^ 2 * (weilPrimeKernel n m * Real.sqrt ((n : ℝ) / m) * (r m / r n))) / 2 := by
    intro m hm n hn
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hpos m hm
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hpos n hn
    have hrm := hr m hm
    have hrn := hr n hn
    set a := Real.sqrt ((m : ℝ) / n) * (r n / r m) with ha_def
    have ha : 0 < a := mul_pos (Real.sqrt_pos.mpr (by positivity)) (by positivity)
    have hinv : Real.sqrt ((n : ℝ) / m) * (r m / r n) = a⁻¹ := by
      rw [ha_def, mul_inv, ← Real.sqrt_inv, inv_div, inv_div]
    have hP := weilPrimeKernel_nonneg m n
    have e1 : weilPrimeKernel m n * Real.sqrt ((m : ℝ) / n) * (r n / r m) =
        weilPrimeKernel m n * a := by rw [mul_assoc]
    have e2 : weilPrimeKernel n m * Real.sqrt ((n : ℝ) / m) * (r m / r n) =
        weilPrimeKernel m n * a⁻¹ := by rw [weilPrimeKernel_comm n m, mul_assoc, hinv]
    rw [e1, e2]
    have key : x m ^ 2 * a + x n ^ 2 * a⁻¹ - 2 * (x m * x n) = (x m * a - x n) ^ 2 / a := by
      field_simp
      ring
    have h2 : 2 * (x m * x n) ≤ x m ^ 2 * a + x n ^ 2 * a⁻¹ := by
      have : 0 ≤ (x m * a - x n) ^ 2 / a := by positivity
      linarith
    nlinarith
  have hsym : ∑ m ∈ S, ∑ n ∈ S,
      x n ^ 2 * (weilPrimeKernel n m * Real.sqrt ((n : ℝ) / m) * (r m / r n)) =
      ∑ m ∈ S, ∑ n ∈ S,
        x m ^ 2 * (weilPrimeKernel m n * Real.sqrt ((m : ℝ) / n) * (r n / r m)) := sum_comm
  calc atomicWeilForm N x
      ≤ ∑ m ∈ S, ∑ n ∈ S,
          (x m ^ 2 * (weilPrimeKernel m n * Real.sqrt ((m : ℝ) / n) * (r n / r m)) +
            x n ^ 2 * (weilPrimeKernel n m * Real.sqrt ((n : ℝ) / m) * (r m / r n))) / 2 :=
        sum_le_sum fun m hm => sum_le_sum fun n hn => hpair m hm n hn
    _ = ∑ m ∈ S, x m ^ 2 *
          ∑ n ∈ S, weilPrimeKernel m n * Real.sqrt ((m : ℝ) / n) * (r n / r m) := by
        simp only [← sum_div, sum_add_distrib, hsym, mul_sum]
        ring

/-! ### Chebyshev's bound -/

/-- **Chebyshev's bound**: `Σ_{k ≤ K} Λ(k) ≤ (log 4 + 4) K`. -/
theorem sum_vonMangoldt_Icc_le (K : ℕ) :
    ∑ k ∈ Icc 1 K, Λ k ≤ (Real.log 4 + 4) * K := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hpsi : Chebyshev.psi K = ∑ k ∈ Icc 1 K, Λ k := by
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast, ← Finset.add_sum_Ioc_eq_sum_Icc
      (Nat.zero_le K)]
    have hIoc : Finset.Ioc 0 K = Finset.Icc 1 K := by ext; simp; omega
    simp [hIoc]
  rw [← hpsi]
  have hle := Chebyshev.psi_le hK1
  -- `log K ≤ 2√K`, so `2√K log K ≤ 4K`
  have hs0 : 0 ≤ Real.sqrt K := Real.sqrt_nonneg _
  have hlog : Real.log K ≤ 2 * Real.sqrt K := by
    have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by linarith : (0 : ℝ) < K))
    rw [Real.log_sqrt (by linarith)] at h
    linarith
  have hsq : Real.sqrt K * Real.sqrt K = K := Real.mul_self_sqrt (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hlog hs0]

/-! ### Reindexing the up tower -/

/-- Up the tower: `Σ_{n ≤ N} [m ∣ n, m ≠ n] F(n/m) = Σ_{k ≤ N/m} F(k)` when `F(1) = 0`. -/
theorem sum_up_reindex {m N : ℕ} (hm : 0 < m) (F : ℕ → ℝ) (hF : F 1 = 0) :
    ∑ n ∈ Icc 1 N, (if m ∣ n ∧ m ≠ n then F (n / m) else 0) = ∑ k ∈ Icc 1 (N / m), F k := by
  have hterm : ∀ n ∈ Icc 1 N, (if m ∣ n ∧ m ≠ n then F (n / m) else 0) =
      if m ∣ n then F (n / m) else 0 := by
    intro n _
    by_cases h : m ∣ n
    · by_cases h' : m = n
      · subst h'
        simp [Nat.div_self hm, hF]
      · rw [if_pos ⟨h, h'⟩, if_pos h]
    · rw [if_neg (fun h'' => h h''.1), if_neg h]
  rw [sum_congr rfl hterm, ← sum_filter, filter_dvd_Icc_eq_image hm,
    sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hm h]
  exact sum_congr rfl fun k _ => by rw [Nat.mul_div_cancel_left k hm]

/-! ### The tilted rows -/

/-- The tilt `r(n) = 1 + n/N`. -/
def tilt (N n : ℕ) : ℝ := 1 + (n : ℝ) / N

theorem one_le_tilt (N n : ℕ) : 1 ≤ tilt N n := by
  unfold tilt
  have : (0 : ℝ) ≤ (n : ℝ) / N := by positivity
  linarith

theorem tilt_pos (N n : ℕ) : 0 < tilt N n := lt_of_lt_of_le one_pos (one_le_tilt N n)

/-- **Up the tower the tilt costs a constant**:
`Σ_n [m ∣ n, m ≠ n] (Λ(n/m)/(n/m)) r(n)/r(m) ≤ A(⌊N/m⌋) + log 4 + 4`. -/
theorem sum_up_tilt_le {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    ∑ n ∈ Icc 1 N, (if m ∣ n ∧ m ≠ n then Λ (n / m) / ((n / m : ℕ) : ℝ) else 0) *
        (tilt N n / tilt N m) ≤
      mertensSum (N / m) + (Real.log 4 + 4) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hm.trans_le hmN
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  -- each term is at most `Λ(k)/k + (m/N) Λ(k)` with `k = n/m`
  have hterm : ∀ n ∈ Icc 1 N,
      (if m ∣ n ∧ m ≠ n then Λ (n / m) / ((n / m : ℕ) : ℝ) else 0) * (tilt N n / tilt N m) ≤
        (if m ∣ n ∧ m ≠ n then Λ (n / m) / ((n / m : ℕ) : ℝ) else 0) +
          (m : ℝ) / N * (if m ∣ n ∧ m ≠ n then Λ (n / m) else 0) := by
    intro n hn
    split_ifs with h
    · obtain ⟨k, rfl⟩ := h.1
      have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
      rw [Nat.mul_div_cancel_left k hm]
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
      have hΛ : 0 ≤ Λ k := vonMangoldt_nonneg
      have hratio : tilt N (m * k) / tilt N m ≤ 1 + (m : ℝ) * k / N := by
        rw [div_le_iff₀ (tilt_pos N m)]
        have h1 := one_le_tilt N m
        have : tilt N (m * k) = 1 + (m : ℝ) * k / N := by simp [tilt]
        rw [this]
        nlinarith [show (0 : ℝ) ≤ (m : ℝ) * k / N by positivity]
      calc Λ k / (k : ℝ) * (tilt N (m * k) / tilt N m)
          ≤ Λ k / (k : ℝ) * (1 + (m : ℝ) * k / N) :=
            mul_le_mul_of_nonneg_left hratio (by positivity)
        _ = Λ k / k + (m : ℝ) / N * Λ k := by field_simp
    · simp
  have hsum := sum_le_sum hterm
  rw [sum_add_distrib, ← mul_sum, sum_up_reindex hm (fun k => Λ k) (by simp),
    sum_up_reindex hm (fun k => Λ k / (k : ℝ)) (by simp)] at hsum
  refine hsum.trans ?_
  unfold mertensSum
  -- `(m/N) ψ(N/m) ≤ log 4 + 4`
  have hcheb := sum_vonMangoldt_Icc_le (N / m)
  have hfl : ((N / m : ℕ) : ℝ) * m ≤ N := by exact_mod_cast Nat.div_mul_le_self N m
  have hc : (0 : ℝ) ≤ Real.log 4 + 4 := by positivity
  have : (m : ℝ) / N * ∑ k ∈ Icc 1 (N / m), Λ k ≤ Real.log 4 + 4 := by
    calc (m : ℝ) / N * ∑ k ∈ Icc 1 (N / m), Λ k
        ≤ (m : ℝ) / N * ((Real.log 4 + 4) * (N / m : ℕ)) :=
          mul_le_mul_of_nonneg_left hcheb (by positivity)
      _ = (Real.log 4 + 4) * (((N / m : ℕ) : ℝ) * m / N) := by ring
      _ ≤ (Real.log 4 + 4) * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ hc
          rw [div_le_one hN0]; exact hfl
      _ = Real.log 4 + 4 := mul_one _
  linarith

/-- **Down the tower the tilt saves a fraction of `log m`**:
`Σ_n [n ∣ m, n ≠ m] Λ(m/n) r(n)/r(m) ≤ ((1 + m/2N)/(1 + m/N)) log m`. -/
theorem sum_down_tilt_le {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    ∑ n ∈ Icc 1 N, (if n ∣ m ∧ n ≠ m then Λ (m / n) else 0) * (tilt N n / tilt N m) ≤
      (1 + (m : ℝ) / (2 * N)) / tilt N m * Real.log m := by
  have hterm : ∀ n ∈ Icc 1 N, (if n ∣ m ∧ n ≠ m then Λ (m / n) else 0) * (tilt N n / tilt N m) ≤
      (1 + (m : ℝ) / (2 * N)) / tilt N m * (if n ∣ m ∧ n ≠ m then Λ (m / n) else 0) := by
    intro n hn
    split_ifs with h
    · -- a proper divisor lies at most half way down: `2n ≤ m`
      obtain ⟨k, hk⟩ := h.1
      have hk2 : 2 ≤ k := by
        rcases Nat.lt_or_ge k 2 with hk' | hk'
        · interval_cases k
          · simp at hk; omega
          · exact absurd (by rw [hk, mul_one]) h.2
        · exact hk'
      have h2n : (2 : ℝ) * n ≤ m := by
        have : 2 * n ≤ m := by rw [hk]; nlinarith
        exact_mod_cast this
      have hΛ : 0 ≤ Λ (m / n) := vonMangoldt_nonneg
      have htilt : tilt N n ≤ 1 + (m : ℝ) / (2 * N) := by
        unfold tilt
        rcases Nat.eq_zero_or_pos N with hN | hN
        · subst hN; simp
        have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
        have : (n : ℝ) / N ≤ (m : ℝ) / (2 * N) := by
          rw [div_le_div_iff₀ hN0 (by positivity)]; nlinarith
        linarith
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right htilt (tilt_pos N m).le) hΛ
    · simp
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum, sum_down_eq hm hmN]

/-- **The tilted rows**: `Σ_n P(m, n) √(m/n) r(n)/r(m) ≤ log N + 2(log 4 + 4) − (m/4N) log m`. -/
theorem tiltedRow_le {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    ∑ n ∈ Icc 1 N, weilPrimeKernel m n * Real.sqrt ((m : ℝ) / n) * (tilt N n / tilt N m) ≤
      Real.log N + 2 * (Real.log 4 + 4) - (m : ℝ) / (4 * N) * Real.log m := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hm.trans_le hmN
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hsplit : ∀ n ∈ Icc 1 N, weilPrimeKernel m n * Real.sqrt ((m : ℝ) / n) * (tilt N n / tilt N m)
      = (if m ∣ n ∧ m ≠ n then Λ (n / m) / ((n / m : ℕ) : ℝ) else 0) * (tilt N n / tilt N m) +
        (if n ∣ m ∧ n ≠ m then Λ (m / n) else 0) * (tilt N n / tilt N m) := by
    intro n hn
    rw [weilPrimeKernel_mul_sqrt_ratio hm (mem_Icc.mp hn).1, add_mul]
  rw [sum_congr rfl hsplit, sum_add_distrib]
  have hup := sum_up_tilt_le hm hmN
  have hdown := sum_down_tilt_le hm hmN
  have hq : 1 ≤ N / m := (Nat.le_div_iff_mul_le hm).mpr (by linarith)
  have hmert := (abs_le.mp (RHTower.Mertens.mertens_first (N / m) hq)).2
  have hlogs := log_div_add_log_le hm hmN
  have hlogm : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  -- the down saving: `1 − (1 + t/2)/(1 + t) = (t/2)/(1 + t) ≥ t/4`
  have hsave : (1 + (m : ℝ) / (2 * N)) / tilt N m ≤ 1 - (m : ℝ) / (4 * N) := by
    unfold tilt
    have ht : (m : ℝ) / N ≤ 1 := by rw [div_le_one hN0]; exact_mod_cast hmN
    have ht0 : 0 ≤ (m : ℝ) / N := by positivity
    rw [div_le_iff₀ (by positivity)]
    have e1 : (m : ℝ) / (2 * N) = (m / N) / 2 := by ring
    have e2 : (m : ℝ) / (4 * N) = (m / N) / 4 := by ring
    rw [e1, e2]
    nlinarith
  have hdown' : (1 + (m : ℝ) / (2 * N)) / tilt N m * Real.log m ≤
      (1 - (m : ℝ) / (4 * N)) * Real.log m := mul_le_mul_of_nonneg_right hsave hlogm
  unfold mertensSum at hup
  linarith

/-- **The tilted bound on the atomic prime form**:
`P_N(x) ≤ Σ_m x_m² (log N + 2(log 4 + 4) − (m/4N) log m)`. -/
theorem atomicWeilForm_le_tilted (N : ℕ) (x : ℕ → ℝ) :
    atomicWeilForm N x ≤ ∑ m ∈ Icc 1 N, x m ^ 2 *
      (Real.log N + 2 * (Real.log 4 + 4) - (m : ℝ) / (4 * N) * Real.log m) :=
  (atomicWeilForm_le_of_tiltedRow (tilt N) (fun n _ => tilt_pos N n) x).trans
    (sum_le_sum fun _ hm => mul_le_mul_of_nonneg_left
      (tiltedRow_le (mem_Icc.mp hm).1 (mem_Icc.mp hm).2) (sq_nonneg _))

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis
