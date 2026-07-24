import GaloisForLFunctions.RHTower.PsiRemainderRecursion

/-!
# Summatories of `Λ·log` and `Λ*Λ`

Two evaluations feeding Selberg's second inequality:

* `sum_vonMangoldt_conv_eq`: `∑_{k ≤ N} (Λ*Λ)(k) = ∑_{d ≤ N} Λ(d)·ψ(⌊N/d⌋)`
  — the hyperbola swap.
* the discrete Abel bounds
  `ψ(N)log N − 7N ≤ ∑_{k ≤ N} Λ(k)·log k ≤ ψ(N)·log N`: writing
  `log N − log k` as a telescope over `j ∈ [k, N)` and regrouping by `j`
  turns the deficit into `∑_j (log(j+1) − log j)·ψ(j) ≤ ∑_j (1/j)·7j`.

Also extracts the recurring helpers `chebyshevPsi_le_seven` and
`log_succ_sub_log_le`.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

/-- `∑_{k ≤ N} (Λ*Λ)(k) = ∑_{d ≤ N} Λ(d)·ψ(⌊N/d⌋)`. -/
theorem sum_vonMangoldt_conv_eq (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, (vonMangoldt * vonMangoldt) k
      = ∑ d ∈ Finset.Icc 1 N, vonMangoldt d * chebyshevPsi (N / d) :=
  sum_Icc_mul_apply vonMangoldt vonMangoldt N

/-- Chebyshev's bound in the crude form `ψ(j) ≤ 7j`. -/
theorem chebyshevPsi_le_seven (j : ℕ) : chebyshevPsi j ≤ 7 * (j : ℝ) := by
  have hch := Mertens.sum_vonMangoldt_Icc_le j
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (x := (4 : ℝ)) (by norm_num)
    linarith
  have hbound : (Real.log 4 + 4) * (j : ℝ) ≤ 7 * (j : ℝ) := by
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg j)
    linarith
  calc chebyshevPsi j = ∑ d ∈ Finset.Icc 1 j, vonMangoldt d := rfl
    _ ≤ (Real.log 4 + 4) * (j : ℝ) := hch
    _ ≤ 7 * (j : ℝ) := hbound

/-- The logarithmic increment bound `log(j+1) − log j ≤ 1/j`. -/
theorem log_succ_sub_log_le {j : ℕ} (hj : 1 ≤ j) :
    Real.log ((j : ℝ) + 1) - Real.log j ≤ 1 / j := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
  have hdiv := Real.log_le_sub_one_of_pos
    (x := ((j : ℝ) + 1) / j) (by positivity)
  rw [Real.log_div (by positivity) hj0.ne'] at hdiv
  have heq : ((j : ℝ) + 1) / j - 1 = 1 / j := by
    field_simp
    ring
  linarith

/-- **Upper Abel bound**: `∑_{k ≤ N} Λ(k)·log k ≤ ψ(N)·log N`. -/
theorem sum_vonMangoldt_mul_log_le (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, vonMangoldt k * Real.log k
      ≤ chebyshevPsi N * Real.log N := by
  have hterm : ∀ k ∈ Finset.Icc 1 N,
      vonMangoldt k * Real.log k ≤ vonMangoldt k * Real.log N := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    apply mul_le_mul_of_nonneg_left _ vonMangoldt_nonneg
    exact Real.log_le_log (by exact_mod_cast (by omega : 0 < k))
      (by exact_mod_cast hk.2)
  calc ∑ k ∈ Finset.Icc 1 N, vonMangoldt k * Real.log k
      ≤ ∑ k ∈ Finset.Icc 1 N, vonMangoldt k * Real.log N :=
        Finset.sum_le_sum hterm
    _ = chebyshevPsi N * Real.log N := by
        rw [← Finset.sum_mul,
          show (∑ k ∈ Finset.Icc 1 N, vonMangoldt k) = chebyshevPsi N
            from rfl]

/-- **Lower Abel bound**: `ψ(N)·log N − 7N ≤ ∑_{k ≤ N} Λ(k)·log k`. -/
theorem le_sum_vonMangoldt_mul_log (N : ℕ) (hN : 1 ≤ N) :
    chebyshevPsi N * Real.log N - 7 * N
      ≤ ∑ k ∈ Finset.Icc 1 N, vonMangoldt k * Real.log k := by
  -- the deficit `D = ∑ Λ(k)(log N − log k)`, telescoped and regrouped
  have htel : ∀ k ∈ Finset.Icc 1 N,
      vonMangoldt k * Real.log N - vonMangoldt k * Real.log k
        = ∑ j ∈ Finset.Ico k N, vonMangoldt k
            * (Real.log ((j : ℝ) + 1) - Real.log j) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have h3 := Finset.sum_Ico_eq_sub
      (fun j => Real.log ((j : ℝ) + 1) - Real.log (j : ℝ)) hk.2
    have h1 := Finset.sum_range_sub (fun j => Real.log (j : ℝ)) N
    have h2 := Finset.sum_range_sub (fun j => Real.log (j : ℝ)) k
    simp only [Nat.cast_add, Nat.cast_one] at h1 h2
    have hsum : ∑ j ∈ Finset.Ico k N,
        (Real.log ((j : ℝ) + 1) - Real.log j)
        = Real.log N - Real.log k := by
      rw [h3, h1, h2]
      simp
    rw [← Finset.mul_sum, hsum]
    ring
  have hD : ∑ k ∈ Finset.Icc 1 N,
      (vonMangoldt k * Real.log N - vonMangoldt k * Real.log k)
      = ∑ j ∈ Finset.Ico 1 N,
          (Real.log ((j : ℝ) + 1) - Real.log j) * chebyshevPsi j := by
    rw [Finset.sum_congr rfl htel, Finset.sum_sigma']
    have hbij : ∑ x ∈ (Finset.Icc 1 N).sigma (fun k => Finset.Ico k N),
        vonMangoldt x.1 * (Real.log ((x.2 : ℝ) + 1) - Real.log x.2)
        = ∑ y ∈ (Finset.Ico 1 N).sigma (fun j => Finset.Icc 1 j),
            vonMangoldt y.2 * (Real.log ((y.1 : ℝ) + 1) - Real.log y.1) := by
      apply Finset.sum_nbij' (i := fun x => ⟨x.2, x.1⟩)
        (j := fun y => ⟨y.2, y.1⟩)
      · rintro ⟨k, j⟩ hx
        rw [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_Ico] at hx
        dsimp only at hx
        rw [Finset.mem_sigma, Finset.mem_Ico, Finset.mem_Icc]
        dsimp only
        omega
      · rintro ⟨j, k⟩ hy
        rw [Finset.mem_sigma, Finset.mem_Ico, Finset.mem_Icc] at hy
        dsimp only at hy
        rw [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_Ico]
        dsimp only
        omega
      · rintro ⟨k, j⟩ _
        rfl
      · rintro ⟨j, k⟩ _
        rfl
      · rintro ⟨k, j⟩ _
        rfl
    rw [hbij, Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only
    rw [← Finset.sum_mul,
      show (∑ k ∈ Finset.Icc 1 j, vonMangoldt k) = chebyshevPsi j from rfl]
    ring
  have hDle : ∑ j ∈ Finset.Ico 1 N,
      (Real.log ((j : ℝ) + 1) - Real.log j) * chebyshevPsi j
      ≤ 7 * N := by
    have hterm : ∀ j ∈ Finset.Ico 1 N,
        (Real.log ((j : ℝ) + 1) - Real.log j) * chebyshevPsi j
          ≤ 7 := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      have hj0 : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
      have hw := log_succ_sub_log_le hj.1
      have hw0 : 0 ≤ Real.log ((j : ℝ) + 1) - Real.log j := by
        have := Real.log_le_log hj0 (show (j : ℝ) ≤ (j : ℝ) + 1 by linarith)
        linarith
      have hψ0 : 0 ≤ chebyshevPsi j :=
        Finset.sum_nonneg fun m _ => vonMangoldt_nonneg
      calc (Real.log ((j : ℝ) + 1) - Real.log j) * chebyshevPsi j
          ≤ (1 / j) * (7 * j) :=
            mul_le_mul hw (chebyshevPsi_le_seven j) hψ0 (by positivity)
        _ = 7 := by field_simp
    calc ∑ j ∈ Finset.Ico 1 N,
          (Real.log ((j : ℝ) + 1) - Real.log j) * chebyshevPsi j
        ≤ ∑ _j ∈ Finset.Ico 1 N, (7 : ℝ) := Finset.sum_le_sum hterm
      _ = 7 * ((N : ℝ) - 1) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
          have : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
            rw [Nat.cast_sub hN, Nat.cast_one]
          rw [this]
          ring
      _ ≤ 7 * N := by
          have : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
          linarith
  have hsplit : ∑ k ∈ Finset.Icc 1 N,
      (vonMangoldt k * Real.log N - vonMangoldt k * Real.log k)
      = chebyshevPsi N * Real.log N
        - ∑ k ∈ Finset.Icc 1 N, vonMangoldt k * Real.log k := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul,
      show (∑ k ∈ Finset.Icc 1 N, vonMangoldt k) = chebyshevPsi N from rfl]
  rw [hsplit] at hD
  linarith [hD ▸ hDle]

end RHTower
