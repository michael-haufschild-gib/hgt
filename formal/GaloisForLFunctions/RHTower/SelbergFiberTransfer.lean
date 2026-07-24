import GaloisForLFunctions.RHTower.MWindowContraction
import GaloisForLFunctions.RHTower.FiberVariationBound
import GaloisForLFunctions.HTGeometry.DiscreteAbelIcc

/-!
# The Selberg fiber transfer

The Selberg-weighted fiber sum contracts against the trivial ratio:

`∑_{m ≤ N} (Λ(m)log m + (Λ*Λ)(m))·|R(⌊N/m⌋)|
   ≤ N·((a − θ)·(G(N) − G(x₁)) + O_{Q,c,x₁}(log N))`,

`G = log² + 2 log`, `θ = (a − ε')·ρ/(8·log(2Q))`.  Discrete Abel
summation trades the Selberg weight `W` for its evaluation
`V(m) = 2m·log m ± 420m`; the `±420m` pays the fiber variation
`∑ m·|Δ|R(⌊N/m⌋)||  ≤ 2N log N + 9N` exactly once; Abel back with the
exact antiderivative `2m·log m` returns increments in `[2 log m, 2 log m + 2]`,
and the smooth-weighted sum splits into a crude head (`m ≤ x₁`, ratio 8)
and the contracted m-window.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

/-- `R(0) = 0`. -/
theorem psiRemainder_zero : psiRemainder 0 = 0 := by
  simp [psiRemainder, chebyshevPsi]

/-- The partial sums of the `2m log m` increments telescope exactly. -/
theorem twoMulLog_partial_sum (m : ℕ) :
    ∑ k ∈ Finset.Icc 1 m,
        (2 * (k : ℝ) * Real.log k
          - 2 * ((k - 1 : ℕ) : ℝ) * Real.log ((k - 1 : ℕ) : ℝ))
      = 2 * m * Real.log m := by
  have hre : ∑ k ∈ Finset.Icc 1 m,
      (2 * (k : ℝ) * Real.log k
        - 2 * ((k - 1 : ℕ) : ℝ) * Real.log ((k - 1 : ℕ) : ℝ))
      = ∑ j ∈ Finset.range m,
          (2 * ((j + 1 : ℕ) : ℝ) * Real.log ((j + 1 : ℕ) : ℝ)
            - 2 * (j : ℝ) * Real.log j) := by
    apply Finset.sum_nbij' (i := fun k => k - 1) (j := fun j => j + 1)
    · intro k hk
      rw [Finset.mem_Icc] at hk
      rw [Finset.mem_range]
      omega
    · intro j hj
      rw [Finset.mem_range] at hj
      rw [Finset.mem_Icc]
      omega
    · intro k hk
      rw [Finset.mem_Icc] at hk
      omega
    · intro j _
      omega
    · intro k hk
      rw [Finset.mem_Icc] at hk
      have h1 : k - 1 + 1 = k := by omega
      rw [h1]
  rw [hre, Finset.sum_range_sub (fun j => 2 * (j : ℝ) * Real.log j) m]
  simp

/-- The `2m log m` increment is at most `2 log m + 2`. -/
theorem twoMulLog_increment_le {k : ℕ} (hk : 1 ≤ k) :
    2 * (k : ℝ) * Real.log k
      - 2 * ((k - 1 : ℕ) : ℝ) * Real.log ((k - 1 : ℕ) : ℝ)
      ≤ 2 * Real.log k + 2 := by
  rcases Nat.lt_or_ge k 2 with h1 | h2
  · have hk1 : k = 1 := by omega
    subst hk1
    simp [Real.log_one]
  · have hj : 1 ≤ k - 1 := by omega
    have h := log_succ_sub_log_le (j := k - 1) hj
    have hcast : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by
      push_cast [Nat.cast_sub hk]
      ring
    rw [hcast] at h
    have hk1R : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < k - 1)
    have hmul : ((k - 1 : ℕ) : ℝ)
        * (Real.log k - Real.log ((k - 1 : ℕ) : ℝ)) ≤ 1 := by
      calc ((k - 1 : ℕ) : ℝ) * (Real.log k - Real.log ((k - 1 : ℕ) : ℝ))
          ≤ ((k - 1 : ℕ) : ℝ) * (1 / ((k - 1 : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left h hk1R.le
        _ = 1 := by field_simp
    have hexpand : 2 * (k : ℝ) * Real.log k
        - 2 * ((k - 1 : ℕ) : ℝ) * Real.log ((k - 1 : ℕ) : ℝ)
        = 2 * Real.log k
          + 2 * (((k - 1 : ℕ) : ℝ)
            * (Real.log k - Real.log ((k - 1 : ℕ) : ℝ))) := by
      have hc : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        push_cast [Nat.cast_sub hk]
        ring
      rw [hc]
      ring
    rw [hexpand]
    linarith

set_option maxHeartbeats 1600000 in
/-- **The Selberg fiber transfer.** -/
theorem selberg_weight_fiber_transfer {a δ ρ κ : ℝ} {Q x₀ x₁ c N : ℕ}
    (ha : 0 < a) (hδ : 0 < δ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2)
    (hκ : 0 ≤ κ) (hQ1 : 1 ≤ Q) (hQ : 40 / δ + 2 < Real.log Q)
    (hx₁8 : 8 ≤ x₁) (hx₁ρ : 8 / ρ ≤ (x₁ : ℝ))
    (hx₁Q : Real.log ((2 * Q : ℕ) : ℝ) + 2 ≤ 2 * Real.log x₁)
    (hε'a : δ + ρ * (Real.log (1 / ρ) + 3) + κ ≤ a)
    (hratio : ∀ t : ℕ, x₀ ≤ t → |psiRemainder t| ≤ a * t)
    (hc8 : 8 * Q ≤ c)
    (hρc : 2 / ρ ≤ (c : ℝ) / (2 * Q) - 1)
    (hx₀c : (x₀ : ℝ) ≤ (c : ℝ) / (2 * Q) - 1)
    (hcx₁N : c * x₁ ≤ N)
    (hjunkc : ∀ t : ℕ, (c : ℝ) / (2 * Q) - 1 ≤ (t : ℝ) →
      Real.log N + 1 + 2 * Real.sqrt t * Real.log t ≤ κ * t) :
    ∑ m ∈ Finset.Icc 1 N,
        (vonMangoldt m * Real.log m + (vonMangoldt * vonMangoldt) m)
          * |psiRemainder (N / m)|
      ≤ (N : ℝ) * ((a - (a - (δ + ρ * (Real.log (1 / ρ) + 3) + κ)) * ρ
            / (8 * Real.log ((2 * Q : ℕ) : ℝ)))
          * ((Real.log N ^ 2 + 2 * Real.log N)
            - (Real.log x₁ ^ 2 + 2 * Real.log x₁))
        + (2 * Real.log N + 1) * (3 * a * ((2 * Real.log N + 8) / x₁))
        + 8 * ((2 * Real.log N + 8) / x₁)
        + 8 * Real.log c * (2 * Real.log N + 2)
        + 8 * (Real.log x₁ ^ 2 + 2 * Real.log x₁) + 66
        + 840 * Real.log N + 3780) := by
  have hx₁0 : 0 < x₁ := by omega
  have hN0 : 0 < N := by
    have : 0 < c * x₁ := Nat.mul_pos (by omega) hx₁0
    omega
  have hN1 : 1 ≤ N := hN0
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hx₁N : x₁ ≤ N := by
    have : 1 * x₁ ≤ c * x₁ := Nat.mul_le_mul_right x₁ (by omega)
    omega
  have hgN1 : |psiRemainder (N / (N + 1))| = 0 := by
    rw [Nat.div_eq_of_lt (by omega), psiRemainder_zero, abs_zero]
  -- Abel: trade the Selberg weight for its partial sums
  have hAbel := HTGeometry.sum_mul_eq_partial_mul_diff
    (fun m => vonMangoldt m * Real.log m + (vonMangoldt * vonMangoldt) m)
    (fun m => |psiRemainder (N / m)|) N
  rw [hgN1, mul_zero, add_zero] at hAbel
  -- replace `V(m)` by `2m log m` at fiber-variation cost
  have hFV := sum_mul_abs_fiber_diff_le N hN1
  have hVrep : ∑ m ∈ Finset.Icc 1 N,
      (∑ k ∈ Finset.Icc 1 m,
        (vonMangoldt k * Real.log k + (vonMangoldt * vonMangoldt) k))
        * (|psiRemainder (N / m)| - |psiRemainder (N / (m + 1))|)
      ≤ (∑ m ∈ Finset.Icc 1 N, 2 * (m : ℝ) * Real.log m
          * (|psiRemainder (N / m)| - |psiRemainder (N / (m + 1))|))
        + 420 * (2 * N * Real.log N + 9 * N) := by
    have hterm : ∀ m ∈ Finset.Icc 1 N,
        (∑ k ∈ Finset.Icc 1 m,
          (vonMangoldt k * Real.log k + (vonMangoldt * vonMangoldt) k))
          * (|psiRemainder (N / m)| - |psiRemainder (N / (m + 1))|)
        ≤ 2 * (m : ℝ) * Real.log m
            * (|psiRemainder (N / m)| - |psiRemainder (N / (m + 1))|)
          + 420 * ((m : ℝ)
            * |(|psiRemainder (N / m)| - |psiRemainder (N / (m + 1))|)|) := by
      intro m hm
      rw [Finset.mem_Icc] at hm
      have h420 := abs_selberg_weight_summatory m hm.1
      have h1 : (∑ k ∈ Finset.Icc 1 m,
          (vonMangoldt k * Real.log k + (vonMangoldt * vonMangoldt) k)
          - 2 * m * Real.log m)
          * (|psiRemainder (N / m)| - |psiRemainder (N / (m + 1))|)
          ≤ 420 * ((m : ℝ)
            * |(|psiRemainder (N / m)| - |psiRemainder (N / (m + 1))|)|) := by
        calc (∑ k ∈ Finset.Icc 1 m,
            (vonMangoldt k * Real.log k + (vonMangoldt * vonMangoldt) k)
            - 2 * m * Real.log m)
            * (|psiRemainder (N / m)| - |psiRemainder (N / (m + 1))|)
            ≤ |(∑ k ∈ Finset.Icc 1 m,
                (vonMangoldt k * Real.log k
                  + (vonMangoldt * vonMangoldt) k)
                - 2 * m * Real.log m)
              * (|psiRemainder (N / m)| - |psiRemainder (N / (m + 1))|)| :=
              le_abs_self _
          _ = |∑ k ∈ Finset.Icc 1 m,
                (vonMangoldt k * Real.log k
                  + (vonMangoldt * vonMangoldt) k)
                - 2 * m * Real.log m|
              * |(|psiRemainder (N / m)| - |psiRemainder (N / (m + 1))|)| :=
              abs_mul _ _
          _ ≤ 420 * (m : ℝ)
              * |(|psiRemainder (N / m)| - |psiRemainder (N / (m + 1))|)| :=
              mul_le_mul_of_nonneg_right h420 (abs_nonneg _)
          _ = 420 * ((m : ℝ)
              * |(|psiRemainder (N / m)| - |psiRemainder (N / (m + 1))|)|) := by
              ring
      linarith [h1]
    calc ∑ m ∈ Finset.Icc 1 N,
        (∑ k ∈ Finset.Icc 1 m,
          (vonMangoldt k * Real.log k + (vonMangoldt * vonMangoldt) k))
          * (|psiRemainder (N / m)| - |psiRemainder (N / (m + 1))|)
        ≤ ∑ m ∈ Finset.Icc 1 N,
            (2 * (m : ℝ) * Real.log m
              * (|psiRemainder (N / m)| - |psiRemainder (N / (m + 1))|)
            + 420 * ((m : ℝ)
              * |(|psiRemainder (N / m)|
                  - |psiRemainder (N / (m + 1))|)|)) :=
          Finset.sum_le_sum hterm
      _ = (∑ m ∈ Finset.Icc 1 N, 2 * (m : ℝ) * Real.log m
            * (|psiRemainder (N / m)| - |psiRemainder (N / (m + 1))|))
          + 420 * ∑ m ∈ Finset.Icc 1 N, (m : ℝ)
              * |(|psiRemainder (N / m)| - |psiRemainder (N / (m + 1))|)| := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ _ := by
          have := mul_le_mul_of_nonneg_left hFV
            (by norm_num : (0 : ℝ) ≤ 420)
          linarith
  -- Abel back with the exact antiderivative `2m log m`
  have hb := HTGeometry.sum_mul_eq_partial_mul_diff
    (fun k => 2 * (k : ℝ) * Real.log k
      - 2 * ((k - 1 : ℕ) : ℝ) * Real.log ((k - 1 : ℕ) : ℝ))
    (fun m => |psiRemainder (N / m)|) N
  rw [hgN1, mul_zero, add_zero] at hb
  have hb2 : ∑ m ∈ Finset.Icc 1 N,
      (∑ k ∈ Finset.Icc 1 m,
        (2 * (k : ℝ) * Real.log k
          - 2 * ((k - 1 : ℕ) : ℝ) * Real.log ((k - 1 : ℕ) : ℝ)))
        * (|psiRemainder (N / m)| - |psiRemainder (N / (m + 1))|)
      = ∑ m ∈ Finset.Icc 1 N, 2 * (m : ℝ) * Real.log m
          * (|psiRemainder (N / m)| - |psiRemainder (N / (m + 1))|) := by
    apply Finset.sum_congr rfl
    intro m _
    rw [twoMulLog_partial_sum]
  rw [hb2] at hb
  -- increments are at most the smooth weight `2 log m + 2`
  have hInc : ∑ m ∈ Finset.Icc 1 N,
      (2 * (m : ℝ) * Real.log m
        - 2 * ((m - 1 : ℕ) : ℝ) * Real.log ((m - 1 : ℕ) : ℝ))
        * |psiRemainder (N / m)|
      ≤ ∑ m ∈ Finset.Icc 1 N,
          (2 * Real.log m + 2) * |psiRemainder (N / m)| := by
    apply Finset.sum_le_sum
    intro m hm
    rw [Finset.mem_Icc] at hm
    exact mul_le_mul_of_nonneg_right (twoMulLog_increment_le hm.1)
      (abs_nonneg _)
  -- head: crude ratio 8 on `m ≤ x₁`
  have hhead : ∑ m ∈ Finset.Icc 1 x₁,
      (2 * Real.log m + 2) * |psiRemainder (N / m)|
      ≤ (N : ℝ) * (8 * (Real.log x₁ ^ 2 + 2 * Real.log x₁) + 66) := by
    have hpt : ∀ m ∈ Finset.Icc 1 x₁,
        (2 * Real.log m + 2) * |psiRemainder (N / m)|
          ≤ 8 * (N : ℝ) * ((2 * Real.log m + 2) / m) := by
      intro m hm
      rw [Finset.mem_Icc] at hm
      have hm0R : (0 : ℝ) < m := by
        exact_mod_cast (by omega : 0 < m)
      have hw0 : (0 : ℝ) ≤ 2 * Real.log m + 2 := by
        have := Real.log_nonneg
          (by exact_mod_cast hm.1 : (1 : ℝ) ≤ (m : ℝ))
        linarith
      have hcr := abs_psiRemainder_le (N / m)
      have hfl : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / m := by
        rw [le_div_iff₀ hm0R]
        exact_mod_cast Nat.div_mul_le_self N m
      calc (2 * Real.log m + 2) * |psiRemainder (N / m)|
          ≤ (2 * Real.log m + 2) * (8 * ((N : ℝ) / m)) := by
            apply mul_le_mul_of_nonneg_left _ hw0
            linarith
        _ = 8 * (N : ℝ) * ((2 * Real.log m + 2) / m) := by
            field_simp
    have hlogdiv := sum_log_div_le x₁ (by omega)
    have hinv := sum_inv_le x₁ (by omega)
    have hterms : ∀ m ∈ Finset.Icc 1 x₁,
        (2 * Real.log m + 2) / (m : ℝ)
          = 2 * (Real.log m / m) + 2 * (1 / m) := by
      intro m _
      ring
    calc ∑ m ∈ Finset.Icc 1 x₁,
          (2 * Real.log m + 2) * |psiRemainder (N / m)|
        ≤ ∑ m ∈ Finset.Icc 1 x₁,
            8 * (N : ℝ) * ((2 * Real.log m + 2) / m) :=
          Finset.sum_le_sum hpt
      _ = 8 * (N : ℝ) * ∑ m ∈ Finset.Icc 1 x₁,
            (2 * Real.log m + 2) / m := by
          rw [Finset.mul_sum]
      _ = 8 * (N : ℝ) * (2 * (∑ m ∈ Finset.Icc 1 x₁, Real.log m / m)
            + 2 * ∑ m ∈ Finset.Icc 1 x₁, 1 / (m : ℝ)) := by
          rw [Finset.sum_congr rfl hterms, Finset.sum_add_distrib,
            ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ 8 * (N : ℝ) * (2 * (Real.log x₁ ^ 2 / 2 + 1)
            + 2 * (Real.log x₁ + 2)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith [hlogdiv, hinv]
      _ ≤ (N : ℝ) * (8 * (Real.log x₁ ^ 2 + 2 * Real.log x₁) + 66) := by
          nlinarith [hNR]
  -- window: the contracted m-window on `(x₁, N]`
  have hwin := m_window_contraction_of_ratio ha hδ hρ0 hρ1 hκ hQ1 hQ hx₁8
    hx₁ρ hx₁Q hε'a hratio hc8 hρc hx₀c hcx₁N hjunkc
  -- split the smooth-weighted sum
  have hsplit : Finset.Icc 1 N = Finset.Icc 1 x₁ ∪ Finset.Ioc x₁ N := by
    ext t
    simp only [Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 x₁) (Finset.Ioc x₁ N) := by
    rw [Finset.disjoint_left]
    intro t ht ht'
    rw [Finset.mem_Icc] at ht
    rw [Finset.mem_Ioc] at ht'
    omega
  have hsmooth : ∑ m ∈ Finset.Icc 1 N,
      (2 * Real.log m + 2) * |psiRemainder (N / m)|
      = (∑ m ∈ Finset.Icc 1 x₁,
          (2 * Real.log m + 2) * |psiRemainder (N / m)|)
        + ∑ m ∈ Finset.Ioc x₁ N,
            (2 * Real.log m + 2) * |psiRemainder (N / m)| := by
    rw [hsplit, Finset.sum_union hdisj]
  -- assemble
  have hfinal : (N : ℝ) * ((a - (a - (δ + ρ * (Real.log (1 / ρ) + 3) + κ))
        * ρ / (8 * Real.log ((2 * Q : ℕ) : ℝ)))
        * ((Real.log N ^ 2 + 2 * Real.log N)
          - (Real.log x₁ ^ 2 + 2 * Real.log x₁))
      + (2 * Real.log N + 1) * (3 * a * ((2 * Real.log N + 8) / x₁))
      + 8 * ((2 * Real.log N + 8) / x₁)
      + 8 * Real.log c * (2 * Real.log N + 2))
      + (N : ℝ) * (8 * (Real.log x₁ ^ 2 + 2 * Real.log x₁) + 66)
      + 420 * (2 * N * Real.log N + 9 * N)
      = (N : ℝ) * ((a - (a - (δ + ρ * (Real.log (1 / ρ) + 3) + κ))
          * ρ / (8 * Real.log ((2 * Q : ℕ) : ℝ)))
          * ((Real.log N ^ 2 + 2 * Real.log N)
            - (Real.log x₁ ^ 2 + 2 * Real.log x₁))
        + (2 * Real.log N + 1) * (3 * a * ((2 * Real.log N + 8) / x₁))
        + 8 * ((2 * Real.log N + 8) / x₁)
        + 8 * Real.log c * (2 * Real.log N + 2)
        + 8 * (Real.log x₁ ^ 2 + 2 * Real.log x₁) + 66
        + 840 * Real.log N + 3780) := by
    ring
  rw [hAbel]
  linarith [hVrep, hb, hInc, hhead, hwin, hsmooth, hfinal]

end RHTower
