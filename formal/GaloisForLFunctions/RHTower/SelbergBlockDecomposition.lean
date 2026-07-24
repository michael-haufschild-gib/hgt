import GaloisForLFunctions.RHTower.SelbergFiberBlockBound

/-!
# The block decomposition of the Selberg fiber sum

For increasing fiber cuts `0 = c(0) < c(1) < ⋯ < c(K) = N` and per-block
ratio bounds `|R(t)| ≤ s(k)·t` on each `(c(k), c(k+1)]`,

`∑_{m ≤ N} W(m)·|R(⌊N/m⌋)| ≤ N·∑_k s(k)·(W/m-mass of the k-th m-block)`,

by tiling `[1, N]` with the antitone m-cuts `d(k) = ⌊N/(c(k)+1)⌋` and
pricing each block with the per-block fiber bound.  Substituted into
Selberg's second inequality this is the raw ratio recursion: the choice
of cuts (uniform vs gain blocks) decides the contraction.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

/-- **Block decomposition of the fiber sum**. -/
theorem fiber_sum_block_decomposition (N K : ℕ) (c : ℕ → ℕ) (s : ℕ → ℝ)
    (_hN : 1 ≤ N) (hc0 : c 0 = 0) (hcK : c K = N)
    (hmono : ∀ k, k < K → c k < c (k + 1))
    (hs : ∀ k, k < K → 0 ≤ s k)
    (hratio : ∀ k, k < K → ∀ t : ℕ, c k < t → t ≤ c (k + 1) →
      |psiRemainder t| ≤ s k * t) :
    ∑ m ∈ Finset.Icc 1 N,
        (vonMangoldt m * Real.log m + (vonMangoldt * vonMangoldt) m)
          * |psiRemainder (N / m)|
      ≤ (N : ℝ) * ∑ k ∈ Finset.range K, s k
          * ∑ m ∈ Finset.Ioc (N / (c (k + 1) + 1)) (N / (c k + 1)),
              (vonMangoldt m * Real.log m
                + (vonMangoldt * vonMangoldt) m) / m := by
  set d : ℕ → ℕ := fun k => N / (c k + 1) with hd
  have hdanti : ∀ k, k < K → d (k + 1) ≤ d k := by
    intro k hk
    exact Nat.div_le_div_left (by
      have := hmono k hk
      omega) (by omega)
  have hIcc : Finset.Icc 1 N = Finset.Ioc (d K) (d 0) := by
    have h0 : d 0 = N := by
      rw [hd]
      simp only [hc0]
      norm_num
    have hK : d K = 0 := by
      rw [hd]
      simp only [hcK]
      exact Nat.div_eq_of_lt (by omega)
    rw [h0, hK]
    ext x
    rw [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hpart := HTGeometry.sum_Ioc_partition
    (fun m => (vonMangoldt m * Real.log m
      + (vonMangoldt * vonMangoldt) m) * |psiRemainder (N / m)|)
    d K hdanti
  rw [hIcc, ← hpart]
  have hblock : ∀ k ∈ Finset.range K,
      ∑ m ∈ Finset.Ioc (d (k + 1)) (d k),
          (vonMangoldt m * Real.log m + (vonMangoldt * vonMangoldt) m)
            * |psiRemainder (N / m)|
        ≤ s k * N * ∑ m ∈ Finset.Ioc (N / (c (k + 1) + 1)) (N / (c k + 1)),
            (vonMangoldt m * Real.log m
              + (vonMangoldt * vonMangoldt) m) / m := by
    intro k hk
    rw [Finset.mem_range] at hk
    exact fiber_block_weighted_le (hs k hk)
      (fun t ht1 ht2 => hratio k hk t ht1 ht2)
  calc ∑ k ∈ Finset.range K, ∑ m ∈ Finset.Ioc (d (k + 1)) (d k),
        (vonMangoldt m * Real.log m + (vonMangoldt * vonMangoldt) m)
          * |psiRemainder (N / m)|
      ≤ ∑ k ∈ Finset.range K, s k * N
          * ∑ m ∈ Finset.Ioc (N / (c (k + 1) + 1)) (N / (c k + 1)),
              (vonMangoldt m * Real.log m
                + (vonMangoldt * vonMangoldt) m) / m :=
        Finset.sum_le_sum hblock
    _ = (N : ℝ) * ∑ k ∈ Finset.range K, s k
          * ∑ m ∈ Finset.Ioc (N / (c (k + 1) + 1)) (N / (c k + 1)),
              (vonMangoldt m * Real.log m
                + (vonMangoldt * vonMangoldt) m) / m := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring

/-- **Second inequality in block form**. -/
theorem selberg_second_block_form (N K : ℕ) (c : ℕ → ℕ) (s : ℕ → ℝ)
    (hN : 1 ≤ N) (hc0 : c 0 = 0) (hcK : c K = N)
    (hmono : ∀ k, k < K → c k < c (k + 1))
    (hs : ∀ k, k < K → 0 ≤ s k)
    (hratio : ∀ k, k < K → ∀ t : ℕ, c k < t → t ≤ c (k + 1) →
      |psiRemainder t| ≤ s k * t) :
    |psiRemainder N| * Real.log N ^ 2
      ≤ (N : ℝ) * (∑ k ∈ Finset.range K, s k
          * ∑ m ∈ Finset.Ioc (N / (c (k + 1) + 1)) (N / (c k + 1)),
              (vonMangoldt m * Real.log m
                + (vonMangoldt * vonMangoldt) m) / m)
        + 800 * N * Real.log N + 2900 * N := by
  have h1 := selberg_second_inequality N hN
  have h2 := fiber_sum_block_decomposition N K c s hN hc0 hcK hmono hs hratio
  have h3 : ∑ m ∈ Finset.Icc 1 N,
      (vonMangoldt m * Real.log m + (vonMangoldt * vonMangoldt) m)
        * |psiRemainder (N / m)| ≥ 0 := by
    apply Finset.sum_nonneg
    intro m hm
    rw [Finset.mem_Icc] at hm
    apply mul_nonneg _ (abs_nonneg _)
    exact add_nonneg
      (mul_nonneg vonMangoldt_nonneg
        (Real.log_nonneg (by exact_mod_cast hm.1)))
      (vonMangoldt_conv_nonneg m)
  linarith

end RHTower
