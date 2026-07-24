import GaloisForLFunctions.RHTower.WeightedSigmaTotalBound
import GaloisForLFunctions.HTGeometry.IocPartitionSum

/-!
# The weighted variation of the fiber remainder

The map `m ↦ |R(⌊N/m⌋)|` has `m`-weighted total variation `O(N log N)`:

`∑_{m ≤ N} m·||R(⌊N/m⌋)| − |R(⌊N/(m+1)⌋)|| ≤ 2N·log N + 9N`.

Each fiber gap's variation telescopes into steps `|R(u) − R(u−1)| =
|Λ(u) − 1| ≤ Λ(u) + 1`; the gaps partition `(0, N]`, the `m`-weight on
the gap containing `u` is at most `N/u`, and Mertens plus the harmonic sum
close the bound.  This is the error the Abel transfer of the Selberg
fiber sum pays exactly once against the `V(t) = 2t log t ± 420t`
cumulative — keeping the transfer at `O(N log N)`.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

/-- Step telescoping: `|R(B) − R(A)| ≤ ∑_{A < u ≤ B} (Λ(u) + 1)`. -/
theorem abs_psiRemainder_sub_le_sum {A B : ℕ} (hAB : A ≤ B) :
    |psiRemainder B - psiRemainder A|
      ≤ ∑ u ∈ Finset.Ioc A B, (vonMangoldt u + 1) := by
  have htel : psiRemainder B - psiRemainder A
      = ∑ u ∈ Finset.Ioc A B, (psiRemainder u - psiRemainder (u - 1)) := by
    have hre : ∑ u ∈ Finset.Ioc A B,
        (psiRemainder u - psiRemainder (u - 1))
        = ∑ j ∈ Finset.Ico A B,
            (psiRemainder (j + 1) - psiRemainder j) := by
      apply Finset.sum_nbij' (i := fun u => u - 1) (j := fun j => j + 1)
      · intro u hu
        rw [Finset.mem_Ioc] at hu
        rw [Finset.mem_Ico]
        omega
      · intro j hj
        rw [Finset.mem_Ico] at hj
        rw [Finset.mem_Ioc]
        omega
      · intro u hu
        rw [Finset.mem_Ioc] at hu
        omega
      · intro j _
        omega
      · intro u hu
        rw [Finset.mem_Ioc] at hu
        have h1 : u - 1 + 1 = u := by omega
        rw [h1]
    rw [hre, Finset.sum_Ico_eq_sub _ hAB,
      Finset.sum_range_sub (fun j => psiRemainder j),
      Finset.sum_range_sub (fun j => psiRemainder j)]
    ring
  rw [htel]
  calc |∑ u ∈ Finset.Ioc A B, (psiRemainder u - psiRemainder (u - 1))|
      ≤ ∑ u ∈ Finset.Ioc A B, |psiRemainder u - psiRemainder (u - 1)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u ∈ Finset.Ioc A B, (vonMangoldt u + 1) := by
        apply Finset.sum_le_sum
        intro u hu
        rw [Finset.mem_Ioc] at hu
        have hstep := psiRemainder_succ_sub (u - 1)
        have h1 : u - 1 + 1 = u := by omega
        rw [h1] at hstep
        rw [hstep, abs_le]
        constructor
        · have := vonMangoldt_nonneg (n := u)
          linarith
        · have := vonMangoldt_nonneg (n := u)
          have hlog := vonMangoldt_le_log (n := u)
          linarith [abs_nonneg (vonMangoldt u - 1)]

/-- **Weighted fiber variation**:
`∑_{m ≤ N} m·||R(⌊N/m⌋)| − |R(⌊N/(m+1)⌋)|| ≤ 2N log N + 9N`. -/
theorem sum_mul_abs_fiber_diff_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ m ∈ Finset.Icc 1 N, (m : ℝ)
        * |(|psiRemainder (N / m)| - |psiRemainder (N / (m + 1))|)|
      ≤ 2 * N * Real.log N + 9 * N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  -- per-`m` gap bound with the `N/u` weight
  have hterm : ∀ m ∈ Finset.Icc 1 N,
      (m : ℝ) * |(|psiRemainder (N / m)| - |psiRemainder (N / (m + 1))|)|
        ≤ ∑ u ∈ Finset.Ioc (N / (m + 1)) (N / m),
            (N : ℝ) / u * (vonMangoldt u + 1) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hAB : N / (m + 1) ≤ N / m :=
      Nat.div_le_div_left (by omega) (by omega)
    have habs : |(|psiRemainder (N / m)| - |psiRemainder (N / (m + 1))|)|
        ≤ |psiRemainder (N / m) - psiRemainder (N / (m + 1))| :=
      abs_abs_sub_abs_le_abs_sub _ _
    have hsum := abs_psiRemainder_sub_le_sum hAB
    calc (m : ℝ) * |(|psiRemainder (N / m)| - |psiRemainder (N / (m + 1))|)|
        ≤ (m : ℝ) * ∑ u ∈ Finset.Ioc (N / (m + 1)) (N / m),
            (vonMangoldt u + 1) := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg m)
          exact le_trans habs hsum
      _ = ∑ u ∈ Finset.Ioc (N / (m + 1)) (N / m),
            (m : ℝ) * (vonMangoldt u + 1) := by
          rw [Finset.mul_sum]
      _ ≤ ∑ u ∈ Finset.Ioc (N / (m + 1)) (N / m),
            (N : ℝ) / u * (vonMangoldt u + 1) := by
          apply Finset.sum_le_sum
          intro u hu
          rw [Finset.mem_Ioc] at hu
          have hupos : 0 < u := Nat.lt_of_le_of_lt (Nat.zero_le _) hu.1
          have hu0 : (0 : ℝ) < u := by exact_mod_cast hupos
          apply mul_le_mul_of_nonneg_right _ (by
            have := vonMangoldt_nonneg (n := u)
            linarith)
          -- `m ≤ N/u` since `u ≤ ⌊N/m⌋`
          have h1 : u * m ≤ N :=
            (Nat.le_div_iff_mul_le (by omega : 0 < m)).1 hu.2
          have h2 : m * u ≤ N := by
            rw [Nat.mul_comm]
            exact h1
          rw [le_div_iff₀ hu0]
          exact_mod_cast h2
  -- collapse the gaps via the partition
  have hpart := HTGeometry.sum_Ioc_partition
    (fun u => (N : ℝ) / u * (vonMangoldt u + 1))
    (fun k => N / (k + 1)) N
    (fun k _ => Nat.div_le_div_left (by omega) (by omega))
  dsimp only at hpart
  have hd0 : N / (0 + 1) = N := by norm_num
  have hdN : N / (N + 1) = 0 := Nat.div_eq_of_lt (by omega)
  rw [hd0, hdN] at hpart
  -- reindex `m ∈ Icc 1 N` to `k ∈ range N` with `m = k + 1`
  have hreindex : ∑ m ∈ Finset.Icc 1 N,
      ∑ u ∈ Finset.Ioc (N / (m + 1)) (N / m),
        (N : ℝ) / u * (vonMangoldt u + 1)
      = ∑ k ∈ Finset.range N,
          ∑ u ∈ Finset.Ioc (N / (k + 1 + 1)) (N / (k + 1)),
            (N : ℝ) / u * (vonMangoldt u + 1) := by
    apply Finset.sum_nbij' (i := fun m => m - 1) (j := fun k => k + 1)
    · intro m hm
      rw [Finset.mem_Icc] at hm
      rw [Finset.mem_range]
      omega
    · intro k hk
      rw [Finset.mem_range] at hk
      rw [Finset.mem_Icc]
      omega
    · intro m hm
      rw [Finset.mem_Icc] at hm
      omega
    · intro k _
      omega
    · intro m hm
      rw [Finset.mem_Icc] at hm
      have h1 : m - 1 + 1 = m := by omega
      rw [h1]
  -- the final harmonic evaluation
  have hIoc : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext x
    rw [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hval : ∑ u ∈ Finset.Icc 1 N,
      (N : ℝ) / u * (vonMangoldt u + 1)
      ≤ 2 * N * Real.log N + 9 * N := by
    have hsplit : ∀ u ∈ Finset.Icc 1 N,
        (N : ℝ) / u * (vonMangoldt u + 1)
          = (N : ℝ) * (vonMangoldt u / u) + (N : ℝ) * (1 / u) := by
      intro u hu
      rw [Finset.mem_Icc] at hu
      have hu0 : (0 : ℝ) < u := by exact_mod_cast (by omega : 0 < u)
      field_simp
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
    have hM := abs_le.1 (Mertens.mertens_first N hN)
    have hlog4 : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (x := (4 : ℝ)) (by norm_num)
      linarith
    have hH := sum_inv_le N hN
    have h1 : (N : ℝ) * ∑ u ∈ Finset.Icc 1 N, vonMangoldt u / u
        ≤ (N : ℝ) * (Real.log N + 7) := by
      apply mul_le_mul_of_nonneg_left _ hN0.le
      linarith [hM.2]
    have h2 : (N : ℝ) * ∑ u ∈ Finset.Icc 1 N, 1 / (u : ℝ)
        ≤ (N : ℝ) * (Real.log N + 2) := by
      apply mul_le_mul_of_nonneg_left _ hN0.le
      exact hH
    nlinarith [h1, h2, hN0]
  calc ∑ m ∈ Finset.Icc 1 N, (m : ℝ)
        * |(|psiRemainder (N / m)| - |psiRemainder (N / (m + 1))|)|
      ≤ ∑ m ∈ Finset.Icc 1 N,
          ∑ u ∈ Finset.Ioc (N / (m + 1)) (N / m),
            (N : ℝ) / u * (vonMangoldt u + 1) :=
        Finset.sum_le_sum hterm
    _ = ∑ k ∈ Finset.range N,
          ∑ u ∈ Finset.Ioc (N / (k + 1 + 1)) (N / (k + 1)),
            (N : ℝ) / u * (vonMangoldt u + 1) := hreindex
    _ = ∑ u ∈ Finset.Ioc 0 N, (N : ℝ) / u * (vonMangoldt u + 1) := hpart
    _ = ∑ u ∈ Finset.Icc 1 N, (N : ℝ) / u * (vonMangoldt u + 1) := by
        rw [hIoc]
    _ ≤ 2 * N * Real.log N + 9 * N := hval

end RHTower
