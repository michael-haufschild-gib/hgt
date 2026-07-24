import GaloisForLFunctions.RHTower.SelbergWeightEvaluation

/-!
# Selberg's second inequality

`|R(N)|·log²N ≤ ∑_{m ≤ N} (Λ(m)log m + (Λ*Λ)(m))·|R(⌊N/m⌋)|
   + 800·N·log N + 2900·N`

for `R = ψ − id`.  The remainder recursion is applied at `N` (multiplied
by `log N`) and again at every fiber `⌊N/k⌋`; the double fiber sum
regroups bilinearly into the `(Λ*Λ)` weight, the fiber errors sum to
`400N·(log N + 7)` by Mertens, and the floor-log discrepancy
`log N − log k − log⌊N/k⌋ ∈ [0, 1/⌊N/k⌋]` costs `8` per unit of `Λ`-mass.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

/-- The crude remainder bound `|R(j)| ≤ 8j`. -/
theorem abs_psiRemainder_le (j : ℕ) : |psiRemainder j| ≤ 8 * j := by
  have hψ0 : 0 ≤ chebyshevPsi j :=
    Finset.sum_nonneg fun m _ => vonMangoldt_nonneg
  have hψ7 := chebyshevPsi_le_seven j
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  rw [abs_le]
  constructor
  · simp only [psiRemainder]
    linarith
  · simp only [psiRemainder]
    linarith

/-- `(Λ*Λ)(m) ≥ 0`. -/
theorem vonMangoldt_conv_nonneg (m : ℕ) : 0 ≤ (vonMangoldt * vonMangoldt) m := by
  rw [ArithmeticFunction.mul_apply]
  exact Finset.sum_nonneg fun p _ =>
    mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg

/-- **Selberg's second inequality**. -/
theorem selberg_second_inequality (N : ℕ) (hN : 1 ≤ N) :
    |psiRemainder N| * Real.log N ^ 2
      ≤ (∑ m ∈ Finset.Icc 1 N,
          (vonMangoldt m * Real.log m + (vonMangoldt * vonMangoldt) m)
            * |psiRemainder (N / m)|)
        + 800 * N * Real.log N + 2900 * N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlN0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  -- fiber positivity facts
  have hfib : ∀ k ∈ Finset.Icc 1 N, 1 ≤ N / k := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    exact (Nat.le_div_iff_mul_le (by omega : 0 < k)).2 (by omega)
  -- the three-way split of `S₁·log N`
  have hABD : (∑ k ∈ Finset.Icc 1 N, vonMangoldt k * psiRemainder (N / k))
      * Real.log N
      = (∑ k ∈ Finset.Icc 1 N,
          vonMangoldt k * Real.log k * psiRemainder (N / k))
        + (∑ k ∈ Finset.Icc 1 N, vonMangoldt k
            * (psiRemainder (N / k) * Real.log ((N / k : ℕ) : ℝ)))
        + (∑ k ∈ Finset.Icc 1 N, vonMangoldt k
            * (Real.log N - Real.log k - Real.log ((N / k : ℕ) : ℝ))
            * psiRemainder (N / k)) := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  -- A: the `Λ·log` weight
  have hA : |∑ k ∈ Finset.Icc 1 N,
      vonMangoldt k * Real.log k * psiRemainder (N / k)|
      ≤ ∑ k ∈ Finset.Icc 1 N,
          vonMangoldt k * Real.log k * |psiRemainder (N / k)| := by
    calc |∑ k ∈ Finset.Icc 1 N,
          vonMangoldt k * Real.log k * psiRemainder (N / k)|
        ≤ ∑ k ∈ Finset.Icc 1 N,
            |vonMangoldt k * Real.log k * psiRemainder (N / k)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k ∈ Finset.Icc 1 N,
            vonMangoldt k * Real.log k * |psiRemainder (N / k)| := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mem_Icc] at hk
          rw [abs_mul, abs_mul,
            abs_of_nonneg vonMangoldt_nonneg,
            abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hk.1))]
  -- B: recursion at the fibers, regrouped bilinearly
  have hT : ∑ k ∈ Finset.Icc 1 N, vonMangoldt k
      * ∑ j ∈ Finset.Icc 1 (N / k), vonMangoldt j * psiRemainder (N / k / j)
      = ∑ m ∈ Finset.Icc 1 N,
          (vonMangoldt * vonMangoldt) m * psiRemainder (N / m) := by
    rw [hyperbola_bilinear_regroup vonMangoldt vonMangoldt psiRemainder N]
    apply Finset.sum_congr rfl
    intro m _
    rw [sum_antidiagonal_vonMangoldt_mul]
  have hBX : |(∑ k ∈ Finset.Icc 1 N, vonMangoldt k
      * (psiRemainder (N / k) * Real.log ((N / k : ℕ) : ℝ)))
      + ∑ k ∈ Finset.Icc 1 N, vonMangoldt k
          * ∑ j ∈ Finset.Icc 1 (N / k),
              vonMangoldt j * psiRemainder (N / k / j)|
      ≤ ∑ k ∈ Finset.Icc 1 N, vonMangoldt k * (400 * ((N / k : ℕ) : ℝ)) := by
    rw [← Finset.sum_add_distrib]
    calc |∑ k ∈ Finset.Icc 1 N,
          (vonMangoldt k * (psiRemainder (N / k) * Real.log ((N / k : ℕ) : ℝ))
            + vonMangoldt k * ∑ j ∈ Finset.Icc 1 (N / k),
                vonMangoldt j * psiRemainder (N / k / j))|
        ≤ ∑ k ∈ Finset.Icc 1 N,
            |vonMangoldt k * (psiRemainder (N / k) * Real.log ((N / k : ℕ) : ℝ))
              + vonMangoldt k * ∑ j ∈ Finset.Icc 1 (N / k),
                  vonMangoldt j * psiRemainder (N / k / j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.Icc 1 N,
            vonMangoldt k * (400 * ((N / k : ℕ) : ℝ)) := by
          apply Finset.sum_le_sum
          intro k hk
          have hrec := abs_psiRemainder_recursion (N / k) (hfib k hk)
          have hfactor : vonMangoldt k
              * (psiRemainder (N / k) * Real.log ((N / k : ℕ) : ℝ))
              + vonMangoldt k * ∑ j ∈ Finset.Icc 1 (N / k),
                  vonMangoldt j * psiRemainder (N / k / j)
              = vonMangoldt k
                * (psiRemainder (N / k) * Real.log ((N / k : ℕ) : ℝ)
                  + ∑ j ∈ Finset.Icc 1 (N / k),
                      vonMangoldt j * psiRemainder (N / k / j)) := by
            ring
          rw [hfactor, abs_mul, abs_of_nonneg vonMangoldt_nonneg]
          exact mul_le_mul_of_nonneg_left hrec vonMangoldt_nonneg
  have hMert : ∑ k ∈ Finset.Icc 1 N, vonMangoldt k * (400 * ((N / k : ℕ) : ℝ))
      ≤ 400 * N * (Real.log N + 7) := by
    have hterm : ∀ k ∈ Finset.Icc 1 N,
        vonMangoldt k * (400 * ((N / k : ℕ) : ℝ))
          ≤ 400 * N * (vonMangoldt k / k) := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      have hfl : ((N / k : ℕ) : ℝ) ≤ (N : ℝ) / k := by
        rw [le_div_iff₀ hk0]
        exact_mod_cast Nat.div_mul_le_self N k
      have h1 : vonMangoldt k * (400 * ((N / k : ℕ) : ℝ))
          ≤ vonMangoldt k * (400 * ((N : ℝ) / k)) := by
        apply mul_le_mul_of_nonneg_left _ vonMangoldt_nonneg
        linarith
      calc vonMangoldt k * (400 * ((N / k : ℕ) : ℝ))
          ≤ vonMangoldt k * (400 * ((N : ℝ) / k)) := h1
        _ = 400 * N * (vonMangoldt k / k) := by
            field_simp
    calc ∑ k ∈ Finset.Icc 1 N, vonMangoldt k * (400 * ((N / k : ℕ) : ℝ))
        ≤ ∑ k ∈ Finset.Icc 1 N, 400 * N * (vonMangoldt k / k) :=
          Finset.sum_le_sum hterm
      _ = 400 * N * ∑ k ∈ Finset.Icc 1 N, vonMangoldt k / k := by
          rw [Finset.mul_sum]
      _ ≤ 400 * N * (Real.log N + 7) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hm := abs_le.1 (Mertens.mertens_first N hN)
          have hlog4 : Real.log 4 ≤ 3 := by
            have := Real.log_le_sub_one_of_pos (x := (4 : ℝ)) (by norm_num)
            linarith
          linarith [hm.2]
  have hX : |∑ m ∈ Finset.Icc 1 N,
      (vonMangoldt * vonMangoldt) m * psiRemainder (N / m)|
      ≤ ∑ m ∈ Finset.Icc 1 N,
          (vonMangoldt * vonMangoldt) m * |psiRemainder (N / m)| := by
    calc |∑ m ∈ Finset.Icc 1 N,
          (vonMangoldt * vonMangoldt) m * psiRemainder (N / m)|
        ≤ ∑ m ∈ Finset.Icc 1 N,
            |(vonMangoldt * vonMangoldt) m * psiRemainder (N / m)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ m ∈ Finset.Icc 1 N,
            (vonMangoldt * vonMangoldt) m * |psiRemainder (N / m)| := by
          apply Finset.sum_congr rfl
          intro m _
          rw [abs_mul, abs_of_nonneg (vonMangoldt_conv_nonneg m)]
  -- D: the floor-log discrepancy
  have hD : |∑ k ∈ Finset.Icc 1 N, vonMangoldt k
      * (Real.log N - Real.log k - Real.log ((N / k : ℕ) : ℝ))
      * psiRemainder (N / k)|
      ≤ 56 * N := by
    have hterm : ∀ k ∈ Finset.Icc 1 N,
        |vonMangoldt k
          * (Real.log N - Real.log k - Real.log ((N / k : ℕ) : ℝ))
          * psiRemainder (N / k)|
          ≤ vonMangoldt k * 8 := by
      intro k hk
      have hk' := hk
      rw [Finset.mem_Icc] at hk'
      have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      have hM1 : 1 ≤ N / k := hfib k hk
      have hM0 : (0 : ℝ) < ((N / k : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 0 < N / k)
      have hfl : ((N / k : ℕ) : ℝ) ≤ (N : ℝ) / k := by
        rw [le_div_iff₀ hk0]
        exact_mod_cast Nat.div_mul_le_self N k
      have hfl' : (N : ℝ) / k ≤ ((N / k : ℕ) : ℝ) + 1 := by
        rw [div_le_iff₀ hk0]
        have h1 : N < k * (N / k) + k := by
          have h2 := Nat.div_add_mod N k
          have h3 := Nat.mod_lt N (show 0 < k by omega)
          omega
        have h4 : (N : ℝ) < (k : ℝ) * ((N / k : ℕ) : ℝ) + k := by
          exact_mod_cast h1
        nlinarith [h4]
      have hlogdiv : Real.log N - Real.log k = Real.log ((N : ℝ) / k) :=
        (Real.log_div hN0.ne' hk0.ne').symm
      have hδ0 : 0 ≤ Real.log N - Real.log k
          - Real.log ((N / k : ℕ) : ℝ) := by
        rw [hlogdiv]
        have := Real.log_le_log hM0 hfl
        linarith
      have hδu : Real.log N - Real.log k - Real.log ((N / k : ℕ) : ℝ)
          ≤ 1 / ((N / k : ℕ) : ℝ) := by
        rw [hlogdiv]
        have h1 : Real.log ((N : ℝ) / k)
            ≤ Real.log (((N / k : ℕ) : ℝ) + 1) :=
          Real.log_le_log (by positivity) hfl'
        have h2 := log_succ_sub_log_le hM1
        linarith
      have hR8 := abs_psiRemainder_le (N / k)
      rw [abs_mul, abs_mul, abs_of_nonneg vonMangoldt_nonneg,
        abs_of_nonneg hδ0, mul_assoc]
      apply mul_le_mul_of_nonneg_left _ vonMangoldt_nonneg
      calc (Real.log N - Real.log k - Real.log ((N / k : ℕ) : ℝ))
            * |psiRemainder (N / k)|
          ≤ (1 / ((N / k : ℕ) : ℝ)) * (8 * ((N / k : ℕ) : ℝ)) :=
            mul_le_mul hδu hR8 (abs_nonneg _) (by positivity)
        _ = 8 := by field_simp
    calc |∑ k ∈ Finset.Icc 1 N, vonMangoldt k
          * (Real.log N - Real.log k - Real.log ((N / k : ℕ) : ℝ))
          * psiRemainder (N / k)|
        ≤ ∑ k ∈ Finset.Icc 1 N, |vonMangoldt k
            * (Real.log N - Real.log k - Real.log ((N / k : ℕ) : ℝ))
            * psiRemainder (N / k)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.Icc 1 N, vonMangoldt k * 8 :=
          Finset.sum_le_sum hterm
      _ = 8 * chebyshevPsi N := by
          rw [← Finset.sum_mul,
            show (∑ k ∈ Finset.Icc 1 N, vonMangoldt k) = chebyshevPsi N
              from rfl]
          ring
      _ ≤ 56 * N := by
          have := chebyshevPsi_le_seven N
          linarith
  -- assemble
  have h0 := abs_psiRemainder_recursion N hN
  have hS1 : |psiRemainder N * Real.log N|
      ≤ 400 * N + |∑ k ∈ Finset.Icc 1 N,
          vonMangoldt k * psiRemainder (N / k)| := by
    have htri : |psiRemainder N * Real.log N|
        ≤ |psiRemainder N * Real.log N
            + ∑ k ∈ Finset.Icc 1 N, vonMangoldt k * psiRemainder (N / k)|
          + |∑ k ∈ Finset.Icc 1 N, vonMangoldt k * psiRemainder (N / k)| := by
      calc |psiRemainder N * Real.log N|
          = |(psiRemainder N * Real.log N
              + ∑ k ∈ Finset.Icc 1 N, vonMangoldt k * psiRemainder (N / k))
            - ∑ k ∈ Finset.Icc 1 N, vonMangoldt k * psiRemainder (N / k)| := by
            ring_nf
        _ ≤ _ := abs_sub _ _
    linarith
  have hstep1 : |psiRemainder N| * Real.log N ^ 2
      ≤ 400 * N * Real.log N
        + |(∑ k ∈ Finset.Icc 1 N, vonMangoldt k * psiRemainder (N / k))
            * Real.log N| := by
    have heq : |psiRemainder N| * Real.log N ^ 2
        = |psiRemainder N * Real.log N| * Real.log N := by
      rw [abs_mul, abs_of_nonneg hlN0]
      ring
    have hS1'' : |(∑ k ∈ Finset.Icc 1 N,
        vonMangoldt k * psiRemainder (N / k)) * Real.log N|
        = |∑ k ∈ Finset.Icc 1 N,
            vonMangoldt k * psiRemainder (N / k)| * Real.log N := by
      rw [abs_mul, abs_of_nonneg hlN0]
    rw [heq, hS1'']
    calc |psiRemainder N * Real.log N| * Real.log N
        ≤ (400 * N + |∑ k ∈ Finset.Icc 1 N,
            vonMangoldt k * psiRemainder (N / k)|) * Real.log N :=
          mul_le_mul_of_nonneg_right hS1 hlN0
      _ = 400 * N * Real.log N
          + |∑ k ∈ Finset.Icc 1 N,
              vonMangoldt k * psiRemainder (N / k)| * Real.log N := by
          ring
  have hsplit2 : |(∑ k ∈ Finset.Icc 1 N,
      vonMangoldt k * psiRemainder (N / k)) * Real.log N|
      ≤ (∑ k ∈ Finset.Icc 1 N,
          vonMangoldt k * Real.log k * |psiRemainder (N / k)|)
        + (∑ m ∈ Finset.Icc 1 N,
            (vonMangoldt * vonMangoldt) m * |psiRemainder (N / m)|)
        + 400 * N * (Real.log N + 7) + 56 * N := by
    rw [hABD]
    have hB : |∑ k ∈ Finset.Icc 1 N, vonMangoldt k
        * (psiRemainder (N / k) * Real.log ((N / k : ℕ) : ℝ))|
        ≤ (∑ m ∈ Finset.Icc 1 N,
            (vonMangoldt * vonMangoldt) m * |psiRemainder (N / m)|)
          + 400 * N * (Real.log N + 7) := by
      have htriB : |∑ k ∈ Finset.Icc 1 N, vonMangoldt k
          * (psiRemainder (N / k) * Real.log ((N / k : ℕ) : ℝ))|
          ≤ |(∑ k ∈ Finset.Icc 1 N, vonMangoldt k
              * (psiRemainder (N / k) * Real.log ((N / k : ℕ) : ℝ)))
            + ∑ k ∈ Finset.Icc 1 N, vonMangoldt k
                * ∑ j ∈ Finset.Icc 1 (N / k),
                    vonMangoldt j * psiRemainder (N / k / j)|
            + |∑ k ∈ Finset.Icc 1 N, vonMangoldt k
                * ∑ j ∈ Finset.Icc 1 (N / k),
                    vonMangoldt j * psiRemainder (N / k / j)| := by
        calc |∑ k ∈ Finset.Icc 1 N, vonMangoldt k
              * (psiRemainder (N / k) * Real.log ((N / k : ℕ) : ℝ))|
            = |((∑ k ∈ Finset.Icc 1 N, vonMangoldt k
                * (psiRemainder (N / k) * Real.log ((N / k : ℕ) : ℝ)))
              + ∑ k ∈ Finset.Icc 1 N, vonMangoldt k
                  * ∑ j ∈ Finset.Icc 1 (N / k),
                      vonMangoldt j * psiRemainder (N / k / j))
              - ∑ k ∈ Finset.Icc 1 N, vonMangoldt k
                  * ∑ j ∈ Finset.Icc 1 (N / k),
                      vonMangoldt j * psiRemainder (N / k / j)| := by
              ring_nf
          _ ≤ _ := abs_sub _ _
      have hXbound := hT ▸ hX
      linarith [htriB, hBX, hMert, hXbound]
    have htri3 : ∀ a b c : ℝ, |a + b + c| ≤ |a| + |b| + |c| := by
      intro a b c
      calc |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
        _ ≤ |a| + |b| + |c| := by linarith [abs_add_le a b]
    have h3 := htri3
      (∑ k ∈ Finset.Icc 1 N,
        vonMangoldt k * Real.log k * psiRemainder (N / k))
      (∑ k ∈ Finset.Icc 1 N, vonMangoldt k
        * (psiRemainder (N / k) * Real.log ((N / k : ℕ) : ℝ)))
      (∑ k ∈ Finset.Icc 1 N, vonMangoldt k
        * (Real.log N - Real.log k - Real.log ((N / k : ℕ) : ℝ))
        * psiRemainder (N / k))
    linarith [h3, hA, hB, hD]
  -- final combination
  have hW : ∑ m ∈ Finset.Icc 1 N,
      (vonMangoldt m * Real.log m + (vonMangoldt * vonMangoldt) m)
        * |psiRemainder (N / m)|
      = (∑ k ∈ Finset.Icc 1 N,
          vonMangoldt k * Real.log k * |psiRemainder (N / k)|)
        + ∑ m ∈ Finset.Icc 1 N,
            (vonMangoldt * vonMangoldt) m * |psiRemainder (N / m)| := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [hW]
  nlinarith [hstep1, hsplit2, hN0, hlN0]

end RHTower
