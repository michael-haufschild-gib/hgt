import GaloisForLFunctions.RHTower.VonMangoldtLogHarmonicSummatory

/-!
# The `(Λ*Λ)/id` harmonic summatory

`∑_{m ≤ N} (Λ*Λ)(m)/m = ½·log²N + O(log N)`:

the harmonically-weighted von Mangoldt function `f = Λ/id` satisfies
`(f*f)(m) = (Λ*Λ)(m)/m` on the divisor antidiagonal, so the hyperbola
swap gives `∑_a (Λ(a)/a)·M(⌊N/a⌋)` with `M` the Mertens sum; splitting
`M(⌊N/a⌋) = (log N − log a) + O(7) + O(1/⌊N/a⌋)` reduces to Mertens, the
`Λ·log/id` summatory, and a `2ψ(N)/N ≤ 14` floor-discrepancy.  Combined
with `abs_sum_vonMangoldt_log_div_sub_le` this evaluates the full
fiber-averaged Selberg weight `∑ (Λ log + Λ*Λ)(m)/m = log²N + O(log N)`.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

/-- The harmonically-weighted von Mangoldt function `Λ(m)/m`. -/
def vonMangoldtDiv : ArithmeticFunction ℝ :=
  ⟨fun m => vonMangoldt m / m, by simp⟩

theorem vonMangoldtDiv_apply (m : ℕ) :
    vonMangoldtDiv m = vonMangoldt m / m := rfl

/-- `(Λ/id) * (Λ/id) = (Λ*Λ)/id` pointwise. -/
theorem vonMangoldtDiv_mul_apply (m : ℕ) :
    (vonMangoldtDiv * vonMangoldtDiv) m
      = (vonMangoldt * vonMangoldt) m / m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hprod, hm0⟩ := Nat.mem_divisorsAntidiagonal.1 hp
  rw [vonMangoldtDiv_apply, vonMangoldtDiv_apply, div_mul_div_comm]
  congr 1
  rw [← Nat.cast_mul, hprod]

/-- **The `(Λ*Λ)/id` summatory**:
`|∑_{m ≤ N} (Λ*Λ)(m)/m − ½log²N| ≤ 30·log N + 120`. -/
theorem abs_sum_vonMangoldt_conv_div_sub_le (N : ℕ) (hN : 1 ≤ N) :
    |(∑ m ∈ Finset.Icc 1 N, (vonMangoldt * vonMangoldt) m / m)
        - Real.log N ^ 2 / 2| ≤ 30 * Real.log N + 120 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlN0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (x := (4 : ℝ)) (by norm_num)
    linarith
  have hM : ∀ j : ℕ, 1 ≤ j →
      |(∑ k ∈ Finset.Icc 1 j, vonMangoldt k / k) - Real.log j| ≤ 7 :=
    fun j hj => le_trans (Mertens.mertens_first j hj) (by linarith)
  -- the hyperbola swap for the harmonic weight
  have hswap : ∑ m ∈ Finset.Icc 1 N, (vonMangoldt * vonMangoldt) m / m
      = ∑ a ∈ Finset.Icc 1 N, (vonMangoldt a / a)
          * ∑ b ∈ Finset.Icc 1 (N / a), vonMangoldt b / b := by
    have h1 : ∀ m ∈ Finset.Icc 1 N,
        (vonMangoldt * vonMangoldt) m / m
          = (vonMangoldtDiv * vonMangoldtDiv) m := by
      intro m _
      rw [vonMangoldtDiv_mul_apply]
    rw [Finset.sum_congr rfl h1, sum_Icc_mul_apply vonMangoldtDiv
      vonMangoldtDiv N]
    rfl
  rw [hswap]
  -- the exact three-way split of the inner Mertens sum
  have hsplit : ∀ a ∈ Finset.Icc 1 N,
      (vonMangoldt a / a)
          * ∑ b ∈ Finset.Icc 1 (N / a), vonMangoldt b / b
        = (vonMangoldt a / a * Real.log N - vonMangoldt a * Real.log a / a)
          + (vonMangoldt a / a)
              * ((∑ b ∈ Finset.Icc 1 (N / a), vonMangoldt b / b)
                - Real.log ((N / a : ℕ) : ℝ))
          + (vonMangoldt a / a)
              * (Real.log ((N / a : ℕ) : ℝ)
                - (Real.log N - Real.log a)) := by
    intro a _
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  -- main term
  have hT := hM N hN
  have hTb := abs_le.1 hT
  have hmain : |(∑ a ∈ Finset.Icc 1 N, vonMangoldt a / a * Real.log N)
      - (∑ a ∈ Finset.Icc 1 N, vonMangoldt a * Real.log a / a)
      - Real.log N ^ 2 / 2| ≤ 22 * Real.log N + 50 := by
    have h1 : ∑ a ∈ Finset.Icc 1 N, vonMangoldt a / a * Real.log N
        = (∑ a ∈ Finset.Icc 1 N, vonMangoldt a / a) * Real.log N := by
      rw [Finset.sum_mul]
    have h2 := abs_le.1 (abs_sum_vonMangoldt_log_div_sub_le N hN)
    rw [h1, abs_le]
    constructor
    · nlinarith [hTb.1, hTb.2, h2.1, h2.2, hlN0]
    · nlinarith [hTb.1, hTb.2, h2.1, h2.2, hlN0]
  -- Mertens fiber error
  have hΛdiv0 : ∀ a : ℕ, 0 ≤ vonMangoldt a / (a : ℝ) := fun a =>
    div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg a)
  have herr1 : |∑ a ∈ Finset.Icc 1 N, (vonMangoldt a / a)
      * ((∑ b ∈ Finset.Icc 1 (N / a), vonMangoldt b / b)
        - Real.log ((N / a : ℕ) : ℝ))| ≤ 7 * Real.log N + 49 := by
    calc |∑ a ∈ Finset.Icc 1 N, (vonMangoldt a / a)
          * ((∑ b ∈ Finset.Icc 1 (N / a), vonMangoldt b / b)
            - Real.log ((N / a : ℕ) : ℝ))|
        ≤ ∑ a ∈ Finset.Icc 1 N, |(vonMangoldt a / a)
            * ((∑ b ∈ Finset.Icc 1 (N / a), vonMangoldt b / b)
              - Real.log ((N / a : ℕ) : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ Finset.Icc 1 N, (vonMangoldt a / a) * 7 := by
          apply Finset.sum_le_sum
          intro a ha
          rw [Finset.mem_Icc] at ha
          have hNa1 : 1 ≤ N / a :=
            (Nat.le_div_iff_mul_le (by omega : 0 < a)).2 (by omega)
          rw [abs_mul, abs_of_nonneg (hΛdiv0 a)]
          exact mul_le_mul_of_nonneg_left (hM (N / a) hNa1) (hΛdiv0 a)
      _ = (∑ a ∈ Finset.Icc 1 N, vonMangoldt a / a) * 7 := by
          rw [Finset.sum_mul]
      _ ≤ 7 * Real.log N + 49 := by
          nlinarith [hTb.2]
  -- floor-log discrepancy
  have herr2 : |∑ a ∈ Finset.Icc 1 N, (vonMangoldt a / a)
      * (Real.log ((N / a : ℕ) : ℝ) - (Real.log N - Real.log a))|
      ≤ 14 := by
    have hterm : ∀ a ∈ Finset.Icc 1 N,
        |(vonMangoldt a / a)
          * (Real.log ((N / a : ℕ) : ℝ) - (Real.log N - Real.log a))|
          ≤ 2 * vonMangoldt a / N := by
      intro a ha
      rw [Finset.mem_Icc] at ha
      have ha0 : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
      have hNa1 : 1 ≤ N / a :=
        (Nat.le_div_iff_mul_le (by omega : 0 < a)).2 (by omega)
      have hNa0 : (0 : ℝ) < ((N / a : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 0 < N / a)
      -- `0 ≤ δ ≤ 1/⌊N/a⌋` for `δ = log N − log a − log⌊N/a⌋`
      have hfl : ((N / a : ℕ) : ℝ) ≤ (N : ℝ) / a := by
        rw [le_div_iff₀ ha0]
        exact_mod_cast Nat.div_mul_le_self N a
      have hfl' : (N : ℝ) / a ≤ ((N / a : ℕ) : ℝ) + 1 := by
        rw [div_le_iff₀ ha0]
        have h1 : N < a * (N / a) + a := by
          have h2 := Nat.div_add_mod N a
          have h3 := Nat.mod_lt N (show 0 < a by omega)
          omega
        have h4 : (N : ℝ) < (a : ℝ) * ((N / a : ℕ) : ℝ) + a := by
          exact_mod_cast h1
        nlinarith [h4]
      have hlogdiv : Real.log N - Real.log a = Real.log ((N : ℝ) / a) :=
        (Real.log_div hN0.ne' ha0.ne').symm
      have hδ0 : 0 ≤ Real.log N - Real.log a
          - Real.log ((N / a : ℕ) : ℝ) := by
        rw [hlogdiv]
        have := Real.log_le_log hNa0 hfl
        linarith
      have hδu : Real.log N - Real.log a - Real.log ((N / a : ℕ) : ℝ)
          ≤ 1 / ((N / a : ℕ) : ℝ) := by
        rw [hlogdiv]
        have h1 : Real.log ((N : ℝ) / a)
            ≤ Real.log (((N / a : ℕ) : ℝ) + 1) :=
          Real.log_le_log (by positivity) hfl'
        have h2 := log_succ_sub_log_le hNa1
        linarith
      -- `1/⌊N/a⌋ ≤ 2a/N`
      have hhalf : 1 / ((N / a : ℕ) : ℝ) ≤ 2 * a / N := by
        have h1 : N < 2 * (a * (N / a)) := by
          have h2 := Nat.div_add_mod N a
          have h3 := Nat.mod_lt N (show 0 < a by omega)
          have h4 : a ≤ a * (N / a) := Nat.le_mul_of_pos_right a (by omega)
          omega
        have h5 : (N : ℝ) < 2 * ((a : ℝ) * ((N / a : ℕ) : ℝ)) := by
          exact_mod_cast h1
        rw [div_le_div_iff₀ hNa0 hN0]
        nlinarith [h5]
      have hR : |Real.log ((N / a : ℕ) : ℝ) - (Real.log N - Real.log a)|
          ≤ 2 * a / N := by
        rw [abs_sub_comm, abs_of_nonneg hδ0]
        linarith
      rw [abs_mul, abs_of_nonneg (hΛdiv0 a)]
      calc (vonMangoldt a / a)
            * |Real.log ((N / a : ℕ) : ℝ) - (Real.log N - Real.log a)|
          ≤ (vonMangoldt a / a) * (2 * a / N) :=
            mul_le_mul_of_nonneg_left hR (hΛdiv0 a)
        _ = 2 * vonMangoldt a / N := by
            field_simp
    calc |∑ a ∈ Finset.Icc 1 N, (vonMangoldt a / a)
          * (Real.log ((N / a : ℕ) : ℝ) - (Real.log N - Real.log a))|
        ≤ ∑ a ∈ Finset.Icc 1 N, |(vonMangoldt a / a)
            * (Real.log ((N / a : ℕ) : ℝ)
              - (Real.log N - Real.log a))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ Finset.Icc 1 N, 2 * vonMangoldt a / N :=
          Finset.sum_le_sum hterm
      _ = 2 * chebyshevPsi N / N := by
          rw [show (∑ a ∈ Finset.Icc 1 N, 2 * vonMangoldt a / N)
            = (2 * ∑ a ∈ Finset.Icc 1 N, vonMangoldt a) / N from by
              rw [Finset.mul_sum, Finset.sum_div],
            show (∑ a ∈ Finset.Icc 1 N, vonMangoldt a) = chebyshevPsi N
              from rfl]
      _ ≤ 14 := by
          rw [div_le_iff₀ hN0]
          nlinarith [chebyshevPsi_le_seven N]
  -- combine
  have h1 := abs_le.1 hmain
  have h2 := abs_le.1 herr1
  have h3 := abs_le.1 herr2
  rw [abs_le]
  constructor
  · nlinarith [h1.1, h2.1, h3.1, hlN0]
  · nlinarith [h1.2, h2.2, h3.2, hlN0]

end RHTower
