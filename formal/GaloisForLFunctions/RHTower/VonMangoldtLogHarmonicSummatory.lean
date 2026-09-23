import GaloisForLFunctions.RHTower.PsiRemainderWindowSmallValue

/-!
# The `Λ·log/id` harmonic summatory

`∑_{m ≤ N} Λ(m)·log m/m = ½·log²N + O(log N)`:

partial summation against the Mertens sum `M(t) = ∑_{k ≤ t} Λ(k)/k`
(`|M(t) − log t| ≤ 7`) turns the sum into
`M(N)·log N − ∑_j (log(j+1) − log j)·M(j)`, and the increment-weighted log
sum telescopes to `½log²N` up to `½∑ Δ² ≤ ½∑ 1/j² ≤ 1`.  This is half of
the fiber-averaged Selberg weight `∑ w(m)/m = log²N + O(log N)` that the
Erdős–Selberg contraction divides by.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

/-- Finite Basel bound: `∑_{j ≤ N} 1/j² ≤ 2`. -/
theorem sum_inv_sq_le (N : ℕ) : ∑ j ∈ Finset.Icc 1 N, 1 / (j : ℝ) ^ (2 : ℕ) ≤ 2 := by
  rcases Nat.lt_or_ge N 2 with hN2 | hN2
  · interval_cases N
    · simp
    · norm_num
  · have hins : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
      ext x
      simp [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hins, Finset.sum_insert (by simp [Finset.mem_Icc])]
    have hterm : ∀ j ∈ Finset.Icc 2 N,
        1 / (j : ℝ) ^ (2 : ℕ) ≤ 1 / ((j : ℝ) - 1) - 1 / j := by
      intro j hj
      rw [Finset.mem_Icc] at hj
      have hj1 : (1 : ℝ) < j := by exact_mod_cast (by omega : 1 < j)
      have hne : (j : ℝ) - 1 ≠ 0 := by linarith
      have hjne : (j : ℝ) ≠ 0 := by linarith
      have heq : 1 / ((j : ℝ) - 1) - 1 / j = 1 / (((j : ℝ) - 1) * j) := by
        rw [div_sub_div _ _ hne hjne]
        congr 1
        ring
      rw [heq]
      apply div_le_div_of_nonneg_left one_pos.le (by nlinarith)
      nlinarith
    have hre : ∑ j ∈ Finset.Icc 2 N, (1 / ((j : ℝ) - 1) - 1 / j)
        = ∑ i ∈ Finset.Icc 1 (N - 1), (1 / (i : ℝ) - 1 / ((i : ℝ) + 1)) := by
      apply Finset.sum_nbij' (i := fun j => j - 1) (j := fun i => i + 1)
      · intro j hj
        rw [Finset.mem_Icc] at hj
        rw [Finset.mem_Icc]
        omega
      · intro i hi
        rw [Finset.mem_Icc] at hi
        rw [Finset.mem_Icc]
        omega
      · intro j hj
        rw [Finset.mem_Icc] at hj
        omega
      · intro i _
        omega
      · intro j hj
        rw [Finset.mem_Icc] at hj
        have hc : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega), Nat.cast_one]
        rw [hc, show (j : ℝ) - 1 + 1 = (j : ℝ) from by ring]
    have htel := sum_reciprocal_telescope
      (k := 1) (N := N - 1) le_rfl (by omega)
    have hsum := Finset.sum_le_sum hterm
    have h1 : 1 / (((1 : ℕ)) : ℝ) ^ (2 : ℕ) = 1 := by norm_num
    rw [h1]
    have hnn : (0 : ℝ) ≤ 1 / ((((N - 1 : ℕ)) : ℝ) + 1) := by positivity
    have h2 : (1 : ℝ) / (((1 : ℕ)) : ℝ) = 1 := by norm_num
    rw [hre, htel, h2] at hsum
    linarith

/-- The log telescope: `∑_{1 ≤ j < N} (log(j+1) − log j) = log N`. -/
theorem sum_log_increment_eq (N : ℕ) (hN : 1 ≤ N) :
    ∑ j ∈ Finset.Ico 1 N, (Real.log ((j : ℝ) + 1) - Real.log j)
      = Real.log N := by
  have hcongr : ∑ j ∈ Finset.Ico 1 N,
      (Real.log ((j : ℝ) + 1) - Real.log j)
      = ∑ j ∈ Finset.Ico 1 N,
          (Real.log (((j + 1 : ℕ)) : ℝ) - Real.log ((j : ℕ) : ℝ)) := by
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  rw [hcongr, Finset.sum_Ico_eq_sub _ hN,
    Finset.sum_range_sub (fun j => Real.log ((j : ℕ) : ℝ)) N,
    Finset.sum_range_sub (fun j => Real.log ((j : ℕ) : ℝ)) 1]
  push_cast
  rw [Real.log_zero, Real.log_one]
  ring

/-- The squared-log telescope:
`∑_{1 ≤ j < N} (log²(j+1) − log²j) = log²N`. -/
theorem sum_log_sq_increment_eq (N : ℕ) (hN : 1 ≤ N) :
    ∑ j ∈ Finset.Ico 1 N,
        (Real.log ((j : ℝ) + 1) ^ (2 : ℕ) - Real.log j ^ (2 : ℕ))
      = Real.log N ^ (2 : ℕ) := by
  have hcongr : ∑ j ∈ Finset.Ico 1 N,
      (Real.log ((j : ℝ) + 1) ^ (2 : ℕ) - Real.log j ^ (2 : ℕ))
      = ∑ j ∈ Finset.Ico 1 N,
          (Real.log (((j + 1 : ℕ)) : ℝ) ^ (2 : ℕ)
            - Real.log ((j : ℕ) : ℝ) ^ (2 : ℕ)) := by
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  rw [hcongr, Finset.sum_Ico_eq_sub _ hN,
    Finset.sum_range_sub (fun j => Real.log ((j : ℕ) : ℝ) ^ (2 : ℕ)) N,
    Finset.sum_range_sub (fun j => Real.log ((j : ℕ) : ℝ) ^ (2 : ℕ)) 1]
  push_cast
  rw [Real.log_zero, Real.log_one]
  ring

/-- **The `Λ·log/id` summatory**:
`|∑_{m ≤ N} Λ(m)log m/m − ½log²N| ≤ 15·log N + 1`. -/
theorem abs_sum_vonMangoldt_log_div_sub_le (N : ℕ) (hN : 1 ≤ N) :
    |(∑ m ∈ Finset.Icc 1 N, vonMangoldt m * Real.log m / m)
        - Real.log N ^ (2 : ℕ) / 2| ≤ 15 * Real.log N + 1 := by
  have hlN0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (x := (4 : ℝ)) (by norm_num)
    linarith
  have hM : ∀ j : ℕ, 1 ≤ j →
      |(∑ k ∈ Finset.Icc 1 j, vonMangoldt k / k) - Real.log j| ≤ 7 :=
    fun j hj => le_trans (Mertens.mertens_first j hj) (by linarith)
  -- partial summation: regroup by log increments
  have hswap : ∑ m ∈ Finset.Icc 1 N, vonMangoldt m * Real.log m / m
      = ∑ j ∈ Finset.Ico 1 N, (Real.log ((j : ℝ) + 1) - Real.log j)
          * ∑ m ∈ Finset.Ioc j N, vonMangoldt m / m := by
    have hexp : ∀ m ∈ Finset.Icc 1 N,
        vonMangoldt m * Real.log m / m
          = ∑ j ∈ Finset.Ico 1 m, (vonMangoldt m / m)
              * (Real.log ((j : ℝ) + 1) - Real.log j) := by
      intro m hm
      rw [Finset.mem_Icc] at hm
      rw [← Finset.mul_sum, sum_log_increment_eq m hm.1]
      ring
    rw [Finset.sum_congr rfl hexp, Finset.sum_sigma']
    have hbij : ∑ x ∈ (Finset.Icc 1 N).sigma (fun m => Finset.Ico 1 m),
        (vonMangoldt x.1 / x.1)
          * (Real.log ((x.2 : ℝ) + 1) - Real.log x.2)
        = ∑ y ∈ (Finset.Ico 1 N).sigma (fun j => Finset.Ioc j N),
            (vonMangoldt y.2 / y.2)
              * (Real.log ((y.1 : ℝ) + 1) - Real.log y.1) := by
      apply Finset.sum_nbij' (i := fun x => ⟨x.2, x.1⟩)
        (j := fun y => ⟨y.2, y.1⟩)
      · rintro ⟨m, j⟩ hx
        rw [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_Ico] at hx
        dsimp only at hx
        rw [Finset.mem_sigma, Finset.mem_Ico, Finset.mem_Ioc]
        dsimp only
        omega
      · rintro ⟨j, m⟩ hy
        rw [Finset.mem_sigma, Finset.mem_Ico, Finset.mem_Ioc] at hy
        dsimp only at hy
        rw [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_Ico]
        dsimp only
        omega
      · rintro ⟨m, j⟩ _
        rfl
      · rintro ⟨j, m⟩ _
        rfl
      · rintro ⟨m, j⟩ _
        rfl
    rw [hbij, Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    ring
  -- Mertens tails
  have hMdiff : ∀ j ∈ Finset.Ico 1 N,
      ∑ m ∈ Finset.Ioc j N, vonMangoldt m / m
        = (∑ k ∈ Finset.Icc 1 N, vonMangoldt k / k)
          - ∑ k ∈ Finset.Icc 1 j, vonMangoldt k / k := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    have hu : Finset.Icc 1 N = Finset.Icc 1 j ∪ Finset.Ioc j N := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
      omega
    have hdisj : Disjoint (Finset.Icc 1 j) (Finset.Ioc j N) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      rw [Finset.mem_Icc] at hx
      rw [Finset.mem_Ioc] at hx'
      omega
    have hun := Finset.sum_union (f := fun k => vonMangoldt k / (k : ℝ)) hdisj
    rw [← hu] at hun
    linarith [hun]
  -- the Abel form
  have habel : ∑ m ∈ Finset.Icc 1 N, vonMangoldt m * Real.log m / m
      = (∑ k ∈ Finset.Icc 1 N, vonMangoldt k / k) * Real.log N
        - ∑ j ∈ Finset.Ico 1 N, (Real.log ((j : ℝ) + 1) - Real.log j)
            * ∑ k ∈ Finset.Icc 1 j, vonMangoldt k / k := by
    rw [hswap, Finset.sum_congr rfl (fun j hj => by rw [hMdiff j hj])]
    calc ∑ j ∈ Finset.Ico 1 N, (Real.log ((j : ℝ) + 1) - Real.log j)
          * ((∑ k ∈ Finset.Icc 1 N, vonMangoldt k / k)
            - ∑ k ∈ Finset.Icc 1 j, vonMangoldt k / k)
        = (∑ j ∈ Finset.Ico 1 N,
            (Real.log ((j : ℝ) + 1) - Real.log j)
              * (∑ k ∈ Finset.Icc 1 N, vonMangoldt k / k))
          - ∑ j ∈ Finset.Ico 1 N, (Real.log ((j : ℝ) + 1) - Real.log j)
              * ∑ k ∈ Finset.Icc 1 j, vonMangoldt k / k := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro j _
          ring
      _ = (∑ k ∈ Finset.Icc 1 N, vonMangoldt k / k) * Real.log N
          - ∑ j ∈ Finset.Ico 1 N, (Real.log ((j : ℝ) + 1) - Real.log j)
              * ∑ k ∈ Finset.Icc 1 j, vonMangoldt k / k := by
          rw [← Finset.sum_mul, sum_log_increment_eq N hN]
          ring
  -- increment nonnegativity and upper bound
  have hΔ : ∀ j ∈ Finset.Ico 1 N,
      0 ≤ Real.log ((j : ℝ) + 1) - Real.log j
        ∧ Real.log ((j : ℝ) + 1) - Real.log j ≤ 1 / j := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
    constructor
    · have := Real.log_le_log hj0 (show (j : ℝ) ≤ (j : ℝ) + 1 by linarith)
      linarith
    · exact log_succ_sub_log_le hj.1
  -- the increment-weighted log sum
  have hΔlogsum : |(∑ j ∈ Finset.Ico 1 N,
      (Real.log ((j : ℝ) + 1) - Real.log j) * Real.log j)
      - Real.log N ^ (2 : ℕ) / 2| ≤ 1 := by
    have hid : ∀ j ∈ Finset.Ico 1 N,
        (Real.log ((j : ℝ) + 1) - Real.log j) * Real.log j
          = (Real.log ((j : ℝ) + 1) ^ (2 : ℕ) - Real.log j ^ (2 : ℕ)) / 2
            - (Real.log ((j : ℝ) + 1) - Real.log j) ^ (2 : ℕ) / 2 := by
      intro j _
      ring
    rw [Finset.sum_congr rfl hid, Finset.sum_sub_distrib,
      ← Finset.sum_div, sum_log_sq_increment_eq N hN, ← Finset.sum_div]
    have hΔsq : 0 ≤ ∑ j ∈ Finset.Ico 1 N,
        (Real.log ((j : ℝ) + 1) - Real.log j) ^ (2 : ℕ) := by
      apply Finset.sum_nonneg
      intro j _
      positivity
    have hΔsq2 : ∑ j ∈ Finset.Ico 1 N,
        (Real.log ((j : ℝ) + 1) - Real.log j) ^ (2 : ℕ) ≤ 2 := by
      have hle : ∀ j ∈ Finset.Ico 1 N,
          (Real.log ((j : ℝ) + 1) - Real.log j) ^ (2 : ℕ) ≤ 1 / (j : ℝ) ^ (2 : ℕ) := by
        intro j hj
        have h := hΔ j hj
        have h2 : (1 : ℝ) / (j : ℝ) ^ (2 : ℕ) = (1 / j) ^ (2 : ℕ) := by
          rw [div_pow, one_pow]
        rw [h2]
        exact pow_le_pow_left₀ h.1 h.2 2
      calc ∑ j ∈ Finset.Ico 1 N,
            (Real.log ((j : ℝ) + 1) - Real.log j) ^ (2 : ℕ)
          ≤ ∑ j ∈ Finset.Ico 1 N, 1 / (j : ℝ) ^ (2 : ℕ) :=
            Finset.sum_le_sum hle
        _ ≤ ∑ j ∈ Finset.Icc 1 N, 1 / (j : ℝ) ^ (2 : ℕ) :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (by
                intro x hx
                rw [Finset.mem_Ico] at hx
                rw [Finset.mem_Icc]
                omega)
              (fun j _ _ => by positivity)
        _ ≤ 2 := sum_inv_sq_le N
    rw [abs_le]
    constructor <;> [nlinarith [hΔsq, hΔsq2]; nlinarith [hΔsq, hΔsq2]]
  -- the Mertens-error transfer
  have hΔM : |(∑ j ∈ Finset.Ico 1 N,
      (Real.log ((j : ℝ) + 1) - Real.log j)
        * ∑ k ∈ Finset.Icc 1 j, vonMangoldt k / k)
      - ∑ j ∈ Finset.Ico 1 N,
          (Real.log ((j : ℝ) + 1) - Real.log j) * Real.log j| ≤
      7 * Real.log N := by
    rw [← Finset.sum_sub_distrib]
    have hfac : ∀ j ∈ Finset.Ico 1 N,
        (Real.log ((j : ℝ) + 1) - Real.log j)
            * (∑ k ∈ Finset.Icc 1 j, vonMangoldt k / k)
          - (Real.log ((j : ℝ) + 1) - Real.log j) * Real.log j
        = (Real.log ((j : ℝ) + 1) - Real.log j)
            * ((∑ k ∈ Finset.Icc 1 j, vonMangoldt k / k) - Real.log j) := by
      intro j _
      ring
    rw [Finset.sum_congr rfl hfac]
    calc |∑ j ∈ Finset.Ico 1 N,
          (Real.log ((j : ℝ) + 1) - Real.log j)
            * ((∑ k ∈ Finset.Icc 1 j, vonMangoldt k / k) - Real.log j)|
        ≤ ∑ j ∈ Finset.Ico 1 N,
            |(Real.log ((j : ℝ) + 1) - Real.log j)
              * ((∑ k ∈ Finset.Icc 1 j, vonMangoldt k / k) - Real.log j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.Ico 1 N,
            7 * (Real.log ((j : ℝ) + 1) - Real.log j) := by
          apply Finset.sum_le_sum
          intro j hj
          rw [Finset.mem_Ico] at hj
          have hΔj := hΔ j (Finset.mem_Ico.2 hj)
          rw [abs_mul, abs_of_nonneg hΔj.1]
          calc (Real.log ((j : ℝ) + 1) - Real.log j)
                * |(∑ k ∈ Finset.Icc 1 j, vonMangoldt k / k) - Real.log j|
              ≤ (Real.log ((j : ℝ) + 1) - Real.log j) * 7 :=
                mul_le_mul_of_nonneg_left (hM j hj.1) hΔj.1
            _ = 7 * (Real.log ((j : ℝ) + 1) - Real.log j) := by ring
      _ = 7 * Real.log N := by
          rw [← Finset.mul_sum, sum_log_increment_eq N hN]
  -- final combination
  have hT := hM N hN
  rw [habel, abs_le]
  have hTb := abs_le.1 hT
  have hΔMb := abs_le.1 hΔM
  have hΔlb := abs_le.1 hΔlogsum
  constructor
  · nlinarith [hTb.1, hTb.2, hΔMb.1, hΔMb.2, hΔlb.1, hΔlb.2, hlN0]
  · nlinarith [hTb.1, hTb.2, hΔMb.1, hΔMb.2, hΔlb.1, hΔlb.2, hlN0]

end RHTower
