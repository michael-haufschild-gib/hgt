import GaloisForLFunctions.RHTower.SquarefreeCounting

/-!
# The squarefree counting asymptotic

`Σ_{n ≤ N} μ(n)² = N/ζ(2) + O(√N)`, with the explicit constant `3`.  Only `d ≤ √N` contributes to
the divisor form; the fractional parts contribute at most `√N`, and truncating the Möbius
square-reciprocal series at `√N` costs at most `N/√N`.
-/

namespace RHTower

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable section

theorem inv_sq_le_telescope {n : ℕ} (hn : 2 ≤ n) :
    1 / (n : ℝ) ^ 2 ≤ 1 / ((n : ℝ) - 1) - 1 / (n : ℝ) := by
  have hn1 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h0 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have h1 : (0 : ℝ) < (n : ℝ) := by linarith
  rw [div_sub_div _ _ (ne_of_gt h0) (ne_of_gt h1), div_le_div_iff₀ (by positivity) (by positivity)]
  ring_nf
  nlinarith

/-- The tail of `Σ 1/n²` beyond `D` is at most `1/D`. -/
theorem sum_inv_sq_tail_le {D : ℕ} (hD : 1 ≤ D) (M : ℕ) :
    ∑ n ∈ Finset.Icc (D + 1) M, 1 / (n : ℝ) ^ 2 ≤ 1 / (D : ℝ) := by
  have hD0 : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  rcases Nat.lt_or_ge M (D + 1) with hM | hM
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    positivity
  · have key : ∀ M : ℕ, D + 1 ≤ M →
        ∑ n ∈ Finset.Icc (D + 1) M, 1 / (n : ℝ) ^ 2 ≤ 1 / (D : ℝ) - 1 / (M : ℝ) := by
      intro M hM
      induction M, hM using Nat.le_induction with
      | base =>
        rw [Finset.Icc_self, Finset.sum_singleton]
        have h2 : 2 ≤ D + 1 := by omega
        have := inv_sq_le_telescope (n := D + 1) h2
        have hcast : ((D + 1 : ℕ) : ℝ) - 1 = (D : ℝ) := by push_cast; ring
        rw [hcast] at this
        exact this
      | succ M hM ih =>
        rw [Finset.sum_Icc_succ_top (by omega)]
        have h2 : 2 ≤ M + 1 := by omega
        have hstep := inv_sq_le_telescope (n := M + 1) h2
        have hcast : ((M + 1 : ℕ) : ℝ) - 1 = (M : ℝ) := by push_cast; ring
        rw [hcast] at hstep
        linarith [ih, hstep]
    have h := key M hM
    have hM0 : (0 : ℝ) < (M : ℝ) := by
      have : 0 < M := by omega
      exact_mod_cast this
    have : (0 : ℝ) < 1 / (M : ℝ) := by positivity
    linarith

/-- The Möbius square-reciprocal series sums to `1/ζ(2) = 6/π²`. -/
theorem hasSum_moebius_div_sq :
    HasSum (fun n : ℕ => (μ n : ℝ) / (n : ℝ) ^ 2) (6 / Real.pi ^ 2) := by
  have hs : (1 : ℝ) < ((2 : ℂ)).re := by norm_num
  have hsum : LSeriesSummable (fun n => ((μ n : ℤ) : ℂ)) (2 : ℂ) :=
    LSeriesSummable_moebius_iff.mpr hs
  have hval : (∑' b : ℕ, LSeries.term (fun n => ((μ n : ℤ) : ℂ)) (2 : ℂ) b)
      = (riemannZeta (2 : ℂ))⁻¹ := LSeries_moebius_eq_inv_riemannZeta hs
  have hz : (riemannZeta (2 : ℂ))⁻¹ = ((6 / Real.pi ^ 2 : ℝ) : ℂ) := by
    rw [riemannZeta_two]
    push_cast
    field_simp
  have hC : HasSum (LSeries.term (fun n => ((μ n : ℤ) : ℂ)) (2 : ℂ))
      (((6 / Real.pi ^ 2 : ℝ) : ℂ)) := by
    have := hsum.hasSum
    rw [hval, hz] at this
    exact this
  have hterm : ∀ n : ℕ, LSeries.term (fun n => ((μ n : ℤ) : ℂ)) (2 : ℂ) n
      = (((μ n : ℝ) / (n : ℝ) ^ 2 : ℝ) : ℂ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero (by omega)]
      have hcast : (2 : ℂ) = ((2 : ℕ) : ℂ) := by norm_num
      rw [hcast, Complex.cpow_natCast]
      push_cast
      rfl
  rw [funext hterm] at hC
  have hre := Complex.hasSum_re hC
  simp only [Complex.ofReal_re] at hre
  exact hre

/-- The truncated Möbius square-reciprocal series is within `1/D` of `6/π²`. -/
theorem abs_sum_moebius_div_sq_sub_le {D : ℕ} (hD : 1 ≤ D) :
    |(∑ d ∈ Finset.Icc 1 D, (μ d : ℝ) / (d : ℝ) ^ 2) - 6 / Real.pi ^ 2| ≤ 1 / (D : ℝ) := by
  classical
  have hD0 : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  set g : ℕ → ℝ := fun n => if n ≤ D then 0 else 1 / (n : ℝ) ^ 2 with hg
  have hgnn : ∀ n, 0 ≤ g n := by
    intro n
    rw [hg]
    dsimp only
    split_ifs
    · exact le_rfl
    · positivity
  have hgle : ∀ n, g n ≤ 1 / (n : ℝ) ^ 2 := by
    intro n
    rw [hg]
    dsimp only
    split_ifs
    · positivity
    · exact le_rfl
  have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hgsum : Summable g := Summable.of_nonneg_of_le hgnn hgle hbase
  have hgbound : ∑' n, g n ≤ 1 / (D : ℝ) := by
    refine hgsum.tsum_le_of_sum_le fun s => ?_
    set M := s.sup id with hM
    have hsub : s.filter (fun n => ¬ n ≤ D) ⊆ Finset.Icc (D + 1) M := by
      intro n hn
      rw [Finset.mem_filter] at hn
      rw [Finset.mem_Icc]
      exact ⟨by omega, Finset.le_sup (f := id) hn.1⟩
    have hsplit : ∑ n ∈ s, g n = ∑ n ∈ s.filter (fun n => ¬ n ≤ D), 1 / (n : ℝ) ^ 2 := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [hg]
      dsimp only
      split_ifs <;> rfl
    rw [hsplit]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_) (sum_inv_sq_tail_le hD M)
    intro i _ _
    positivity
  have hs := hasSum_moebius_div_sq
  have hcompl := hs.summable.sum_add_tsum_compl (s := Finset.Icc 1 D)
  rw [hs.tsum_eq] at hcompl
  set T : Set ℕ := (↑(Finset.Icc 1 D) : Set ℕ)ᶜ with hT
  have hdiff : (∑ d ∈ Finset.Icc 1 D, (μ d : ℝ) / (d : ℝ) ^ 2) - 6 / Real.pi ^ 2
      = -(∑' d : T, (μ (d : ℕ) : ℝ) / ((d : ℕ) : ℝ) ^ 2) := by
    rw [hT]
    linarith [hcompl]
  rw [hdiff, abs_neg]
  have hsubsum : Summable
      (fun d : T => (μ (d : ℕ) : ℝ) / ((d : ℕ) : ℝ) ^ 2) := hs.summable.subtype _
  have hnormsum : Summable (fun d : T => ‖(μ (d : ℕ) : ℝ) / ((d : ℕ) : ℝ) ^ 2‖) := hsubsum.norm
  refine le_trans (norm_tsum_le_tsum_norm hnormsum) ?_
  have hbdd : ∀ d : T, ‖(μ (d : ℕ) : ℝ) / ((d : ℕ) : ℝ) ^ 2‖ ≤ g (d : ℕ) := by
    rintro ⟨n, hn⟩
    rw [hT] at hn
    simp only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_Icc, not_and, not_le] at hn
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      simp [hg]
    · have hnD : D < n := hn h0
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h0
      rw [hg]
      dsimp only
      rw [if_neg (by omega)]
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ)^2)]
      have hmu : |((μ n : ℤ) : ℝ)| ≤ 1 := by
        by_cases h : Squarefree n
        · rw [moebius_apply_of_squarefree h]
          push_cast
          simp [abs_pow]
        · rw [moebius_eq_zero_of_not_squarefree h]
          simp
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
  calc (∑' d : T, ‖(μ (d : ℕ) : ℝ) / ((d : ℕ) : ℝ) ^ 2‖)
      ≤ ∑' d : T, g (d : ℕ) :=
        Summable.tsum_le_tsum hbdd hnormsum (hgsum.subtype _)
    _ ≤ ∑' n : ℕ, g n := Summable.tsum_subtype_le g T (fun n => hgnn n) hgsum
    _ ≤ 1 / (D : ℝ) := hgbound

/-! ## The squarefree counting asymptotic -/

theorem natDiv_frac_mem {N m : ℕ} (hm : 1 ≤ m) :
    0 ≤ (N : ℝ) / (m : ℝ) - ((N / m : ℕ) : ℝ) ∧ (N : ℝ) / (m : ℝ) - ((N / m : ℕ) : ℝ) < 1 := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hdiv : N = m * (N / m) + N % m := (Nat.div_add_mod N m).symm
  have hmod : N % m < m := Nat.mod_lt _ (by omega)
  have hcast : (N : ℝ) = (m : ℝ) * ((N / m : ℕ) : ℝ) + ((N % m : ℕ) : ℝ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) hdiv
  have hmodR : ((N % m : ℕ) : ℝ) < (m : ℝ) := by exact_mod_cast hmod
  have hmod0 : (0 : ℝ) ≤ ((N % m : ℕ) : ℝ) := Nat.cast_nonneg _
  constructor
  · rw [sub_nonneg, le_div_iff₀ hm0]
    nlinarith
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hm0]
    nlinarith

/-- **Equation (7i).**  The squarefree counting law with square-root error. -/
theorem abs_sum_moebius_sq_sub_le {N : ℕ} (hN : 1 ≤ N) :
    |(∑ n ∈ Finset.Icc 1 N, ((μ n : ℤ) : ℝ) ^ 2) - (6 / Real.pi ^ 2) * (N : ℝ)|
      ≤ 3 * Real.sqrt (N : ℝ) := by
  classical
  set D := Nat.sqrt N with hDdef
  have hD1 : 1 ≤ D := Nat.sqrt_pos.mpr hN
  have hD0 : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD1
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hDsq : D ^ 2 ≤ N := Nat.sqrt_le' N
  have hDlt : N < (D + 1) ^ 2 := Nat.lt_succ_sqrt' N
  have hDle : (D : ℝ) ≤ Real.sqrt (N : ℝ) := by
    rw [Real.le_sqrt hD0.le]
    · exact_mod_cast hDsq
    · exact hN0.le
  have hsqlt : Real.sqrt (N : ℝ) < (D : ℝ) + 1 := by
    have hR : (N : ℝ) < ((D : ℝ) + 1) ^ 2 := by exact_mod_cast hDlt
    have hs := Real.sq_sqrt hN0.le
    nlinarith [Real.sqrt_nonneg (N : ℝ)]
  have hDhalf : Real.sqrt (N : ℝ) ≤ 2 * (D : ℝ) := by
    have h1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
    linarith
  -- the exact identity, truncated at `D`
  have hident : (∑ n ∈ Finset.Icc 1 N, ((μ n : ℤ) : ℝ) ^ 2)
      = ∑ d ∈ Finset.Icc 1 D, ((μ d : ℤ) : ℝ) * ((N / (d * d) : ℕ) : ℝ) := by
    have hZ := sum_moebius_sq_Icc N
    have hR : (∑ n ∈ Finset.Icc 1 N, ((μ n : ℤ) : ℝ) ^ 2)
        = ∑ d ∈ Finset.Icc 1 N, ((μ d : ℤ) : ℝ) * ((N / (d * d) : ℕ) : ℝ) := by
      have hcast := congrArg (fun z : ℤ => (z : ℝ)) hZ
      push_cast at hcast
      exact hcast
    rw [hR]
    refine (Finset.sum_subset ?_ ?_).symm
    · intro d hd
      rw [Finset.mem_Icc] at hd ⊢
      exact ⟨hd.1, le_trans hd.2 (Nat.sqrt_le_self N)⟩
    · intro d hd hdD
      rw [Finset.mem_Icc] at hd hdD
      have hdgt : D < d := by omega
      have hzero : N / (d * d) = 0 := by
        refine Nat.div_eq_of_lt ?_
        have : N < d * d := by
          have h1 : D + 1 ≤ d := by omega
          calc N < (D + 1) ^ 2 := hDlt
            _ ≤ d * d := by nlinarith [h1]
        exact this
      rw [hzero]
      norm_num
  rw [hident]
  -- split off the fractional parts
  have hsplit : ∑ d ∈ Finset.Icc 1 D, ((μ d : ℤ) : ℝ) * ((N / (d * d) : ℕ) : ℝ)
      = (N : ℝ) * (∑ d ∈ Finset.Icc 1 D, ((μ d : ℤ) : ℝ) / (d : ℝ) ^ 2)
        - ∑ d ∈ Finset.Icc 1 D, ((μ d : ℤ) : ℝ)
            * ((N : ℝ) / ((d * d : ℕ) : ℝ) - ((N / (d * d) : ℕ) : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Finset.mem_Icc] at hd
    have hd0 : (0 : ℝ) < (d : ℝ) := by
      have : 0 < d := hd.1
      exact_mod_cast this
    have hcast : ((d * d : ℕ) : ℝ) = (d : ℝ) ^ 2 := by push_cast; ring
    rw [hcast]
    field_simp
    ring
  rw [hsplit]
  -- bound the two pieces
  have hmain : |(N : ℝ) * (∑ d ∈ Finset.Icc 1 D, ((μ d : ℤ) : ℝ) / (d : ℝ) ^ 2)
      - (6 / Real.pi ^ 2) * (N : ℝ)| ≤ 2 * Real.sqrt (N : ℝ) := by
    have h := abs_sum_moebius_div_sq_sub_le hD1
    have hfac : (N : ℝ) * (∑ d ∈ Finset.Icc 1 D, ((μ d : ℤ) : ℝ) / (d : ℝ) ^ 2)
        - (6 / Real.pi ^ 2) * (N : ℝ)
        = (N : ℝ) * ((∑ d ∈ Finset.Icc 1 D, ((μ d : ℤ) : ℝ) / (d : ℝ) ^ 2)
            - 6 / Real.pi ^ 2) := by ring
    rw [hfac, abs_mul, abs_of_nonneg hN0.le]
    have hbound : (N : ℝ) * |(∑ d ∈ Finset.Icc 1 D, ((μ d : ℤ) : ℝ) / (d : ℝ) ^ 2)
        - 6 / Real.pi ^ 2| ≤ (N : ℝ) * (1 / (D : ℝ)) :=
      mul_le_mul_of_nonneg_left h hN0.le
    have hND : (N : ℝ) * (1 / (D : ℝ)) ≤ 2 * Real.sqrt (N : ℝ) := by
      rw [mul_one_div, div_le_iff₀ hD0]
      have hs := Real.sq_sqrt hN0.le
      nlinarith [Real.sqrt_nonneg (N : ℝ), hDhalf]
    linarith
  have hfrac : |∑ d ∈ Finset.Icc 1 D, ((μ d : ℤ) : ℝ)
      * ((N : ℝ) / ((d * d : ℕ) : ℝ) - ((N / (d * d) : ℕ) : ℝ))| ≤ Real.sqrt (N : ℝ) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ d ∈ Finset.Icc 1 D, |((μ d : ℤ) : ℝ)
        * ((N : ℝ) / ((d * d : ℕ) : ℝ) - ((N / (d * d) : ℕ) : ℝ))| ≤ 1 := by
      intro d hd
      rw [Finset.mem_Icc] at hd
      have hdd : 1 ≤ d * d :=
        Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      obtain ⟨hf0, hf1⟩ := natDiv_frac_mem (N := N) hdd
      have hmu : |((μ d : ℤ) : ℝ)| ≤ 1 := by
        by_cases h : Squarefree d
        · rw [moebius_apply_of_squarefree h]
          push_cast
          simp [abs_pow]
        · rw [moebius_eq_zero_of_not_squarefree h]
          simp
      rw [abs_mul]
      have habs : |(N : ℝ) / ((d * d : ℕ) : ℝ) - ((N / (d * d) : ℕ) : ℝ)| ≤ 1 := by
        rw [abs_of_nonneg hf0]
        linarith
      nlinarith [abs_nonneg ((μ d : ℤ) : ℝ),
        abs_nonneg ((N : ℝ) / ((d * d : ℕ) : ℝ) - ((N / (d * d) : ℕ) : ℝ))]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
    have : ((D + 1 - 1 : ℕ) : ℝ) = (D : ℝ) := by
      have : D + 1 - 1 = D := by omega
      rw [this]
    rw [this]
    exact hDle
  have habs := abs_sub (a := (N : ℝ) * (∑ d ∈ Finset.Icc 1 D, ((μ d : ℤ) : ℝ) / (d : ℝ) ^ 2)
      - (6 / Real.pi ^ 2) * (N : ℝ))
    (b := ∑ d ∈ Finset.Icc 1 D, ((μ d : ℤ) : ℝ)
      * ((N : ℝ) / ((d * d : ℕ) : ℝ) - ((N / (d * d) : ℕ) : ℝ)))
  calc |(N : ℝ) * (∑ d ∈ Finset.Icc 1 D, ((μ d : ℤ) : ℝ) / (d : ℝ) ^ 2)
        - ∑ d ∈ Finset.Icc 1 D, ((μ d : ℤ) : ℝ)
            * ((N : ℝ) / ((d * d : ℕ) : ℝ) - ((N / (d * d) : ℕ) : ℝ))
        - (6 / Real.pi ^ 2) * (N : ℝ)|
      ≤ |(N : ℝ) * (∑ d ∈ Finset.Icc 1 D, ((μ d : ℤ) : ℝ) / (d : ℝ) ^ 2)
          - (6 / Real.pi ^ 2) * (N : ℝ)|
        + |∑ d ∈ Finset.Icc 1 D, ((μ d : ℤ) : ℝ)
            * ((N : ℝ) / ((d * d : ℕ) : ℝ) - ((N / (d * d) : ℕ) : ℝ))| := by
        have : (N : ℝ) * (∑ d ∈ Finset.Icc 1 D, ((μ d : ℤ) : ℝ) / (d : ℝ) ^ 2)
            - ∑ d ∈ Finset.Icc 1 D, ((μ d : ℤ) : ℝ)
                * ((N : ℝ) / ((d * d : ℕ) : ℝ) - ((N / (d * d) : ℕ) : ℝ))
            - (6 / Real.pi ^ 2) * (N : ℝ)
            = ((N : ℝ) * (∑ d ∈ Finset.Icc 1 D, ((μ d : ℤ) : ℝ) / (d : ℝ) ^ 2)
                - (6 / Real.pi ^ 2) * (N : ℝ))
              - (∑ d ∈ Finset.Icc 1 D, ((μ d : ℤ) : ℝ)
                  * ((N : ℝ) / ((d * d : ℕ) : ℝ) - ((N / (d * d) : ℕ) : ℝ))) := by ring
        rw [this]
        exact abs_sub _ _
    _ ≤ 2 * Real.sqrt (N : ℝ) + Real.sqrt (N : ℝ) := add_le_add hmain hfrac
    _ = 3 * Real.sqrt (N : ℝ) := by ring

end

end RHTower
