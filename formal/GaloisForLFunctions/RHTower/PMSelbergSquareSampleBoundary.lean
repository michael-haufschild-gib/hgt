import GaloisForLFunctions.RHTower.PMSelbergSublinearPowerBoundary

/-!
The coarse Selberg inputs, even with a sublinear first response, do not imply
the square-source upper bound required by the RH criterion. The existing tuned
positive power model supplies a counterexample. Its exact surviving boundary is
also proved: positive power models have a quadratic square-sample upper bound
if and only if their exponent is at most one half.

These model sequences are not the arithmetic Chebyshev remainder. The result
limits deductions from the displayed abstract inputs; it does not refute RH.
-/

open scoped BigOperators
open Filter Finset ArithmeticFunction

namespace RHTower

/-- Square samples of a positive power before the finite endpoint correction. -/
noncomputable def pmSquarePowerSum (σ : ℝ) (N : ℕ) : ℝ :=
  ∑ s ∈ Ico 1 N, (s : ℝ) ^ (2 * σ)

/-- A dyadic block retains enough positive mass to detect supercritical powers. -/
theorem pmSquarePowerSum_dyadic_lower {σ : ℝ} (hσ : 0 ≤ σ)
    {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * (n : ℝ) ^ (2 * σ) ≤ pmSquarePowerSum σ (2 * n) := by
  calc
    _ = ∑ s ∈ Ico n (2 * n), (n : ℝ) ^ (2 * σ) := by
      simp [show 2 * n - n = n by omega]
    _ ≤ ∑ s ∈ Ico n (2 * n), (s : ℝ) ^ (2 * σ) := by
      apply sum_le_sum
      intro s hs
      apply Real.rpow_le_rpow (Nat.cast_nonneg _)
      · exact_mod_cast (mem_Ico.mp hs).1
      · linarith
    _ ≤ pmSquarePowerSum σ (2 * n) := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro s hs
        rw [mem_Ico] at hs ⊢
        omega
      · intro s _ _
        exact Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- Sharp power threshold for a quadratic one-sided bound on square samples. -/
theorem pmSquarePowerSum_quadratic_upper_iff {σ : ℝ} (hσ : 0 < σ) :
    (∃ B : ℝ, ∀ N : ℕ, 2 ≤ N → pmSquarePowerSum σ N ≤ B * (N : ℝ) ^ 2) ↔
      σ ≤ 1 / 2 := by
  constructor
  · rintro ⟨B, hB⟩
    by_contra hbad
    have hp : 0 < 2 * σ - 1 := by linarith
    have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (2 * σ - 1)) atTop atTop :=
      (tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop
    obtain ⟨n, hn, hgt⟩ :=
      ((eventually_ge_atTop (1 : ℕ)).and (ht.eventually (eventually_gt_atTop (4 * B)))).exists
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hlower := pmSquarePowerSum_dyadic_lower hσ.le hn
    have hupper := hB (2 * n) (by omega)
    have heq : (n : ℝ) ^ 2 * (n : ℝ) ^ (2 * σ - 1) =
        (n : ℝ) * (n : ℝ) ^ (2 * σ) := by
      rw [Real.rpow_sub hnpos, Real.rpow_one]
      field_simp
    have hlarge := mul_lt_mul_of_pos_left hgt (sq_pos_of_pos hnpos)
    push_cast at hupper
    nlinarith
  · intro hhalf
    refine ⟨1, fun N hN => ?_⟩
    calc
      _ ≤ ∑ s ∈ Ico 1 N, (N : ℝ) := by
        apply sum_le_sum
        intro s hs
        have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast (mem_Ico.mp hs).1
        calc
          _ ≤ (s : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hs1 (by linarith)
          _ = (s : ℝ) := Real.rpow_one _
          _ ≤ N := by exact_mod_cast (mem_Ico.mp hs).2.le
      _ ≤ _ := by
        simp only [sum_const, nsmul_eq_mul, Nat.card_Ico, one_mul]
        rw [Nat.cast_sub (by omega : 1 ≤ N)]
        push_cast
        nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]

/-- The source correction at index one changes the square sum by exactly `-(1+c)`. -/
theorem sum_pmScaledPowerRemainder_squares {σ c : ℝ} (hσ : 0 < σ)
    {N : ℕ} (hN : 2 ≤ N) :
    (∑ s ∈ Ico 1 N, pmScaledPowerRemainder σ c (s ^ 2)) =
      c * pmSquarePowerSum σ N - (1 + c) := by
  have hterm (s : ℕ) : pmScaledPowerRemainder σ c (s ^ 2) =
      c * (s : ℝ) ^ (2 * σ) - (1 + c) * (if s = 1 then 1 else 0) := by
    rw [pmScaledPowerRemainder_eq, pmPowerRemainder_eq hσ]
    have hs : s ^ 2 = 1 ↔ s = 1 := by constructor <;> intro h <;> nlinarith
    rw [if_congr hs rfl rfl, Nat.cast_pow]
    rw [← Real.rpow_natCast_mul (Nat.cast_nonneg s) 2 σ]
    by_cases hs1 : s = 1
    · simp only [if_pos hs1, Nat.cast_ofNat]
      ring
    · simp [hs1]
  simp_rw [hterm]
  rw [sum_sub_distrib, ← mul_sum, ← mul_sum]
  have hmem : 1 ∈ Ico 1 N := by simp; omega
  simp [sum_ite_eq', hmem, pmSquarePowerSum]

/-- Positive amplitude and the endpoint correction preserve the exact half-power boundary. -/
theorem pmScaledPowerRemainder_squareSum_quadratic_upper_iff {σ c : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) :
    (∃ B : ℝ, ∀ N : ℕ, 2 ≤ N →
      (∑ s ∈ Ico 1 N, pmScaledPowerRemainder σ c (s ^ 2)) ≤ B * (N : ℝ) ^ 2) ↔
      σ ≤ 1 / 2 := by
  constructor
  · rintro ⟨B, hB⟩
    apply (pmSquarePowerSum_quadratic_upper_iff hσ).mp
    refine ⟨(B + 1 + c) / c, fun N hN => ?_⟩
    have hb := hB N hN
    rw [sum_pmScaledPowerRemainder_squares hσ hN] at hb
    have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hshift : 1 + c ≤ (1 + c) * (N : ℝ) ^ 2 := by
      calc
        _ = (1 + c) * 1 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hc).mpr
    nlinarith
  · intro hhalf
    obtain ⟨B, hB⟩ := (pmSquarePowerSum_quadratic_upper_iff hσ).mpr hhalf
    refine ⟨c * B, fun N hN => ?_⟩
    rw [sum_pmScaledPowerRemainder_squares hσ hN]
    have hb := mul_le_mul_of_nonneg_left (hB N hN) hc.le
    nlinarith

/-- Tuning the first Selberg response to `o(N)` does not control square-source growth. -/
theorem pmCancellingPower_no_squareSum_quadratic_upper :
    ¬ ∃ B : ℝ, ∀ N : ℕ, 2 ≤ N →
      (∑ s ∈ Ico 1 N, pmScaledPowerRemainder (3 / 4)
        (pmCancellingPowerAmplitude (3 / 4)) (s ^ 2)) ≤ B * (N : ℝ) ^ 2 := by
  intro h
  have hc := pmCancellingPowerAmplitude_bounds (by norm_num : (0 : ℝ) < 3 / 4)
    (by norm_num)
  have := (pmScaledPowerRemainder_squareSum_quadratic_upper_iff (by norm_num) hc.1).mp h
  norm_num at this

/-- Both coarse Selberg inequalities and an `o(N)` first response coexist with failure
of the square-source quadratic upper bound. -/
theorem exists_selberg_sublinear_squareSum_counterexample :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧
      Tendsto (fun N : ℕ => pmScaledPowerSelbergResponse (3 / 4) c N / (N : ℝ))
        atTop (nhds 0) ∧
      (∀ N : ℕ, 1 ≤ N → |pmScaledPowerSelbergResponse (3 / 4) c N| ≤ 400 * N) ∧
      (∀ N : ℕ, 1 ≤ N →
        |pmScaledPowerRemainder (3 / 4) c N| * Real.log N ^ 2 ≤
          (∑ m ∈ Icc 1 N, (vonMangoldt m * Real.log m + (vonMangoldt * vonMangoldt) m) *
            |pmScaledPowerRemainder (3 / 4) c (N / m)|) +
              800 * N * Real.log N + 2900 * N) ∧
      ¬ (∃ B : ℝ, ∀ N : ℕ, 2 ≤ N →
        (∑ s ∈ Ico 1 N, pmScaledPowerRemainder (3 / 4) c (s ^ 2)) ≤ B * (N : ℝ) ^ 2) := by
  have hc := pmCancellingPowerAmplitude_bounds (by norm_num : (0 : ℝ) < 3 / 4)
    (by norm_num)
  refine ⟨pmCancellingPowerAmplitude (3 / 4), hc.1, hc.2, ?_,
    pmCancellingPower_selberg_recursion, pmCancellingPower_selberg_second,
    pmCancellingPower_no_squareSum_quadratic_upper⟩
  exact (pmScaledPowerSelbergResponse_sublinear_iff (by norm_num) (by norm_num) _).mpr rfl

end RHTower
