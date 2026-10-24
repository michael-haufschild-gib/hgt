import GaloisForLFunctions.SignedSuccessorArithmetic.TheSuccessorDilationCocycle
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The one-third successor floor

For a completely multiplicative sign `f` let `a(n) ∈ {0, 1}` record agreement across the step
`n → n+1` (`a(n) = 1` iff `f(n) = f(n+1)`). The dilation cocycle at `m = 2`,
`σ(2n) σ(2n+1) = σ(n)`, is equivalent to the per-step count

  `a(2n) + a(2n+1) + a(n) = 1 + 2 a(n) a(2n)`:

a disagreement at `n` forces exactly one agreement among `2n, 2n+1`, and an agreement at `n` forces
the two to agree with each other. Summing gives the **exact two-scale identity**

  `A(2N+1) + A(N) = a(1) + N + 2 E_N`,  `E_N = #{n ≤ N : a(n) = a(2n) = 1}`,

for the agreement count `A`, equivalently `C(2N+1) − σ(1) + C(N) = 4E_N − N` for the successor
correlation `C(N) = Σ_{n ≤ N} f(n) f(n+1)`. The defect `E_N` is a count, so it is nonnegative:
positivity is inherited from counting doubled agreements. Weighting the same step by `1/n` gives the
**logarithmic floor**

  `Σ_{n ≤ M, f(n) = f(n+1)} 1/n ≥ (1/3) log M − 1`,

equivalently `Σ_{n ≤ M} f(n) f(n+1)/n ≥ −(1/3) log M − 3`, for every completely multiplicative sign
and every `M ≥ 1`, with absolute constants. The constant `1/3` is optimal: the conductor-three
twins attain it (`TheFloorIsAttainedAtConductorThree`).
-/

namespace GaloisForLFunctions.SignedSuccessorArithmetic

open Finset

/-- `(-1 : ℤˣ) ≠ 1`. -/
theorem units_neg_one_ne_one : (-1 : ℤˣ) ≠ 1 := by decide

/-- Agreement indicator: `1` when the sign is kept across the step `n → n+1`. -/
def agree (f : ℕ → ℤˣ) (n : ℕ) : ℕ := if succSign f n = 1 then 1 else 0

theorem agree_le_one (f : ℕ → ℤˣ) (n : ℕ) : agree f n ≤ 1 := by
  unfold agree; split_ifs <;> omega

/-- The successor sign in terms of the agreement indicator. -/
theorem succSign_val_eq (f : ℕ → ℤˣ) (n : ℕ) :
    ((succSign f n : ℤˣ) : ℤ) = 2 * (agree f n : ℤ) - 1 := by
  unfold agree
  rcases Int.units_eq_one_or (succSign f n) with h | h <;>
    simp [h]

/-- The dilation cocycle at `m = 2`. -/
theorem succSign_two_mul_mul (f : CMSign) {n : ℕ} (hn : 0 < n) :
    succSign f (2 * n) * succSign f (2 * n + 1) = succSign f n := by
  have h := dilation_cocycle f (m := 2) two_pos hn
  rwa [prod_range_succ, prod_range_one, add_zero] at h

/-- **Per-step doubling count.** `a(2n) + a(2n+1) + a(n) = 1 + 2 a(n) a(2n)`. -/
theorem agree_doubling (f : CMSign) {n : ℕ} (hn : 0 < n) :
    agree f (2 * n) + agree f (2 * n + 1) + agree f n = 1 + 2 * (agree f n * agree f (2 * n)) := by
  have hw := (succSign_two_mul_mul f hn).symm
  unfold agree
  rcases Int.units_eq_one_or (succSign f (2 * n)) with hu | hu <;>
    rcases Int.units_eq_one_or (succSign f (2 * n + 1)) with hv | hv <;>
    simp [hu, hv] at hw ⊢ <;> simp [hw]

/-- Splitting `[1, 2N+1]` into `1` and the pairs `{2n, 2n+1}`. -/
theorem sum_Icc_two_mul_add_one {M : Type*} [AddCommMonoid M] (g : ℕ → M) (N : ℕ) :
    ∑ k ∈ Icc 1 (2 * N + 1), g k = g 1 + ∑ n ∈ Icc 1 N, (g (2 * n) + g (2 * n + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) + 1 = (2 * N + 1 + 1) + 1 by ring, sum_Icc_succ_top (by omega),
      sum_Icc_succ_top (by omega), ih, sum_Icc_succ_top (by omega)]
    simp only [add_assoc]
    rw [show 2 * N + (1 + 1) = 2 * (N + 1) by ring, show 2 * N + (2 + 1) = 2 * (N + 1) + 1 by ring]

/-! ## Counts -/

/-- The agreement count `A(N) = #{1 ≤ n ≤ N : f(n) = f(n+1)}`. -/
def agreeCount (f : ℕ → ℤˣ) (N : ℕ) : ℕ := ∑ n ∈ Icc 1 N, agree f n

/-- The doubled-agreement count `E_N = #{1 ≤ n ≤ N : a(n) = a(2n) = 1}`. -/
def doubleAgreeCount (f : ℕ → ℤˣ) (N : ℕ) : ℕ := ∑ n ∈ Icc 1 N, agree f n * agree f (2 * n)

/-- **Exact two-scale identity.** `A(2N+1) + A(N) = a(1) + N + 2 E_N`. -/
theorem two_scale_identity (f : CMSign) (N : ℕ) :
    agreeCount f (2 * N + 1) + agreeCount f N = agree f 1 + N + 2 * doubleAgreeCount f N := by
  rw [agreeCount, sum_Icc_two_mul_add_one, agreeCount, doubleAgreeCount, mul_sum, add_assoc,
    ← sum_add_distrib]
  have h : ∑ n ∈ Icc 1 N, (agree f (2 * n) + agree f (2 * n + 1) + agree f n) =
      ∑ n ∈ Icc 1 N, (1 + 2 * (agree f n * agree f (2 * n))) :=
    sum_congr rfl fun n hn => agree_doubling f (by simp at hn; omega)
  rw [h, sum_add_distrib, sum_const, Nat.card_Icc, smul_eq_mul, mul_one, Nat.add_sub_cancel]
  ring

/-- **Two-scale floor.** `A(2N+1) + A(N) ≥ N`. -/
theorem two_scale_floor (f : CMSign) (N : ℕ) : N ≤ agreeCount f (2 * N + 1) + agreeCount f N := by
  have := two_scale_identity f N; omega

/-- At one of the two scales `N`, `2N+1` the agreement density is at least one third. -/
theorem one_third_at_one_of_two_scales (f : CMSign) (N : ℕ) :
    N ≤ 3 * agreeCount f N + 1 ∨ 2 * N + 1 ≤ 3 * agreeCount f (2 * N + 1) := by
  have := two_scale_floor f N; omega

/-- The agreement density is at least one third (up to `1/(3N)`) at arbitrarily large scales. -/
theorem frequently_one_third (f : CMSign) (N₀ : ℕ) :
    ∃ N, N₀ ≤ N ∧ N ≤ 3 * agreeCount f N + 1 := by
  rcases one_third_at_one_of_two_scales f N₀ with h | h
  · exact ⟨N₀, le_rfl, h⟩
  · exact ⟨2 * N₀ + 1, by omega, by omega⟩

/-- The successor correlation `C(N) = Σ_{n ≤ N} f(n) f(n+1)`. -/
def succCorr (f : ℕ → ℤˣ) (N : ℕ) : ℤ := ∑ n ∈ Icc 1 N, ((succSign f n : ℤˣ) : ℤ)

theorem succCorr_eq (f : ℕ → ℤˣ) (N : ℕ) : succCorr f N = 2 * (agreeCount f N : ℤ) - N := by
  rw [succCorr, agreeCount]
  simp_rw [succSign_val_eq]
  rw [sum_sub_distrib, ← mul_sum, sum_const, Nat.card_Icc, Nat.add_sub_cancel]
  push_cast
  simp

/-- **Signed two-scale identity.** `C(2N+1) − σ(1) + C(N) = 4 E_N − N`. -/
theorem signed_two_scale_identity (f : CMSign) (N : ℕ) :
    succCorr f (2 * N + 1) - ((succSign f 1 : ℤˣ) : ℤ) + succCorr f N =
      4 * (doubleAgreeCount f N : ℤ) - N := by
  have h := two_scale_identity f N
  rw [succCorr_eq, succCorr_eq, succSign_val_eq]
  have h' : (agreeCount f (2 * N + 1) : ℤ) + agreeCount f N = agree f 1 + N +
      2 * doubleAgreeCount f N := by exact_mod_cast h
  push_cast
  linear_combination 2 * h'

/-- **Signed two-scale floor.** `C(2N+1) + C(N) ≥ σ(1) − N`. -/
theorem signed_two_scale_floor (f : CMSign) (N : ℕ) :
    ((succSign f 1 : ℤˣ) : ℤ) - N ≤ succCorr f (2 * N + 1) + succCorr f N := by
  have := signed_two_scale_identity f N
  have : (0 : ℤ) ≤ doubleAgreeCount f N := Nat.cast_nonneg _
  linarith

/-! ## The logarithmic floor -/

/-- The logarithmic agreement mass `L(N) = Σ_{n ≤ N} a(n)/n`. -/
noncomputable def logAgree (f : ℕ → ℤˣ) (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, (agree f n : ℝ) / n

theorem logAgree_mono (f : ℕ → ℤˣ) : Monotone (logAgree f) := by
  intro M N hMN
  exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hMN) fun n _ _ => by positivity

theorem harmonic_eq_sum (N : ℕ) : (harmonic N : ℝ) = ∑ n ∈ Icc 1 N, (1 : ℝ) / n := by
  rw [harmonic_eq_sum_Icc]; push_cast; simp

/-- `Σ_{n ≤ N} 1/(2n(2n+1)) ≤ 1/2`. -/
theorem sum_inv_two_mul_two_mul_add_one_le (N : ℕ) :
    ∑ n ∈ Icc 1 N, (1 : ℝ) / (2 * n * (2 * n + 1)) ≤ 1 / 2 - 1 / (2 * (N + 1)) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega)]
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have key : (1 : ℝ) / (2 * ((N + 1 : ℕ) : ℝ) * (2 * ((N + 1 : ℕ) : ℝ) + 1)) ≤
        1 / (2 * (N + 1)) - 1 / (2 * (((N + 1 : ℕ) : ℝ) + 1)) := by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    push_cast at ih key ⊢
    linarith

/-- The per-step lower bound behind the logarithmic floor. -/
theorem pair_term_ge (f : CMSign) {n : ℕ} (hn : 0 < n) :
    (1 - (agree f n : ℝ)) / (2 * n) - 1 / (2 * n * (2 * n + 1)) ≤
      (agree f (2 * n) : ℝ) / ((2 * n : ℕ) : ℝ) + (agree f (2 * n + 1) : ℝ) / ((2 * n + 1 : ℕ) : ℝ) := by
  have hcount : (1 : ℝ) - agree f n ≤ (agree f (2 * n) : ℝ) + agree f (2 * n + 1) := by
    have := agree_doubling f hn
    have h' : ((agree f (2 * n) + agree f (2 * n + 1) + agree f n : ℕ) : ℝ) =
        ((1 + 2 * (agree f n * agree f (2 * n)) : ℕ) : ℝ) := by rw [this]
    push_cast at h'
    nlinarith [Nat.cast_nonneg (α := ℝ) (agree f n * agree f (2 * n))]
  have ha1 : (agree f n : ℝ) ≤ 1 := by exact_mod_cast agree_le_one f n
  have hb0 : (0 : ℝ) ≤ agree f (2 * n) := Nat.cast_nonneg _
  have hc0 : (0 : ℝ) ≤ agree f (2 * n + 1) := Nat.cast_nonneg _
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  push_cast
  have e1 : (agree f (2 * n) : ℝ) / (2 * n + 1) ≤ (agree f (2 * n) : ℝ) / (2 * n) :=
    div_le_div_of_nonneg_left hb0 (by positivity) (by linarith)
  have e2 : (1 - (agree f n : ℝ)) / (2 * n) - 1 / (2 * n * (2 * n + 1)) ≤
      (1 - (agree f n : ℝ)) / (2 * n + 1) := by
    have hid : (1 - (agree f n : ℝ)) / (2 * n + 1) =
        (1 - (agree f n : ℝ)) / (2 * n) - (1 - (agree f n : ℝ)) / (2 * n * (2 * n + 1)) := by
      field_simp; ring
    have hle : (1 - (agree f n : ℝ)) / (2 * n * (2 * n + 1)) ≤ 1 / (2 * n * (2 * n + 1)) :=
      div_le_div_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) (agree f n)])
        (by positivity)
    linarith
  have e3 : (1 - (agree f n : ℝ)) / (2 * n + 1) ≤
      ((agree f (2 * n) : ℝ) + agree f (2 * n + 1)) / (2 * n + 1) :=
    div_le_div_of_nonneg_right hcount (by positivity)
  rw [add_div] at e3
  linarith

/-- `L(2N+1) ≥ H_N/3 − 1/3`. -/
theorem logAgree_two_mul_add_one_ge (f : CMSign) (N : ℕ) :
    (harmonic N : ℝ) / 3 - 1 / 3 ≤ logAgree f (2 * N + 1) := by
  have hsplit : logAgree f (2 * N + 1) = (agree f 1 : ℝ) / 1 +
      ∑ n ∈ Icc 1 N, ((agree f (2 * n) : ℝ) / ((2 * n : ℕ) : ℝ) +
        (agree f (2 * n + 1) : ℝ) / ((2 * n + 1 : ℕ) : ℝ)) := by
    rw [logAgree, sum_Icc_two_mul_add_one (fun k => (agree f k : ℝ) / k)]
    simp
  have hsum : ∑ n ∈ Icc 1 N, ((1 - (agree f n : ℝ)) / (2 * n) - 1 / (2 * n * (2 * n + 1))) ≤
      ∑ n ∈ Icc 1 N, ((agree f (2 * n) : ℝ) / ((2 * n : ℕ) : ℝ) +
        (agree f (2 * n + 1) : ℝ) / ((2 * n + 1 : ℕ) : ℝ)) :=
    sum_le_sum fun n hn => pair_term_ge f (by simp at hn; omega)
  have hlin : ∑ n ∈ Icc 1 N, ((1 - (agree f n : ℝ)) / (2 * n) - 1 / (2 * n * (2 * n + 1))) =
      (harmonic N : ℝ) / 2 - logAgree f N / 2 -
        ∑ n ∈ Icc 1 N, (1 : ℝ) / (2 * n * (2 * n + 1)) := by
    rw [harmonic_eq_sum, logAgree, Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    refine sum_congr rfl fun n _ => ?_
    ring
  have htel := sum_inv_two_mul_two_mul_add_one_le N
  have hmono := logAgree_mono f (show N ≤ 2 * N + 1 by omega)
  have ha : (0 : ℝ) ≤ agree f 1 := Nat.cast_nonneg _
  have hN : (0 : ℝ) < 2 * ((N : ℝ) + 1) := by positivity
  have : (0 : ℝ) ≤ 1 / (2 * ((N : ℝ) + 1)) := by positivity
  linarith

/-- **The one-third logarithmic floor.** For every completely multiplicative sign and `M ≥ 1`,
`Σ_{n ≤ M, f(n) = f(n+1)} 1/n ≥ (1/3) log M − 1`. -/
theorem one_third_log_floor (f : CMSign) {M : ℕ} (hM : 0 < M) :
    Real.log M / 3 - 1 ≤ logAgree f M := by
  obtain ⟨N, hN⟩ : ∃ N, M = 2 * N + 1 ∨ M = 2 * N + 2 := ⟨(M - 1) / 2, by omega⟩
  have hbase := logAgree_two_mul_add_one_ge f N
  have hH := log_add_one_le_harmonic N
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (x := 2) (by norm_num) (by norm_num); linarith
  have hMle : Real.log M ≤ Real.log 2 + Real.log ((N + 1 : ℕ) : ℝ) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    apply Real.log_le_log (by exact_mod_cast hM)
    push_cast; rcases hN with rfl | rfl <;> push_cast <;> linarith
  have hL : logAgree f (2 * N + 1) ≤ logAgree f M := logAgree_mono f (by omega)
  linarith

/-- The logarithmic successor correlation `Σ_{n ≤ N} f(n) f(n+1)/n`. -/
noncomputable def logSuccCorr (f : ℕ → ℤˣ) (N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, (((succSign f n : ℤˣ) : ℤ) : ℝ) / n

theorem logSuccCorr_eq (f : ℕ → ℤˣ) (N : ℕ) :
    logSuccCorr f N = 2 * logAgree f N - harmonic N := by
  rw [logSuccCorr, logAgree, harmonic_eq_sum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun n _ => ?_
  rw [succSign_val_eq]; push_cast; ring

/-- **Signed logarithmic floor.** `Σ_{n ≤ M} f(n) f(n+1)/n ≥ −(1/3) log M − 3`. -/
theorem neg_third_log_floor (f : CMSign) {M : ℕ} (hM : 0 < M) :
    -(Real.log M / 3) - 3 ≤ logSuccCorr f M := by
  rw [logSuccCorr_eq]
  have h1 := one_third_log_floor f hM
  have h2 := harmonic_le_one_add_log M
  linarith

end GaloisForLFunctions.SignedSuccessorArithmetic
