import GaloisForLFunctions.MatomakiRadziwill.ZetaRouteT
import GaloisForLFunctions.RHTower.Sieve.MenonRouteTMoebiusPolynomialFrequency
import GaloisForLFunctions.RHTower.DirichletSummatorySwap
import GaloisForLFunctions.RHTower.LiouvilleSummatoryRH

/-!
# Low frequencies for `λ`

`λ = μ * 1_□` (`RHTower.liouvilleC_eq_moebius_mul`) and the twist `n^{-iτ}` is completely
multiplicative, so (`sum_liouvilleTwist_eq`)

`Σ_{n≤N} λ(n)n^{-iτ} = Σ_{d²≤N} d^{-2iτ} M(⌊N/d²⌋, τ)`,   `M(y, τ) = Σ_{m≤y} μ(m)m^{-iτ}`.

The corpus twisted Mertens bound `|M(y, τ)| ≤ K y e^{-(log y)^{1/20}}` for `|τ| ≤ y^{24}`
(`Sieve.exists_norm_sum_moebiusTwist_le_rate_pow_twentyFour`) on `d ≤ N^{1/4}` and `|M| ≤ y` beyond
give (`exists_norm_sum_liouvilleTwist_le`)

`|Σ_{n≤N} λ(n)n^{-iτ}| ≤ 2KN e^{-((log N)/4)^{1/20}} + 4N^{3/4}`   for `2|τ| ≤ √N`.

Summation by parts against `1/n` on `(X, 4X]` bounds `F(w) = Σ_{X<n≤4X} λ(n)/n · n^{2πiw}` by eight
times the relative partial-sum bound (`norm_fullPoly_liouville_le`), so the low frequencies
`2π|w| ≤ (log X)^{19}` contribute `o(1)` to the mean square (`eventually_lowFreq_integral_le`).
-/

open Finset Filter Topology Complex ArithmeticFunction RHTower.Sieve MeasureTheory

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

/-- `μ(n)n^{-iτ}` as an arithmetic function. -/
def muTwistAF (τ : ℝ) : ArithmeticFunction ℂ := ⟨moebiusTwist τ, moebiusTwist_zero τ⟩

/-- `1_□(n)n^{-iτ}` as an arithmetic function. -/
def sqTwistAF (τ : ℝ) : ArithmeticFunction ℂ :=
  ⟨fun n => RHTower.squareIndicatorAF n * (n : ℂ) ^ (-((τ : ℂ) * I)), by
    simp [RHTower.squareIndicatorAF]⟩

theorem sqTwistAF_apply (τ : ℝ) (n : ℕ) :
    sqTwistAF τ n = RHTower.squareIndicatorAF n * (n : ℂ) ^ (-((τ : ℂ) * I)) := rfl

theorem muTwistAF_apply (τ : ℝ) (n : ℕ) : muTwistAF τ n = moebiusTwist τ n := rfl

/-- **The twisted convolution identity** `(1_□ n^{-iτ}) * (μ n^{-iτ}) = λ n^{-iτ}`. -/
theorem sqTwist_mul_muTwist_apply (τ : ℝ) (n : ℕ) :
    (sqTwistAF τ * muTwistAF τ) n = (liouville n : ℂ) * (n : ℂ) ^ (-((τ : ℂ) * I)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [ArithmeticFunction.mul_apply]
  have hterm : ∀ x ∈ n.divisorsAntidiagonal, sqTwistAF τ x.1 * muTwistAF τ x.2
      = (RHTower.squareIndicatorAF x.1 * (ArithmeticFunction.moebius : ArithmeticFunction ℂ) x.2)
        * (n : ℂ) ^ (-((τ : ℂ) * I)) := by
    intro x hx
    have hxn : x.1 * x.2 = n := (Nat.mem_divisorsAntidiagonal.mp hx).1
    rw [sqTwistAF_apply, muTwistAF_apply, moebiusTwist, ArithmeticFunction.intCoe_apply, ← hxn,
      Nat.cast_mul, natCast_mul_natCast_cpow]
    ring
  have hconv : (RHTower.squareIndicatorAF * (ArithmeticFunction.moebius : ArithmeticFunction ℂ)) n
      = (liouville n : ℂ) := by
    rw [mul_comm, ← RHTower.liouvilleC_eq_moebius_mul, RHTower.liouvilleC_apply]
  rw [sum_congr rfl hterm, ← sum_mul, ← ArithmeticFunction.mul_apply, hconv]

/-- **The square-dilation identity** for twisted Liouville partial sums. -/
theorem sum_liouvilleTwist_eq (τ : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (liouville n : ℂ) * (n : ℂ) ^ (-((τ : ℂ) * I))
      = ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (((d ^ 2 : ℕ) : ℂ) ^ (-((τ : ℂ) * I)))
          * ∑ m ∈ Finset.Icc 1 (N / d ^ 2), moebiusTwist τ m := by
  have h1 : ∑ n ∈ Finset.Icc 1 N, (liouville n : ℂ) * (n : ℂ) ^ (-((τ : ℂ) * I))
      = ∑ b ∈ Finset.Icc 1 N, sqTwistAF τ b * ∑ m ∈ Finset.Icc 1 (N / b), muTwistAF τ m := by
    rw [← RHTower.sum_Icc_mul_apply]
    exact sum_congr rfl fun n _ => (sqTwist_mul_muTwist_apply τ n).symm
  rw [h1]
  -- only squares contribute
  have hsub : (Finset.Icc 1 (Nat.sqrt N)).image (fun d => d ^ 2) ⊆ Finset.Icc 1 N := by
    intro b hb
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hb
    rw [Finset.mem_Icc] at hd ⊢
    exact ⟨Nat.one_le_pow _ _ (by omega), by
      have := Nat.sqrt_le N
      calc d ^ 2 = d * d := sq d
        _ ≤ Nat.sqrt N * Nat.sqrt N := Nat.mul_le_mul hd.2 hd.2
        _ ≤ N := this⟩
  rw [← Finset.sum_subset hsub fun b hb hb' => ?_]
  · rw [Finset.sum_image fun x _ y _ h => Nat.pow_left_injective (by norm_num) h]
    refine sum_congr rfl fun d hd => ?_
    have hd1 : d ≠ 0 := by rw [Finset.mem_Icc] at hd; omega
    have hsq : RHTower.squareIndicatorAF (d ^ 2) = 1 := by
      show (if d ^ 2 = 0 then (0 : ℂ) else RHTower.squareIndicator (d ^ 2)) = 1
      rw [if_neg (pow_ne_zero 2 hd1), RHTower.squareIndicator, if_pos ⟨d, sq d⟩]
    rw [sqTwistAF_apply, hsq, one_mul]
    rfl
  · -- `b` is not a square
    have hbpos : b ≠ 0 := by rw [Finset.mem_Icc] at hb; omega
    have hns : ¬ IsSquare b := by
      rintro ⟨r, hr⟩
      apply hb'
      rw [Finset.mem_image]
      refine ⟨r, ?_, by rw [hr]; ring⟩
      rw [Finset.mem_Icc] at hb ⊢
      have hr0 : r ≠ 0 := by rintro rfl; simp at hr; omega
      refine ⟨Nat.one_le_iff_ne_zero.mpr hr0, Nat.le_sqrt.mpr ?_⟩
      rw [← hr]; exact hb.2
    have h0 : RHTower.squareIndicatorAF b = 0 := by
      show (if b = 0 then (0 : ℂ) else RHTower.squareIndicator b) = 0
      rw [if_neg hbpos, RHTower.squareIndicator, if_neg hns]
    rw [sqTwistAF_apply, h0, zero_mul, zero_mul]

/-- `Σ_{d > D} 1/d² ≤ 1/D` for the reciprocal squares. -/
theorem sum_Ioc_inv_sq_le (D M : ℕ) (hD : 1 ≤ D) :
    ∑ d ∈ Finset.Ioc D M, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 1 / D := by
  have hterm : ∀ d ∈ Finset.Ioc D M, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 1 / ((d : ℝ) - 1) - 1 / d := by
    intro d hd
    rw [Finset.mem_Ioc] at hd
    have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast (show 2 ≤ d by omega)
    rw [div_sub_div _ _ (by linarith) (by linarith), div_le_div_iff₀ (by positivity)
      (by nlinarith)]
    nlinarith
  rcases le_or_gt M D with hMD | hDM
  · rw [Finset.Ioc_eq_empty (by omega), sum_empty]; positivity
  · refine le_trans (sum_le_sum hterm) ?_
    -- telescoping
    have htel : ∑ d ∈ Finset.Ioc D M, (1 / ((d : ℝ) - 1) - 1 / d) = 1 / D - 1 / M := by
      have e : Finset.Ioc D M = Finset.Ico (D + 1) (M + 1) := by
        ext d; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
      rw [e, Finset.sum_Ico_eq_sum_range]
      have := Finset.sum_range_sub' (fun k : ℕ => 1 / (((D + k : ℕ) : ℝ))) (M + 1 - (D + 1))
      have e2 : M + 1 - (D + 1) = M - D := by omega
      rw [e2] at this ⊢
      have e3 : ∀ k ∈ Finset.range (M - D),
          1 / (((D + 1 + k : ℕ) : ℝ) - 1) - 1 / ((D + 1 + k : ℕ) : ℝ)
            = 1 / (((D + k : ℕ) : ℝ)) - 1 / (((D + (k + 1) : ℕ) : ℝ)) := by
        intro k _
        push_cast
        congr 1
        · congr 1; ring
        · congr 1; ring
      rw [sum_congr rfl e3, this]
      push_cast
      congr 1
      · simp
      · congr 1; rw [Nat.cast_sub (by omega)]; ring
    rw [htel]
    have : (0 : ℝ) ≤ 1 / M := by positivity
    linarith

theorem norm_d2_cpow_le (τ : ℝ) {d : ℕ} (hd : 0 < d) :
    ‖(((d ^ 2 : ℕ) : ℂ) ^ (-((τ : ℂ) * I)))‖ ≤ 1 := by
  rw [Complex.norm_natCast_cpow_of_pos (by positivity)]
  simp

/-- The trivial bound for a twisted Mertens sum. -/
theorem norm_sum_moebiusTwist_le_card (τ : ℝ) (k : ℕ) :
    ‖∑ m ∈ Finset.Icc 1 k, moebiusTwist τ m‖ ≤ k := by
  calc ‖∑ m ∈ Finset.Icc 1 k, moebiusTwist τ m‖ ≤ ∑ m ∈ Finset.Icc 1 k, ‖moebiusTwist τ m‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _m ∈ Finset.Icc 1 k, (1 : ℝ) := by
        refine sum_le_sum fun m hm => ?_
        have hm0 : 0 < m := by rw [Finset.mem_Icc] at hm; omega
        rw [moebiusTwist, norm_mul, Complex.norm_natCast_cpow_of_pos hm0]
        simp only [neg_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_self, neg_zero, Real.rpow_zero, mul_one]
        rw [Complex.norm_intCast]
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one)
    _ = k := by simp

/-- A twisted Mertens sum of length `N/d²`, `d² ≤ √N`, from the corpus bound. -/
theorem norm_sum_moebiusTwist_div_le {K y₀ : ℝ} (hK : 0 < K)
    (hy₀ : ∀ b : ℝ, y₀ ≤ b → ∀ tau : ℝ, |tau| ≤ b ^ 24 →
      ‖∑ n ∈ Finset.range (⌊b⌋₊ + 1), moebiusTwist tau n‖
        ≤ K * b * Real.exp (-(Real.log b ^ ((1 : ℝ) / 20))))
    {N d : ℕ} (hN16 : (16 : ℝ) ≤ N) (hNy : 2 * y₀ ≤ Real.sqrt N) (hd1 : 1 ≤ d)
    (hd2 : (d : ℝ) ^ 2 ≤ Real.sqrt N) {τ : ℝ} (hτ : 2 * |τ| ≤ Real.sqrt N) :
    ‖∑ m ∈ Finset.Icc 1 (N / d ^ 2), moebiusTwist τ m‖
      ≤ K * Real.exp (-((Real.log N / 4) ^ ((1 : ℝ) / 20))) * (N / (d : ℝ) ^ 2) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hd0 : (0 : ℝ) < (d : ℝ) ^ 2 := pow_pos (by linarith) 2
  set k := N / d ^ 2 with hk
  have hd2pos : 0 < d ^ 2 := pow_pos (by omega) 2
  have hkge : (N : ℝ) / (d : ℝ) ^ 2 - 1 ≤ k := by
    have h1 := Nat.lt_div_mul_add (a := N) hd2pos
    have : (N : ℝ) < (k : ℝ) * (d : ℝ) ^ 2 + (d : ℝ) ^ 2 := by exact_mod_cast h1
    rw [div_sub_one hd0.ne', div_le_iff₀ hd0]
    linarith
  have hkle : (k : ℝ) ≤ N / (d : ℝ) ^ 2 := by
    rw [le_div_iff₀ hd0]
    have : k * d ^ 2 ≤ N := Nat.div_mul_le_self N (d ^ 2)
    exact_mod_cast this
  -- `√N = q²`, `q = N^{1/4} ≥ 2`
  set q := (N : ℝ) ^ ((1 : ℝ) / 4) with hqdef
  have hq0 : 0 < q := Real.rpow_pos_of_pos hN0 _
  have hsqrtN : Real.sqrt N = q ^ 2 := by
    rw [hqdef, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have hq4 : q ^ 4 = N := by
    rw [hqdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have hq2 : 2 ≤ q := by
    by_contra h
    push Not at h
    have : q ^ 4 < 2 ^ 4 := pow_lt_pow_left₀ h hq0.le (by norm_num)
    rw [hq4] at this
    linarith
  have hNd : Real.sqrt N ≤ N / (d : ℝ) ^ 2 := by
    rw [le_div_iff₀ hd0]
    calc Real.sqrt N * (d : ℝ) ^ 2 ≤ Real.sqrt N * Real.sqrt N :=
          mul_le_mul_of_nonneg_left hd2 (Real.sqrt_nonneg _)
      _ = N := Real.mul_self_sqrt hN0.le
  have hk2 : q ^ 2 / 2 ≤ k := by
    have : q ^ 2 / 2 ≤ q ^ 2 - 1 := by nlinarith
    rw [← hsqrtN] at this
    linarith
  have hqk : q ≤ (k : ℝ) := le_trans (by nlinarith) hk2
  have hk1 : (1 : ℝ) ≤ k := by linarith
  -- the corpus bound at `y = k`
  have hky : y₀ ≤ (k : ℝ) := by
    rw [hsqrtN] at hNy
    linarith
  have hτk : |τ| ≤ (k : ℝ) ^ 24 := by
    have h1 : (k : ℝ) ≤ (k : ℝ) ^ 24 := by
      calc (k : ℝ) = (k : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (k : ℝ) ^ 24 := pow_le_pow_right₀ hk1 (by norm_num)
    rw [hsqrtN] at hτ
    linarith
  have hM := hy₀ (k : ℝ) hky τ hτk
  rw [Nat.floor_natCast] at hM
  have hrange : ∑ m ∈ Finset.Icc 1 k, moebiusTwist τ m
      = ∑ m ∈ Finset.range (k + 1), moebiusTwist τ m := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos _), moebiusTwist_zero,
      zero_add, ← Finset.Ico_add_one_right_eq_Icc]
    rfl
  rw [hrange]
  -- `log k ≥ (log N)/4`
  have hlogk : Real.log N / 4 ≤ Real.log k := by
    have h2 := Real.log_le_log hq0 hqk
    rw [hqdef, Real.log_rpow hN0] at h2
    linarith
  have hlogN0 : 0 ≤ Real.log N / 4 := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ N); linarith
  have hexp : Real.exp (-(Real.log k ^ ((1 : ℝ) / 20)))
      ≤ Real.exp (-((Real.log N / 4) ^ ((1 : ℝ) / 20))) :=
    Real.exp_le_exp.mpr (neg_le_neg (Real.rpow_le_rpow hlogN0 hlogk (by norm_num)))
  have h1 : K * k * Real.exp (-(Real.log k ^ ((1 : ℝ) / 20)))
      ≤ K * k * Real.exp (-((Real.log N / 4) ^ ((1 : ℝ) / 20))) :=
    mul_le_mul_of_nonneg_left hexp (by positivity)
  have h2 : K * k * Real.exp (-((Real.log N / 4) ^ ((1 : ℝ) / 20)))
      ≤ K * (N / (d : ℝ) ^ 2) * Real.exp (-((Real.log N / 4) ^ ((1 : ℝ) / 20))) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkle hK.le) (Real.exp_pos _).le
  calc ‖∑ m ∈ Finset.range (k + 1), moebiusTwist τ m‖
      ≤ K * k * Real.exp (-(Real.log k ^ ((1 : ℝ) / 20))) := hM
    _ ≤ K * Real.exp (-((Real.log N / 4) ^ ((1 : ℝ) / 20))) * (N / (d : ℝ) ^ 2) := by linarith

/-- The arithmetic of the `d`-split, in abstract variables. -/
theorem liouville_split_arith {N D S1 S2 E : ℝ} (hN0 : 0 < N) (hD : 1 ≤ D) (hE : 0 ≤ E)
    (hDq : N ^ ((1 : ℝ) / 4) / 2 ≤ D) (hS1 : S1 ≤ 2) (hS2 : S2 ≤ 1 / D) :
    E * N * S1 + N * S2 ≤ 2 * E * N + 4 * N ^ ((3 : ℝ) / 4) := by
  have h1 : E * N * S1 ≤ E * N * 2 := mul_le_mul_of_nonneg_left hS1 (by positivity)
  have hD0 : 0 < D := by linarith
  have h2 : N * S2 ≤ N * (1 / D) := mul_le_mul_of_nonneg_left hS2 hN0.le
  have h3 : N * (1 / D) ≤ 4 * N ^ ((3 : ℝ) / 4) := by
    rw [mul_one_div, div_le_iff₀ hD0]
    have e : N = N ^ ((3 : ℝ) / 4) * N ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_add hN0]; norm_num
    have h34 : 0 ≤ N ^ ((3 : ℝ) / 4) := Real.rpow_nonneg hN0.le _
    have := mul_le_mul_of_nonneg_left hDq (by positivity : (0 : ℝ) ≤ 4 * N ^ ((3 : ℝ) / 4))
    calc N = N ^ ((3 : ℝ) / 4) * N ^ ((1 : ℝ) / 4) := e
      _ = 4 * N ^ ((3 : ℝ) / 4) * (N ^ ((1 : ℝ) / 4) / 2) / 2 := by ring
      _ ≤ 4 * N ^ ((3 : ℝ) / 4) * D / 2 := by linarith
      _ ≤ 4 * N ^ ((3 : ℝ) / 4) * D := by nlinarith
  linarith

/-- **Twisted Liouville partial sums from the twisted Mertens bound.** -/
theorem exists_norm_sum_liouvilleTwist_le :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ τ : ℝ, 2 * |τ| ≤ Real.sqrt N →
      ‖∑ n ∈ Finset.Icc 1 N, (liouville n : ℂ) * (n : ℂ) ^ (-((τ : ℂ) * I))‖
        ≤ 2 * K * N * Real.exp (-((Real.log N / 4) ^ ((1 : ℝ) / 20)))
          + 4 * (N : ℝ) ^ ((3 : ℝ) / 4) := by
  obtain ⟨K, hK, hev⟩ := exists_norm_sum_moebiusTwist_le_rate_pow_twentyFour
  obtain ⟨y₀, hy₀⟩ := eventually_atTop.mp hev
  refine ⟨K, hK, ⌈max (4 * y₀ ^ 2) 16⌉₊, fun N hN τ hτ => ?_⟩
  have hNreal : max (4 * y₀ ^ 2) 16 ≤ (N : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hN)
  have hN16 : (16 : ℝ) ≤ N := le_trans (le_max_right _ _) hNreal
  have hN0 : (0 : ℝ) < N := by linarith
  have hNy : 2 * y₀ ≤ Real.sqrt N := by
    have h1 : (2 * |y₀|) ^ 2 ≤ (N : ℝ) := by
      rw [mul_pow, sq_abs]; linarith [le_max_left (4 * y₀ ^ 2) 16]
    have h2 : Real.sqrt ((2 * |y₀|) ^ 2) ≤ Real.sqrt N := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_sq (by positivity)] at h2
    linarith [le_abs_self y₀]
  rw [sum_liouvilleTwist_eq]
  set q := (N : ℝ) ^ ((1 : ℝ) / 4) with hqdef
  set D := ⌊q⌋₊ with hD
  have hq4 : q ^ 4 = N := by
    rw [hqdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have hq0 : 0 < q := Real.rpow_pos_of_pos hN0 _
  have hq2 : 2 ≤ q := by
    by_contra h
    push Not at h
    have : q ^ 4 < 2 ^ 4 := pow_lt_pow_left₀ h hq0.le (by norm_num)
    rw [hq4] at this
    linarith
  have hD1 : 1 ≤ D := Nat.le_floor (by push_cast; linarith)
  have hD1' : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  have hDle : (D : ℝ) ≤ q := Nat.floor_le hq0.le
  have hDge : q / 2 ≤ D := by
    have := Nat.lt_floor_add_one q
    rw [← hD] at this
    linarith
  have hsqrtN : Real.sqrt N = q ^ 2 := by
    rw [hqdef, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have hDsq : D ≤ Nat.sqrt N := by
    rw [Nat.le_sqrt]
    have : (D : ℝ) * D ≤ N := by
      have h1 : (D : ℝ) * D ≤ q * q := mul_le_mul hDle hDle (Nat.cast_nonneg D) hq0.le
      have h2 : q * q ≤ q ^ 4 := by nlinarith
      linarith
    exact_mod_cast this
  have hsplit : Finset.Icc 1 (Nat.sqrt N) = Finset.Icc 1 D ∪ Finset.Ioc D (Nat.sqrt N) := by
    ext d; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]; omega
  have hdisj : Disjoint (Finset.Icc 1 D) (Finset.Ioc D (Nat.sqrt N)) := by
    rw [Finset.disjoint_left]; intro d h1 h2
    rw [Finset.mem_Icc] at h1; rw [Finset.mem_Ioc] at h2; omega
  rw [hsplit, sum_union hdisj]
  set E := K * Real.exp (-((Real.log N / 4) ^ ((1 : ℝ) / 20))) with hEdef
  have hE0 : 0 ≤ E := by positivity
  have hsmall : ∀ d ∈ Finset.Icc 1 D,
      ‖(((d ^ 2 : ℕ) : ℂ) ^ (-((τ : ℂ) * I))) * ∑ m ∈ Finset.Icc 1 (N / d ^ 2), moebiusTwist τ m‖
        ≤ N * E * ((1 : ℝ) / (d : ℝ) ^ 2) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hdq : (d : ℝ) ≤ q := le_trans (by exact_mod_cast hd.2) hDle
    have hd2 : (d : ℝ) ^ 2 ≤ Real.sqrt N := by
      rw [hsqrtN]; exact pow_le_pow_left₀ (Nat.cast_nonneg d) hdq 2
    have hb := norm_sum_moebiusTwist_div_le hK hy₀ hN16 hNy hd.1 hd2 hτ
    rw [norm_mul]
    calc ‖(((d ^ 2 : ℕ) : ℂ) ^ (-((τ : ℂ) * I)))‖ * ‖∑ m ∈ Finset.Icc 1 (N / d ^ 2), moebiusTwist τ m‖
        ≤ 1 * (E * (N / (d : ℝ) ^ 2)) :=
          mul_le_mul (norm_d2_cpow_le τ (by omega)) hb (norm_nonneg _) zero_le_one
      _ = N * E * ((1 : ℝ) / (d : ℝ) ^ 2) := by ring
  have hlarge : ∀ d ∈ Finset.Ioc D (Nat.sqrt N),
      ‖(((d ^ 2 : ℕ) : ℂ) ^ (-((τ : ℂ) * I))) * ∑ m ∈ Finset.Icc 1 (N / d ^ 2), moebiusTwist τ m‖
        ≤ N * ((1 : ℝ) / (d : ℝ) ^ 2) := by
    intro d hd
    rw [Finset.mem_Ioc] at hd
    have hd0 : 0 < d := lt_of_le_of_lt (Nat.zero_le D) hd.1
    have hdR : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
    rw [norm_mul]
    have hkle : ((N / d ^ 2 : ℕ) : ℝ) ≤ N * ((1 : ℝ) / (d : ℝ) ^ 2) := by
      rw [mul_one_div, le_div_iff₀ hdR]
      have : N / d ^ 2 * d ^ 2 ≤ N := Nat.div_mul_le_self N (d ^ 2)
      exact_mod_cast this
    calc ‖(((d ^ 2 : ℕ) : ℂ) ^ (-((τ : ℂ) * I)))‖ * ‖∑ m ∈ Finset.Icc 1 (N / d ^ 2), moebiusTwist τ m‖
        ≤ 1 * ((N / d ^ 2 : ℕ) : ℝ) :=
          mul_le_mul (norm_d2_cpow_le τ hd0) (norm_sum_moebiusTwist_le_card _ _) (norm_nonneg _)
            zero_le_one
      _ ≤ N * ((1 : ℝ) / (d : ℝ) ^ 2) := by rw [one_mul]; exact hkle
  have hS1 : ∑ d ∈ Finset.Icc 1 D, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 2 := by
    have h := sum_Ioc_inv_sq_le 1 D le_rfl
    have e : Finset.Icc 1 D = insert 1 (Finset.Ioc 1 D) := by
      ext d; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]; omega
    rw [e, sum_insert (by simp)]
    norm_num at h ⊢
    linarith
  have hS2 := sum_Ioc_inv_sq_le D (Nat.sqrt N) hD1
  have hA : ‖∑ d ∈ Finset.Icc 1 D, (((d ^ 2 : ℕ) : ℂ) ^ (-((τ : ℂ) * I)))
      * ∑ m ∈ Finset.Icc 1 (N / d ^ 2), moebiusTwist τ m‖
      ≤ E * N * ∑ d ∈ Finset.Icc 1 D, (1 : ℝ) / (d : ℝ) ^ 2 := by
    refine le_trans (norm_sum_le _ _) (le_trans (sum_le_sum hsmall) (le_of_eq ?_))
    rw [mul_sum]; exact sum_congr rfl fun d _ => by ring
  have hB : ‖∑ d ∈ Finset.Ioc D (Nat.sqrt N), (((d ^ 2 : ℕ) : ℂ) ^ (-((τ : ℂ) * I)))
      * ∑ m ∈ Finset.Icc 1 (N / d ^ 2), moebiusTwist τ m‖
      ≤ N * ∑ d ∈ Finset.Ioc D (Nat.sqrt N), (1 : ℝ) / (d : ℝ) ^ 2 := by
    refine le_trans (norm_sum_le _ _) (le_trans (sum_le_sum hlarge) (le_of_eq ?_))
    rw [mul_sum]
  have hfin := liouville_split_arith hN0 hD1' hE0 hDge hS1 hS2
  refine le_trans (norm_add_le _ _) (le_trans (add_le_add hA hB) ?_)
  rw [hEdef] at hfin
  linarith

end

end GaloisForLFunctions.MatomakiRadziwill
