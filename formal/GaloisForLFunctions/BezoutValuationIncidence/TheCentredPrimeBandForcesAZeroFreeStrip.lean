import GaloisForLFunctions.BezoutValuationIncidence.TheBalancedStatisticIsTheQuasiRiemannHypothesis
import GaloisForLFunctions.BezoutValuationIncidence.ShortWindowPrimeSavingIsTheQuasiRiemannHypothesis

/-!
# A power saving for the balanced prime statistic forces a zero-free strip

The centred prime row `c' = (Λ - 1)𝟙_{(Q,2Q]}` has no inversion law (`Λ ⋆ 1 = log`), so the full-row
value is not explicit. A chain of blocks replaces it. With `d = 2^K X ≤ X^{1+ε}`, the windows
`(2^i X, 2^{i+1} X]`, `i < K`, all lie in the band of `d`, and the near-origin kernel bound turns
their statistics into

`(π²/24) d² Σ_{X < n ≤ d} (Λ(n) - 1)/n²`  up to  `5 d (1 + log d)³`.

So a power saving on the band makes every block `Σ_{X < n ≤ d(X)} (Λ(n) - 1)/n²` of size
`X^{-1-κ}`; chaining `X, d(X), d(d(X)), …` bounds the tail `Σ_{n > X} (Λ(n) - 1)/n² ≪ X^{-1-κ}`,
Abel summation gives `ψ(N) - N ≪ N^{1-κ}`, and the square-sample exponent law gives `Θ ≤ 1 - κ`
(`zetaZeroAbscissa_lt_one_of_centredPrimeBandPowerSaving`).
-/

open Finset Filter Topology ArithmeticFunction RHTower
open ArithmeticFunction (vonMangoldt)
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-- A power saving for the statistic of the centred prime windows on a neighbourhood
`Q^{1-ε} ≤ d ≤ Q^{1+ε}` of the diagonal. -/
def CentredPrimeBandPowerSaving : Prop :=
  ∃ ε η C : ℝ, 0 < ε ∧ 0 < η ∧ ∀ Q d : ℕ, 2 ≤ Q → (Q : ℝ) ^ (1 - ε) ≤ d →
    (d : ℝ) ≤ (Q : ℝ) ^ (1 + ε) →
      |kernelStatisticAll (2 * Q) (centredPrimeBlock Q) d| ≤ C * ((d : ℝ) ^ 2 / Q) * (Q : ℝ) ^ (-η)

/-- The terms `(Λ(n) - 1)/n²` (zero at `n = 0`). -/
def primeSqTerm (n : ℕ) : ℝ := (vonMangoldt n - 1) / (n : ℝ) ^ 2

/-- `S(X) = Σ_{n ≤ X} (Λ(n) - 1)/n²`. -/
def primeSqSum (X : ℕ) : ℝ := ∑ n ∈ Ioc 0 X, primeSqTerm n

/-! ## §1. Windows, summability, Abel summation -/

/-- A prime window statistic is the sum of `(Λ - 1) ℓ_d` over the window. -/
theorem kernelStatisticAll_centredPrimeBlock_eq (d Q : ℕ) :
    kernelStatisticAll (2 * Q) (centredPrimeBlock Q) d =
      ∑ n ∈ Ioc Q (2 * Q), (vonMangoldt n - 1) * kernelTerm d n := by
  rw [kernelStatisticAll_eq_sum_kernelTerm]
  have e : ∀ n ∈ Icc 1 (2 * Q), centredPrimeBlock Q n * kernelTerm d n =
      if Q < n ∧ n ≤ 2 * Q then (vonMangoldt n - 1) * kernelTerm d n else 0 := fun n _ => by
    unfold centredPrimeBlock
    split_ifs <;> simp
  rw [sum_congr rfl e, ← sum_filter]
  refine sum_congr ?_ fun _ _ => rfl
  ext n
  simp only [mem_filter, mem_Icc, mem_Ioc]
  omega

/-- `|Λ(n) - 1| ≤ 1 + log n` for `n ≥ 1`. -/
theorem abs_vonMangoldt_sub_one_le_self {n : ℕ} (hn : 1 ≤ n) :
    |vonMangoldt n - 1| ≤ 1 + Real.log n := by
  have := abs_vonMangoldt_sub_one_le hn le_rfl
  linarith

theorem summable_primeSqTerm : Summable primeSqTerm := by
  have hs : Summable (fun n : ℕ => 3 * ((n : ℝ) ^ (-(3 / 2 : ℝ)))) :=
    (Real.summable_nat_rpow.mpr (by norm_num)).mul_left 3
  refine Summable.of_norm_bounded hs fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [primeSqTerm]
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  rw [Real.norm_eq_abs, primeSqTerm, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)]
  have h1 := abs_vonMangoldt_sub_one_le_self hn
  have hlog : Real.log n ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
    have := Real.log_le_rpow_div hn0.le (by norm_num : (0 : ℝ) < 1 / 2)
    linarith
  have hsq : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := Real.one_le_rpow hnR (by norm_num)
  have e : 3 * (n : ℝ) ^ (-(3 / 2 : ℝ)) = 3 * (n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ 2 := by
    rw [show (-(3 / 2 : ℝ)) = 1 / 2 - 2 by norm_num, Real.rpow_sub hn0, Real.rpow_two]; ring
  rw [e]
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- `Σ_{n ≤ N} (Λ(n) - 1) = Σ_{n ≤ N} n² (Λ(n) - 1)/n²`. -/
theorem psiRemainder_eq_sum_sq_mul (N : ℕ) :
    psiRemainder N = ∑ n ∈ Ioc 0 N, (n : ℝ) ^ 2 * primeSqTerm n := by
  have h := sum_Ioc_vonMangoldt_sub_eq 0 N
  rw [zero_add] at h
  have h0 : psiRemainder 0 = 0 := by simp [psiRemainder, chebyshevPsi]
  rw [h0, sub_zero] at h
  rw [← h, show (N : ℝ) = ∑ _n ∈ Ioc 0 N, (1 : ℝ) by simp, ← sum_sub_distrib]
  refine sum_congr rfl fun n hn => ?_
  have hn0 : (n : ℝ) ≠ 0 := by have := (mem_Ioc.mp hn).1; exact_mod_cast this.ne'
  unfold primeSqTerm
  field_simp

/-- **Abel summation, generic form.** With `D(n) = Σ_{m ≤ n} a(m) - c`,
`Σ_{n ≤ N} n² a(n) = N² D(N) - Σ_{n<N} (2n + 1) D(n)`. -/
theorem sum_Ioc_sq_mul_eq_abel (a : ℕ → ℝ) (c : ℝ) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (n : ℝ) ^ 2 * a n = (N : ℝ) ^ 2 * (∑ m ∈ Ioc 0 N, a m - c) -
      ∑ n ∈ range N, (2 * (n : ℝ) + 1) * (∑ m ∈ Ioc 0 n, a m - c) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Ioc_succ_top (Nat.zero_le N), ih, sum_Ioc_succ_top (Nat.zero_le N),
      Finset.sum_range_succ]
    push_cast
    ring

/-- **Abel summation bound.** If `|Σ_{m ≤ n} a(m) - c| ≤ C n^{-1-κ}` for `n ≥ 1`, `0 < κ < 1`, then
`|Σ_{n ≤ N} n² a(n)| ≤ (C + |c| + 3C/(1 - κ)) (N + 1)^{1-κ}`. -/
theorem abs_sum_Ioc_sq_mul_le {a : ℕ → ℝ} {c C κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) (hC : 0 ≤ C)
    (hD : ∀ n : ℕ, 1 ≤ n → |∑ m ∈ Ioc 0 n, a m - c| ≤ C * (n : ℝ) ^ (-1 - κ)) (N : ℕ) :
    |∑ n ∈ Ioc 0 N, (n : ℝ) ^ 2 * a n| ≤ (C + |c| + 3 * C / (1 - κ)) * ((N : ℝ) + 1) ^ (1 - κ) := by
  have h1κ : 0 < 1 - κ := by linarith
  have hX1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hpow1 : 1 ≤ ((N : ℝ) + 1) ^ (1 - κ) := Real.one_le_rpow hX1 h1κ.le
  rw [sum_Ioc_sq_mul_eq_abel a c]
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · simp; positivity
  have hT1 : |(N : ℝ) ^ 2 * (∑ m ∈ Ioc 0 N, a m - c)| ≤ C * ((N : ℝ) + 1) ^ (1 - κ) := by
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc (N : ℝ) ^ 2 * |∑ m ∈ Ioc 0 N, a m - c| ≤ (N : ℝ) ^ 2 * (C * (N : ℝ) ^ (-1 - κ)) :=
          mul_le_mul_of_nonneg_left (hD N hNpos) (by positivity)
      _ = C * (N : ℝ) ^ (1 - κ) := by
          rw [mul_left_comm, ← Real.rpow_natCast (N : ℝ) 2, ← Real.rpow_add (by linarith)]
          congr 2; push_cast; ring
      _ ≤ C * ((N : ℝ) + 1) ^ (1 - κ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) (by linarith) h1κ.le) hC
  have hT2 : |∑ n ∈ range N, (2 * (n : ℝ) + 1) * (∑ m ∈ Ioc 0 n, a m - c)| ≤
      |c| + 3 * C / (1 - κ) * ((N : ℝ) + 1) ^ (1 - κ) := by
    rw [range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hNpos]
    have h0 : |(2 * ((0 : ℕ) : ℝ) + 1) * (∑ m ∈ Ioc 0 0, a m - c)| ≤ |c| := by simp
    have hterm : ∀ n ∈ Ico (0 + 1) N, |(2 * (n : ℝ) + 1) * (∑ m ∈ Ioc 0 n, a m - c)| ≤
        3 * C * (((n - 1 : ℕ) : ℝ) + 1) ^ (-κ) := by
      intro n hn
      have hn1 : 1 ≤ n := (mem_Ico.mp hn).1
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have hcast : (((n - 1 : ℕ) : ℝ) + 1) = n := by rw [Nat.cast_sub hn1]; push_cast; ring
      rw [hcast, abs_mul, abs_of_pos (by positivity)]
      calc (2 * (n : ℝ) + 1) * |∑ m ∈ Ioc 0 n, a m - c| ≤ (3 * (n : ℝ)) * (C * (n : ℝ) ^ (-1 - κ)) :=
            mul_le_mul (by linarith) (hD n hn1) (abs_nonneg _) (by positivity)
        _ = 3 * C * (n : ℝ) ^ (-κ) := by
            rw [show (-1 - κ : ℝ) = -1 + -κ by ring, Real.rpow_add (by linarith), Real.rpow_neg_one]
            field_simp
    have hsum : ∑ n ∈ Ico (0 + 1) N, 3 * C * (((n - 1 : ℕ) : ℝ) + 1) ^ (-κ) ≤
        3 * C / (1 - κ) * ((N : ℝ) + 1) ^ (1 - κ) := by
      rw [← mul_sum, Finset.sum_Ico_eq_sum_range]
      simp only [zero_add, Nat.add_sub_cancel_left]
      have h := RHTower.sum_range_rpow_neg_le κ hκ0 hκ1 (N - 1)
      calc 3 * C * ∑ k ∈ range (N - 1), ((k : ℝ) + 1) ^ (-κ)
          ≤ 3 * C * (((N - 1 : ℕ) : ℝ) ^ (1 - κ) / (1 - κ)) :=
            mul_le_mul_of_nonneg_left h (by positivity)
        _ ≤ 3 * C * (((N : ℝ) + 1) ^ (1 - κ) / (1 - κ)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            refine div_le_div_of_nonneg_right ?_ h1κ.le
            refine Real.rpow_le_rpow (Nat.cast_nonneg _) ?_ h1κ.le
            have : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
            linarith
        _ = 3 * C / (1 - κ) * ((N : ℝ) + 1) ^ (1 - κ) := by ring
    calc |(2 * ((0 : ℕ) : ℝ) + 1) * (∑ m ∈ Ioc 0 0, a m - c) +
          ∑ n ∈ Ico (0 + 1) N, (2 * (n : ℝ) + 1) * (∑ m ∈ Ioc 0 n, a m - c)|
        ≤ |c| + ∑ n ∈ Ico (0 + 1) N, 3 * C * (((n - 1 : ℕ) : ℝ) + 1) ^ (-κ) :=
          (abs_add_le _ _).trans (add_le_add h0 ((abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)))
      _ ≤ _ := by linarith
  calc |(N : ℝ) ^ 2 * (∑ m ∈ Ioc 0 N, a m - c) -
        ∑ n ∈ range N, (2 * (n : ℝ) + 1) * (∑ m ∈ Ioc 0 n, a m - c)|
      ≤ C * ((N : ℝ) + 1) ^ (1 - κ) + (|c| + 3 * C / (1 - κ) * ((N : ℝ) + 1) ^ (1 - κ)) :=
        (abs_sub _ _).trans (add_le_add hT1 hT2)
    _ ≤ (C + |c| + 3 * C / (1 - κ)) * ((N : ℝ) + 1) ^ (1 - κ) := by
        have := abs_nonneg c
        nlinarith

/-- **A power bound on `ψ(N) - N` is a zero-free strip**, through the square-sample exponent law. -/
theorem zetaZeroAbscissa_le_of_psiRemainder_le {K c : ℝ} (hK : 0 ≤ K) (hc : 1 / 2 ≤ c)
    (hR : ∀ N : ℕ, 1 ≤ N → |psiRemainder N| ≤ K * (N : ℝ) ^ c) : zetaZeroAbscissa ≤ c := by
  have hmem : c - 1 / 2 ∈ psiRemainderSquareSumUpperExponentSet := by
    refine ⟨sub_nonneg.mpr hc, K, hK, fun N hN => ?_⟩
    have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hN0 : (0 : ℝ) < N := by linarith
    have hN2 : ((N ^ 2 : ℕ) : ℝ) = (N : ℝ) ^ 2 := by push_cast; ring
    have hsum : ∑ s ∈ Ico 1 N, psiRemainder (s ^ 2) ≤ N * (K * ((N ^ 2 : ℕ) : ℝ) ^ c) := by
      calc ∑ s ∈ Ico 1 N, psiRemainder (s ^ 2) ≤ ∑ s ∈ Ico 1 N, |psiRemainder (s ^ 2)| :=
            sum_le_sum fun s _ => le_abs_self _
        _ ≤ ∑ _s ∈ Ico 1 N, K * ((N ^ 2 : ℕ) : ℝ) ^ c := by
            refine sum_le_sum fun s hs => ?_
            have hs' := mem_Ico.mp hs
            refine (hR (s ^ 2) (Nat.one_le_pow _ _ hs'.1)).trans ?_
            refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) ?_
              (by linarith)) hK
            exact_mod_cast Nat.pow_le_pow_left hs'.2.le 2
        _ = ((N - 1 : ℕ) : ℝ) * (K * ((N ^ 2 : ℕ) : ℝ) ^ c) := by
            rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
        _ ≤ N * (K * ((N ^ 2 : ℕ) : ℝ) ^ c) := by
            gcongr
            exact_mod_cast Nat.sub_le N 1
    rw [div_le_iff₀ (by positivity)]
    refine hsum.trans (le_of_eq ?_)
    rw [hN2, Real.rpow_sub (by positivity), show ((N : ℝ) ^ 2) ^ (1 / 2 : ℝ) = N by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hN0.le]]
    field_simp
  have hbdd : BddBelow psiRemainderSquareSumUpperExponentSet := ⟨0, fun _ hc => hc.1⟩
  have := csInf_le hbdd hmem
  rw [zetaZeroAbscissa_eq_half_add_sInf_psiRemainder_squareSum_upper]
  linarith

/-! ## §2. One block inside the band -/

/-- **One block.** If `2^K ≤ X^ε` then every window `(2^i X, 2^{i+1} X]`, `i < K`, lies in the band
of `d = 2^K X`, and
`(π²/24) d² |Σ_{X < n ≤ d} (Λ(n) - 1)/n²| ≤ 4 C d² X^{-(1+η)} + 5 d (1 + log d)³`. -/
theorem abs_primeBlock_le {ε η C : ℝ} (hε : 0 < ε) (hη : 0 < η) (hC : 0 ≤ C)
    (hband : ∀ Q d : ℕ, 2 ≤ Q → (Q : ℝ) ^ (1 - ε) ≤ d → (d : ℝ) ≤ (Q : ℝ) ^ (1 + ε) →
      |kernelStatisticAll (2 * Q) (centredPrimeBlock Q) d| ≤ C * ((d : ℝ) ^ 2 / Q) * (Q : ℝ) ^ (-η))
    {X K : ℕ} (hX : 2 ≤ X) (hK : (2 : ℝ) ^ K ≤ (X : ℝ) ^ ε) :
    Real.pi ^ 2 / 24 * ((2 ^ K * X : ℕ) : ℝ) ^ 2 * |∑ n ∈ Ioc X (2 ^ K * X), primeSqTerm n| ≤
      4 * C * ((2 ^ K * X : ℕ) : ℝ) ^ 2 * (X : ℝ) ^ (-(1 + η)) +
        5 * ((2 ^ K * X : ℕ) : ℝ) * (1 + Real.log ((2 ^ K * X : ℕ) : ℝ)) ^ 3 := by
  set d := 2 ^ K * X with hddef
  have hXR : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hXd : X ≤ d := Nat.le_mul_of_pos_left _ (by positivity)
  have hdR : (1 : ℝ) ≤ d := by have : (X : ℝ) ≤ d := by exact_mod_cast hXd
                               linarith
  have hd0 : 0 < d := by omega
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg hdR
  set F : ℕ → ℝ := fun n => (vonMangoldt n - 1) * kernelTerm d n
  -- the block is the sum of `K` windows, each in the band
  have hwin : ∑ n ∈ Ioc X d, F n = ∑ i ∈ range K,
      kernelStatisticAll (2 * (2 ^ i * X)) (centredPrimeBlock (2 ^ i * X)) d := by
    have h := sum_Ioc_two_pow_mul_eq F X K
    rw [← sum_Ioc_consecutive F (Nat.zero_le X) hXd] at h
    rw [add_left_cancel h]
    exact sum_congr rfl fun i _ => (kernelStatisticAll_centredPrimeBlock_eq d _).symm
  have hdX : (d : ℝ) ≤ (X : ℝ) ^ (1 + ε) := by
    rw [hddef, Real.rpow_add hX0, Real.rpow_one]; push_cast
    nlinarith [Real.rpow_nonneg hX0.le ε]
  have hWsum : |∑ n ∈ Ioc X d, F n| ≤ 4 * C * (d : ℝ) ^ 2 * (X : ℝ) ^ (-(1 + η)) := by
    rw [hwin]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ i ∈ range K,
        |kernelStatisticAll (2 * (2 ^ i * X)) (centredPrimeBlock (2 ^ i * X)) d| ≤
          C * (d : ℝ) ^ 2 * ((2 ^ i * X : ℕ) : ℝ) ^ (-(1 + η)) := by
      intro i hi
      have hQX : X ≤ 2 ^ i * X := Nat.le_mul_of_pos_left _ (by positivity)
      have hQd : 2 ^ i * X ≤ d := by
        rw [hddef]
        exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (mem_range.mp hi).le)
      have hQ1 : (1 : ℝ) ≤ ((2 ^ i * X : ℕ) : ℝ) := by
        have : (X : ℝ) ≤ ((2 ^ i * X : ℕ) : ℝ) := by exact_mod_cast hQX
        linarith
      have hQ0 : (0 : ℝ) < ((2 ^ i * X : ℕ) : ℝ) := by linarith
      have hlo : ((2 ^ i * X : ℕ) : ℝ) ^ (1 - ε) ≤ d := by
        calc ((2 ^ i * X : ℕ) : ℝ) ^ (1 - ε) ≤ ((2 ^ i * X : ℕ) : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
          _ = ((2 ^ i * X : ℕ) : ℝ) := Real.rpow_one _
          _ ≤ d := by exact_mod_cast hQd
      have hhi : (d : ℝ) ≤ ((2 ^ i * X : ℕ) : ℝ) ^ (1 + ε) :=
        hdX.trans (Real.rpow_le_rpow hX0.le (by exact_mod_cast hQX) (by linarith))
      refine (hband _ d (hX.trans hQX) hlo hhi).trans (le_of_eq ?_)
      rw [show (-(1 + η) : ℝ) = -1 + -η by ring, Real.rpow_add hQ0, Real.rpow_neg_one]
      field_simp
    refine (sum_le_sum hterm).trans ?_
    rw [← mul_sum]
    have h4 := sum_range_two_pow_mul_rpow_neg_le (a := 1 + η) (by linarith) (by omega : 1 ≤ X) K
    calc C * (d : ℝ) ^ 2 * ∑ i ∈ range K, ((2 ^ i * X : ℕ) : ℝ) ^ (-(1 + η))
        ≤ C * (d : ℝ) ^ 2 * (4 * (X : ℝ) ^ (-(1 + η))) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = 4 * C * (d : ℝ) ^ 2 * (X : ℝ) ^ (-(1 + η)) := by ring
  -- the near-origin kernel bound on the block
  have hnear : |∑ n ∈ Ioc X d, (F n - Real.pi ^ 2 / 24 * (d : ℝ) ^ 2 * primeSqTerm n)| ≤
      5 * (d : ℝ) * (1 + Real.log d) ^ 3 := by
    have hterm : ∀ n ∈ Ioc X d, |F n - Real.pi ^ 2 / 24 * (d : ℝ) ^ 2 * primeSqTerm n| ≤
        5 * (d : ℝ) * (1 + Real.log d) * (1 + Real.log d) * (1 / (n : ℝ)) := by
      intro n hn
      obtain ⟨hXn, hnd⟩ := mem_Ioc.mp hn
      have hn1 : 1 ≤ n := by omega
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have hn0 : (0 : ℝ) < n := by linarith
      have hb := abs_sq_mul_kernelTerm_sub_le hd0 hn1
      have hl := abs_vonMangoldt_sub_one_le_self hn1
      have hlogn : Real.log n ≤ Real.log d := Real.log_le_log hn0 (by exact_mod_cast hnd)
      have e : F n - Real.pi ^ 2 / 24 * (d : ℝ) ^ 2 * primeSqTerm n =
          (vonMangoldt n - 1) * (((n : ℝ) ^ 2 * kernelTerm d n - Real.pi ^ 2 / 24 * (d : ℝ) ^ 2) /
            (n : ℝ) ^ 2) := by
        simp only [F, primeSqTerm]; field_simp
      rw [e, abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)]
      calc |vonMangoldt n - 1| * (|(n : ℝ) ^ 2 * kernelTerm d n - Real.pi ^ 2 / 24 * (d : ℝ) ^ 2| /
            (n : ℝ) ^ 2)
          ≤ (1 + Real.log d) * (5 * (n : ℝ) * d * (1 + Real.log d) / (n : ℝ) ^ 2) :=
            mul_le_mul (by linarith) (div_le_div_of_nonneg_right hb (by positivity))
              (by positivity) (by linarith)
        _ = 5 * (d : ℝ) * (1 + Real.log d) * (1 + Real.log d) * (1 / (n : ℝ)) := by
            field_simp
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hterm).trans ?_)
    rw [← mul_sum]
    have hsub : ∑ n ∈ Ioc X d, 1 / (n : ℝ) ≤ ∑ n ∈ Ioc 0 d, 1 / (n : ℝ) :=
      sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_left (Nat.zero_le X))
        fun _ _ _ => by positivity
    have hharm : ∑ n ∈ Ioc 0 d, 1 / (n : ℝ) ≤ 1 + Real.log d := by
      rw [sum_Ioc_eq_sum_range_succ]; exact sum_range_one_div_succ_le hd0
    calc 5 * (d : ℝ) * (1 + Real.log d) * (1 + Real.log d) * ∑ n ∈ Ioc X d, 1 / (n : ℝ)
        ≤ 5 * (d : ℝ) * (1 + Real.log d) * (1 + Real.log d) * (1 + Real.log d) :=
          mul_le_mul_of_nonneg_left (hsub.trans hharm) (by positivity)
      _ = 5 * (d : ℝ) * (1 + Real.log d) ^ 3 := by ring
  have e : Real.pi ^ 2 / 24 * (d : ℝ) ^ 2 * ∑ n ∈ Ioc X d, primeSqTerm n =
      ∑ n ∈ Ioc X d, F n - ∑ n ∈ Ioc X d, (F n - Real.pi ^ 2 / 24 * (d : ℝ) ^ 2 * primeSqTerm n) := by
    rw [mul_sum, ← sum_sub_distrib]; exact sum_congr rfl fun n _ => by ring
  rw [← abs_of_pos (by positivity : (0 : ℝ) < Real.pi ^ 2 / 24 * (d : ℝ) ^ 2), ← abs_mul, e]
  exact (abs_sub _ _).trans (add_le_add hWsum hnear)

/-! ## §3. The chain of blocks and the strip -/

/-- The block step `X ↦ 2^{K(X)} X` with `K(X) = log₂ ⌊X^e⌋`. -/
def primeBlockStep (e : ℝ) (X : ℕ) : ℕ := 2 ^ Nat.log 2 ⌊(X : ℝ) ^ e⌋₊ * X

/-- `X^e/2 < 2^{K(X)} ≤ X^e` for `X ≥ 1`, `e ≥ 0`. -/
theorem two_pow_log_floor_bounds {e : ℝ} (he : 0 ≤ e) {X : ℕ} (hX : 1 ≤ X) :
    (2 : ℝ) ^ Nat.log 2 ⌊(X : ℝ) ^ e⌋₊ ≤ (X : ℝ) ^ e ∧
      (X : ℝ) ^ e / 2 < (2 : ℝ) ^ Nat.log 2 ⌊(X : ℝ) ^ e⌋₊ := by
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hXe : (1 : ℝ) ≤ (X : ℝ) ^ e := Real.one_le_rpow hX1 he
  have hfl : ⌊(X : ℝ) ^ e⌋₊ ≠ 0 := by
    have : 1 ≤ ⌊(X : ℝ) ^ e⌋₊ := Nat.le_floor (by exact_mod_cast hXe)
    omega
  constructor
  · have h1 : 2 ^ Nat.log 2 ⌊(X : ℝ) ^ e⌋₊ ≤ ⌊(X : ℝ) ^ e⌋₊ := Nat.pow_log_le_self 2 hfl
    have h1R : ((2 ^ Nat.log 2 ⌊(X : ℝ) ^ e⌋₊ : ℕ) : ℝ) ≤ (⌊(X : ℝ) ^ e⌋₊ : ℝ) := by exact_mod_cast h1
    push_cast at h1R
    exact h1R.trans (Nat.floor_le (by positivity))
  · have h2 : ⌊(X : ℝ) ^ e⌋₊ < 2 ^ (Nat.log 2 ⌊(X : ℝ) ^ e⌋₊).succ :=
      Nat.lt_pow_succ_log_self (by norm_num) _
    have h2R : (⌊(X : ℝ) ^ e⌋₊ : ℝ) + 1 ≤ ((2 ^ (Nat.log 2 ⌊(X : ℝ) ^ e⌋₊).succ : ℕ) : ℝ) := by
      exact_mod_cast h2
    have h3 := Nat.lt_floor_add_one ((X : ℝ) ^ e)
    push_cast at h2R
    rw [pow_succ] at h2R
    linarith

/-- For `X ≥ 2^{1/e}`, the block step at least doubles. -/
theorem two_mul_le_primeBlockStep {e : ℝ} (he : 0 < e) {X : ℕ} (hX : (2 : ℝ) ^ (1 / e) ≤ X) :
    2 * X ≤ primeBlockStep e X := by
  have hX1 : (1 : ℝ) ≤ X := le_trans (Real.one_le_rpow (by norm_num) (by positivity)) hX
  have hXe : (2 : ℝ) ≤ (X : ℝ) ^ e := by
    calc (2 : ℝ) = ((2 : ℝ) ^ (1 / e)) ^ e := by
          rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel he.ne', Real.rpow_one]
      _ ≤ (X : ℝ) ^ e := Real.rpow_le_rpow (by positivity) hX he.le
  have h2 : 2 ≤ ⌊(X : ℝ) ^ e⌋₊ := Nat.le_floor (by exact_mod_cast hXe)
  have hK : 1 ≤ Nat.log 2 ⌊(X : ℝ) ^ e⌋₊ := Nat.log_pos (by norm_num) h2
  unfold primeBlockStep
  calc 2 * X = 2 ^ 1 * X := by ring
    _ ≤ 2 ^ Nat.log 2 ⌊(X : ℝ) ^ e⌋₊ * X :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hK)

/-- `X ≥ 2^{1/e}` gives `X^e ≥ 2`. -/
theorem two_le_rpow_of_le {e : ℝ} (he : 0 < e) {X : ℝ} (hX : (2 : ℝ) ^ (1 / e) ≤ X) :
    (2 : ℝ) ≤ X ^ e := by
  calc (2 : ℝ) = ((2 : ℝ) ^ (1 / e)) ^ e := by
        rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel he.ne', Real.rpow_one]
    _ ≤ X ^ e := Real.rpow_le_rpow (by positivity) hX he.le

/-- **One block step, power form.** With the band at width `e ≤ 1/2` and `X^e ≥ 2`,
`|Σ_{X < n ≤ 2^{K(X)} X} (Λ(n) - 1)/n²| ≤ (24/π²)(4C + 80(1 + 6/e)³) X^{-1-min(η, e/2)}`. -/
theorem abs_primeBlockStep_le {e η C : ℝ} (he : 0 < e) (he1 : e ≤ 1 / 2) (hη : 0 < η) (hC : 0 ≤ C)
    (hband : ∀ Q d : ℕ, 2 ≤ Q → (Q : ℝ) ^ (1 - e) ≤ d → (d : ℝ) ≤ (Q : ℝ) ^ (1 + e) →
      |kernelStatisticAll (2 * Q) (centredPrimeBlock Q) d| ≤ C * ((d : ℝ) ^ 2 / Q) * (Q : ℝ) ^ (-η))
    {X : ℕ} (hX2 : 2 ≤ X) (hXe : (2 : ℝ) ≤ (X : ℝ) ^ e) :
    |∑ n ∈ Ioc X (primeBlockStep e X), primeSqTerm n| ≤
      24 / Real.pi ^ 2 * (4 * C + 80 * (1 + 6 / e) ^ 3) * (X : ℝ) ^ (-1 - min η (e / 2)) := by
  set κ := min η (e / 2) with hκdef
  have hκη : κ ≤ η := min_le_left _ _
  have hκe : κ ≤ e / 2 := min_le_right _ _
  have hXR : (2 : ℝ) ≤ X := by exact_mod_cast hX2
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hX0 : (0 : ℝ) < X := by linarith
  obtain ⟨hKu, hKl⟩ := two_pow_log_floor_bounds he.le (by omega : 1 ≤ X)
  set K := Nat.log 2 ⌊(X : ℝ) ^ e⌋₊ with hKdef
  have hb := abs_primeBlock_le he hη hC hband (X := X) (K := K) hX2 hKu
  have hstep : primeBlockStep e X = 2 ^ K * X := rfl
  rw [hstep]
  set D : ℝ := ((2 ^ K * X : ℕ) : ℝ) with hDdef
  have hDeq : D = (2 : ℝ) ^ K * X := by rw [hDdef]; push_cast; ring
  have hXe0 : (0 : ℝ) < (X : ℝ) ^ e := by positivity
  have hDlo : (X : ℝ) ^ (1 + e) / 2 ≤ D := by
    rw [hDeq, Real.rpow_add hX0, Real.rpow_one]; nlinarith
  have hDhi : D ≤ (X : ℝ) ^ (1 + e) := by
    rw [hDeq, Real.rpow_add hX0, Real.rpow_one]; nlinarith
  have hD0 : 0 < D := lt_of_lt_of_le (by positivity) hDlo
  -- divide by `(π²/24) D²`
  have hpi : (0 : ℝ) < Real.pi ^ 2 / 24 * D ^ 2 := by positivity
  have hmain : |∑ n ∈ Ioc X (2 ^ K * X), primeSqTerm n| ≤
      24 / Real.pi ^ 2 * (4 * C * (X : ℝ) ^ (-(1 + η)) + 5 * (1 + Real.log D) ^ 3 * (1 / D)) := by
    rw [← mul_le_mul_iff_of_pos_left hpi]
    refine hb.trans (le_of_eq ?_)
    field_simp
  refine hmain.trans ?_
  -- the logarithmic layer
  have hlogD : 1 + Real.log D ≤ 2 * (1 + Real.log X) := by
    have h := Real.log_le_log hD0 hDhi
    rw [Real.log_rpow hX0] at h
    have := Real.log_nonneg hX1
    nlinarith
  have hlogX : (1 + Real.log X) ^ 3 ≤ (1 + 6 / e) ^ 3 * (X : ℝ) ^ (e / 2) := by
    have h := one_add_log_le_rpow hX1 (by positivity : 0 < e / 6)
    rw [show 1 / (e / 6) = 6 / e by field_simp] at h
    have h0 : 0 ≤ 1 + Real.log X := by have := Real.log_nonneg hX1; linarith
    calc (1 + Real.log X) ^ 3 ≤ ((1 + 6 / e) * (X : ℝ) ^ (e / 6)) ^ 3 := pow_le_pow_left₀ h0 h 3
      _ = (1 + 6 / e) ^ 3 * (X : ℝ) ^ (e / 2) := by
          rw [mul_pow, ← Real.rpow_natCast ((X : ℝ) ^ (e / 6)) 3, ← Real.rpow_mul hX0.le]
          congr 2; push_cast; ring
  have hinvD : 1 / D ≤ 2 * (X : ℝ) ^ (-1 - e) := by
    calc 1 / D ≤ 1 / ((X : ℝ) ^ (1 + e) / 2) := one_div_le_one_div_of_le (by positivity) hDlo
      _ = 2 * (X : ℝ) ^ (-1 - e) := by
          rw [show (-1 - e : ℝ) = -(1 + e) by ring, Real.rpow_neg hX0.le]; field_simp
  have hlog0 : 0 ≤ 1 + Real.log D := by have := Real.log_nonneg (show (1:ℝ) ≤ D by
    nlinarith [Real.one_le_rpow hX1 (by linarith : (0 : ℝ) ≤ 1 + e)]); linarith
  have t2 : 5 * (1 + Real.log D) ^ 3 * (1 / D) ≤ 80 * (1 + 6 / e) ^ 3 * (X : ℝ) ^ (-1 - κ) := by
    calc 5 * (1 + Real.log D) ^ 3 * (1 / D) ≤ 5 * (2 * (1 + Real.log X)) ^ 3 * (2 * (X : ℝ) ^ (-1 - e)) := by
          gcongr
      _ = 80 * (1 + Real.log X) ^ 3 * (X : ℝ) ^ (-1 - e) := by ring
      _ ≤ 80 * ((1 + 6 / e) ^ 3 * (X : ℝ) ^ (e / 2)) * (X : ℝ) ^ (-1 - e) := by gcongr
      _ = 80 * (1 + 6 / e) ^ 3 * (X : ℝ) ^ (-1 - e / 2) := by
          rw [mul_assoc, mul_assoc, ← Real.rpow_add hX0]; ring_nf
      _ ≤ 80 * (1 + 6 / e) ^ 3 * (X : ℝ) ^ (-1 - κ) := by
          gcongr
  have t1 : 4 * C * (X : ℝ) ^ (-(1 + η)) ≤ 4 * C * (X : ℝ) ^ (-1 - κ) :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)) (by positivity)
  have hpi0 : 0 ≤ 24 / Real.pi ^ 2 := by positivity
  calc 24 / Real.pi ^ 2 * (4 * C * (X : ℝ) ^ (-(1 + η)) + 5 * (1 + Real.log D) ^ 3 * (1 / D))
      ≤ 24 / Real.pi ^ 2 * (4 * C * (X : ℝ) ^ (-1 - κ) + 80 * (1 + 6 / e) ^ 3 * (X : ℝ) ^ (-1 - κ)) :=
        mul_le_mul_of_nonneg_left (add_le_add t1 t2) hpi0
    _ = _ := by ring

/-- **The chain of blocks bounds the tail.** If every block `(X, f X]` from `X ≥ X₀` has
`|Σ a| ≤ K₁ X^{-1-κ}`, `f X ≥ 2X`, and `Σ a = c`, then `|S(X) - c| ≤ 2K₁ X^{-1-κ}` for `X ≥ X₀`. -/
theorem abs_sum_Ioc_sub_tsum_le_of_blocks {a : ℕ → ℝ} {c K₁ κ : ℝ} (ha0 : a 0 = 0)
    (hc : HasSum a c) (hK₁ : 0 ≤ K₁) (hκ : 0 ≤ κ) {f : ℕ → ℕ} {X₀ : ℕ} (hX₀ : 1 ≤ X₀)
    (hstep : ∀ X, X₀ ≤ X → 2 * X ≤ f X)
    (hblock : ∀ X, X₀ ≤ X → |∑ n ∈ Ioc X (f X), a n| ≤ K₁ * (X : ℝ) ^ (-1 - κ))
    {X : ℕ} (hX : X₀ ≤ X) :
    |∑ n ∈ Ioc 0 X, a n - c| ≤ 2 * K₁ * (X : ℝ) ^ (-1 - κ) := by
  set Xs : ℕ → ℕ := fun j => f^[j] X with hXs
  have hgrow : ∀ j, X₀ ≤ Xs j ∧ 2 ^ j * X ≤ Xs j := by
    intro j
    induction j with
    | zero => simp [hXs, hX]
    | succ j ih =>
      have h2 := hstep _ ih.1
      have e : Xs (j + 1) = f (Xs j) := by
        simp only [hXs]; rw [Function.iterate_succ_apply']
      rw [e]
      refine ⟨by omega, ?_⟩
      calc 2 ^ (j + 1) * X = 2 * (2 ^ j * X) := by ring
        _ ≤ 2 * Xs j := by omega
        _ ≤ f (Xs j) := h2
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hX0 : (0 : ℝ) < X := by linarith
  -- telescoping into blocks
  have htel : ∀ k, ∑ n ∈ Ioc 0 (Xs k), a n - ∑ n ∈ Ioc 0 X, a n =
      ∑ j ∈ range k, ∑ n ∈ Ioc (Xs j) (Xs (j + 1)), a n := by
    intro k
    induction k with
    | zero => simp [hXs]
    | succ k ih =>
      rw [Finset.sum_range_succ, ← ih]
      have hle : Xs k ≤ Xs (k + 1) := by
        have e : Xs (k + 1) = f (Xs k) := by simp only [hXs]; rw [Function.iterate_succ_apply']
        rw [e]; have := hstep _ (hgrow k).1; omega
      rw [← sum_Ioc_consecutive a (Nat.zero_le _) hle]
      ring
  have hbound : ∀ k, |∑ n ∈ Ioc 0 (Xs k), a n - ∑ n ∈ Ioc 0 X, a n| ≤ 2 * K₁ * (X : ℝ) ^ (-1 - κ) := by
    intro k
    rw [htel]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ j ∈ range k, |∑ n ∈ Ioc (Xs j) (Xs (j + 1)), a n| ≤
        K₁ * (X : ℝ) ^ (-1 - κ) * (1 / 2) ^ j := by
      intro j _
      have e : Xs (j + 1) = f (Xs j) := by simp only [hXs]; rw [Function.iterate_succ_apply']
      rw [e]
      refine (hblock _ (hgrow j).1).trans ?_
      have hXj : (2 : ℝ) ^ j * X ≤ Xs j := by exact_mod_cast (hgrow j).2
      have hXj0 : (0 : ℝ) < (2 : ℝ) ^ j * X := by positivity
      have h1 : ((Xs j : ℕ) : ℝ) ^ (-1 - κ) ≤ ((2 : ℝ) ^ j * X) ^ (-1 - κ) :=
        Real.rpow_le_rpow_of_nonpos hXj0 hXj (by linarith)
      have h2 : ((2 : ℝ) ^ j * X) ^ (-1 - κ) ≤ (X : ℝ) ^ (-1 - κ) * (1 / 2) ^ j := by
        rw [Real.mul_rpow (by positivity) hX0.le, mul_comm]
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hX0.le _)
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), one_div, ← Real.rpow_neg_one,
          ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
      calc K₁ * ((Xs j : ℕ) : ℝ) ^ (-1 - κ) ≤ K₁ * ((X : ℝ) ^ (-1 - κ) * (1 / 2) ^ j) :=
            mul_le_mul_of_nonneg_left (h1.trans h2) hK₁
        _ = K₁ * (X : ℝ) ^ (-1 - κ) * (1 / 2) ^ j := by ring
    refine (sum_le_sum hterm).trans ?_
    rw [← mul_sum]
    have hg : ∑ j ∈ range k, (1 / 2 : ℝ) ^ j ≤ 2 := by
      have h := geom_sum_Ico_le_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
        (m := 0) (n := k)
      rw [← range_eq_Ico, pow_zero] at h
      linarith [show (1 : ℝ) / (1 - 1 / 2) = 2 by norm_num]
    calc K₁ * (X : ℝ) ^ (-1 - κ) * ∑ j ∈ range k, (1 / 2 : ℝ) ^ j ≤ K₁ * (X : ℝ) ^ (-1 - κ) * 2 :=
          mul_le_mul_of_nonneg_left hg (by positivity)
      _ = 2 * K₁ * (X : ℝ) ^ (-1 - κ) := by ring
  -- pass to the limit `S(X_k) → c`
  have hrange : ∀ m, ∑ n ∈ Ioc 0 m, a n = ∑ n ∈ range (m + 1), a n := fun m => by
    induction m with
    | zero => simp [ha0]
    | succ m ih => rw [sum_Ioc_succ_top (Nat.zero_le m), ih, Finset.sum_range_succ _ (m + 1)]
  have hXs_top : Tendsto (fun k => Xs k + 1) atTop atTop := by
    refine tendsto_atTop_mono (fun k => ?_) tendsto_id
    have h1 : k < 2 ^ k := Nat.lt_two_pow_self
    have h2 : 2 ^ k ≤ 2 ^ k * X := Nat.le_mul_of_pos_right _ (by omega)
    have := (hgrow k).2
    simp only [id]; omega
  have hlim : Tendsto (fun k => ∑ n ∈ Ioc 0 (Xs k), a n - ∑ n ∈ Ioc 0 X, a n) atTop
      (𝓝 (c - ∑ n ∈ Ioc 0 X, a n)) := by
    simp_rw [hrange]
    exact (hc.tendsto_sum_nat.comp hXs_top).sub_const _
  have h := le_of_tendsto' hlim.abs hbound
  rwa [abs_sub_comm] at h

end

end GaloisForLFunctions.BezoutValuationIncidence
