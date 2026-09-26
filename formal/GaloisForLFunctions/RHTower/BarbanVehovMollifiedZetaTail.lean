import GaloisForLFunctions.RHTower.HighBlockParameters
import GaloisForLFunctions.RHTower.EntireDirichletPolynomial
import GaloisForLFunctions.RHTower.Sieve.ProductFirstMoment

/-!
# The Barban–Vehov mollified zeta function beyond its von Mangoldt head

Let `Ψ_N(s) = Σ_{n ≤ N} μ(n) log(N/n)/log N · n^{-s}` be the Barban–Vehov mollifier
(`hbCoeff`). On `Re s > 1` the Dirichlet coefficients of `ζΨ_N` are
`c_n = Σ_{d | n, d ≤ N} μ(d) log(N/d)/log N`: `c_1 = 1`, `c_n = Λ(n)/log N` for `1 < n ≤ N`, and
`|c_n| ≤ d(n) ≤ n` always. Subtracting the head `1 + P_N(s)`, `P_N(s) = Σ_{n ≤ N} Λ(n)/log N · n^{-s}`,
leaves only the coefficients beyond `N`:

`ζ(s)Ψ_N(s) − 1 − P_N(s) = Σ_{n > N} c_n n^{-s}`,

so that `‖ζΨ_N − 1 − P_N‖ ≤ 2/N` on `Re s ≥ 3` (`norm_hbMollifiedTail_le`).
-/

noncomputable section

open Complex

namespace RHTower

/-- The von Mangoldt head coefficient `Λ(n)/log N`. -/
def hbVonMangoldtCoeff (N n : ℕ) : ℂ :=
  ((ArithmeticFunction.vonMangoldt n / Real.log N : ℝ) : ℂ)

/-- The mollified error beyond its von Mangoldt head: `ζΨ_N − 1 − P_N`. -/
def hbMollifiedTail (N : ℕ) (s : ℂ) : ℂ :=
  riemannZeta s * edPoly (hbCoeff N) (Finset.Icc 1 N) s - 1 -
    edPoly (hbVonMangoldtCoeff N) (Finset.Icc 1 N) s

/-- A coefficient sequence cut off to `[1, N]`. -/
def cutIcc (N : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ := if n ∈ Finset.Icc 1 N then a n else 0

theorem cutIcc_support {N : ℕ} {a : ℕ → ℂ} {k : ℕ} (hk : cutIcc N a k ≠ 0) :
    k ∈ Finset.Icc 1 N := by
  unfold cutIcc at hk
  by_contra h
  rw [if_neg h] at hk
  exact hk rfl

/-- A Dirichlet polynomial over `[1, N]` is the `L`-series of its cut-off coefficients. -/
theorem edPoly_Icc_eq_LSeries (N : ℕ) (a : ℕ → ℂ) (s : ℂ) :
    edPoly a (Finset.Icc 1 N) s = LSeries (cutIcc N a) s := by
  unfold LSeries edPoly
  rw [tsum_eq_sum (s := Finset.Icc 1 N)]
  · refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
    rw [LSeries.term_of_ne_zero hn0, cutIcc, if_pos hn, Complex.ofReal_natCast,
      Complex.cpow_neg, div_eq_mul_inv]
  · intro n hn
    rw [LSeries.term_def]
    split_ifs with h0
    · rfl
    · rw [cutIcc, if_neg hn, zero_div]

theorem hbCoeff_eq_zero_of_lt {N n : ℕ} (hn : N < n) : hbCoeff N n = 0 := by
  unfold hbCoeff Sieve.barbanVehovWeight
  rw [if_neg (by omega)]
  simp

/-- The Dirichlet coefficients of `ζΨ_N`. -/
theorem convolution_one_cutIcc_hbCoeff (N n : ℕ) :
    LSeries.convolution 1 (cutIcc N (hbCoeff N)) n =
      ((Sieve.barbanVehovCoeff N n / Real.log N : ℝ) : ℂ) := by
  simp only [LSeries.convolution_def]
  rw [Nat.sum_divisorsAntidiagonal' (fun x y => (1 : ℕ → ℂ) x * cutIcc N (hbCoeff N) y)]
  simp only [Pi.one_apply, one_mul]
  unfold Sieve.barbanVehovCoeff
  rw [Finset.sum_div, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
  unfold cutIcc
  split_ifs with h
  · rfl
  · have hdN : ¬ d ≤ N := fun h' => h (Finset.mem_Icc.mpr ⟨hd1, h'⟩)
    unfold Sieve.barbanVehovWeight
    rw [if_neg hdN]
    simp

theorem norm_cutIcc_hbCoeff_le {N : ℕ} (hN : 2 ≤ N) (n : ℕ) : ‖cutIcc N (hbCoeff N) n‖ ≤ 1 := by
  unfold cutIcc
  split_ifs with h
  · exact norm_hbCoeff_le hN h
  · simp

theorem norm_convolution_one_cutIcc_hbCoeff_le {N : ℕ} (hN : 2 ≤ N) (n : ℕ) :
    ‖LSeries.convolution 1 (cutIcc N (hbCoeff N)) n‖ ≤ n := by
  simp only [LSeries.convolution_def]
  rw [Nat.sum_divisorsAntidiagonal' (fun x y => (1 : ℕ → ℂ) x * cutIcc N (hbCoeff N) y)]
  simp only [Pi.one_apply, one_mul]
  calc ‖∑ d ∈ n.divisors, cutIcc N (hbCoeff N) d‖
      ≤ ∑ d ∈ n.divisors, ‖cutIcc N (hbCoeff N) d‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ n.divisors, (1 : ℝ) := Finset.sum_le_sum fun d _ => norm_cutIcc_hbCoeff_le hN d
    _ = n.divisors.card := by simp
    _ ≤ n := by exact_mod_cast Nat.card_divisors_le_self n

/-- The coefficients of `ζΨ_N − 1 − P_N`. -/
def hbTailCoeff (N : ℕ) : ℕ → ℂ :=
  LSeries.convolution 1 (cutIcc N (hbCoeff N)) - LSeries.delta - cutIcc N (hbVonMangoldtCoeff N)

theorem hbTailCoeff_eq_zero_of_le {N n : ℕ} (hN : 2 ≤ N) (hn : n ≤ N) : hbTailCoeff N n = 0 := by
  unfold hbTailCoeff
  simp only [Pi.sub_apply]
  rw [convolution_one_cutIcc_hbCoeff]
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · interval_cases n
    · simp [Sieve.barbanVehovCoeff, LSeries.delta, cutIcc]
    · have hlog : Real.log (N : ℝ) ≠ 0 :=
        (Real.log_pos (by exact_mod_cast (by omega : 1 < N))).ne'
      rw [Sieve.barbanVehovCoeff_one (by omega), div_self hlog]
      simp [LSeries.delta, cutIcc, hbVonMangoldtCoeff]
  · rw [Sieve.barbanVehovCoeff_eq_vonMangoldt (by omega) hn]
    have hmem : n ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨by omega, hn⟩
    simp only [cutIcc, if_pos hmem, hbVonMangoldtCoeff, LSeries.delta]
    rw [if_neg (by omega)]
    ring

theorem norm_hbTailCoeff_le {N n : ℕ} (hN : 2 ≤ N) (hn : N < n) : ‖hbTailCoeff N n‖ ≤ n := by
  unfold hbTailCoeff
  simp only [Pi.sub_apply]
  have h1 : LSeries.delta n = 0 := by
    simp only [LSeries.delta]
    rw [if_neg (by omega)]
  have h2 : cutIcc N (hbVonMangoldtCoeff N) n = 0 := by
    unfold cutIcc
    rw [if_neg (by simp; omega)]
  rw [h1, h2, sub_zero, sub_zero]
  exact norm_convolution_one_cutIcc_hbCoeff_le hN n

theorem hbMollifiedTail_eq_LSeries {N : ℕ} {s : ℂ} (hs : 1 < s.re) :
    hbMollifiedTail N s = LSeries (hbTailCoeff N) s := by
  have hsum1 : LSeriesSummable 1 s := LSeriesSummable_one_iff.mpr hs
  have hsumΨ : LSeriesSummable (cutIcc N (hbCoeff N)) s :=
    Sieve.LSeriesSummable_of_support (fun k hk => cutIcc_support hk) s
  have hsumP : LSeriesSummable (cutIcc N (hbVonMangoldtCoeff N)) s :=
    Sieve.LSeriesSummable_of_support (fun k hk => cutIcc_support hk) s
  have hsumδ : LSeriesSummable LSeries.delta s :=
    Sieve.LSeriesSummable_of_support (s := {1}) (fun k hk => by
      simp only [LSeries.delta] at hk
      split_ifs at hk with h
      · simp [h]
      · exact absurd rfl hk) s
  have hconv : LSeriesSummable (LSeries.convolution 1 (cutIcc N (hbCoeff N))) s :=
    hsum1.convolution hsumΨ
  unfold hbMollifiedTail hbTailCoeff
  rw [LSeries_sub (hconv.sub hsumδ) hsumP, LSeries_sub hconv hsumδ, LSeries_convolution' hsum1 hsumΨ,
    LSeries_one_eq_riemannZeta hs, LSeries_delta, edPoly_Icc_eq_LSeries, edPoly_Icc_eq_LSeries]
  rfl

/-- **The tail beyond the von Mangoldt head is `O(1/N)` on `Re s ≥ 3`.** -/
theorem norm_hbMollifiedTail_le {N : ℕ} (hN : 2 ≤ N) {s : ℂ} (hs : 3 ≤ s.re) :
    ‖hbMollifiedTail N s‖ ≤ 2 / N := by
  rw [hbMollifiedTail_eq_LSeries (by linarith)]
  set g : ℕ → ℝ := fun n => if N < n then (((n : ℝ) ^ 2)⁻¹) else 0 with hg
  have hg0 : ∀ n, 0 ≤ g n := fun n => by simp only [hg]; split_ifs <;> positivity
  have hterm : ∀ n : ℕ, ‖LSeries.term (hbTailCoeff N) s n‖ ≤ g n := by
    intro n
    rw [LSeries.norm_term_eq]
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [if_pos h0]
      exact hg0 n
    · rw [if_neg hpos.ne']
      by_cases hNn : N < n
      · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
        have hnpos : (0 : ℝ) < n := by linarith
        have hc := norm_hbTailCoeff_le hN hNn
        have hpow : (n : ℝ) ^ (3 : ℝ) ≤ (n : ℝ) ^ s.re :=
          Real.rpow_le_rpow_of_exponent_le hn1 hs
        have hpow3 : (n : ℝ) ^ (3 : ℝ) = (n : ℝ) ^ 3 := by
          exact_mod_cast Real.rpow_natCast (n : ℝ) 3
        have hgn : g n = ((n : ℝ) ^ 2)⁻¹ := by simp only [hg, if_pos hNn]
        rw [hgn, div_le_iff₀ (by positivity)]
        calc ‖hbTailCoeff N n‖ ≤ n := hc
          _ = ((n : ℝ) ^ 2)⁻¹ * (n : ℝ) ^ 3 := by field_simp
          _ ≤ ((n : ℝ) ^ 2)⁻¹ * (n : ℝ) ^ s.re := by
              rw [← hpow3]
              exact mul_le_mul_of_nonneg_left hpow (by positivity)
      · rw [hbTailCoeff_eq_zero_of_le hN (not_lt.mp hNn), norm_zero, zero_div]
        exact hg0 n
  have hgsum : Summable g := by
    refine Summable.of_nonneg_of_le hg0 (fun n => ?_)
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    simp only [hg]
    split_ifs
    · rw [one_div]
    · positivity
  have htsum : ∑' n, g n ≤ 2 / N := by
    refine hgsum.tsum_le_of_sum_le fun S => ?_
    obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ n ∈ S, n < M := ⟨S.sup id + 1, fun n hn =>
      Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)⟩
    calc ∑ n ∈ S, g n ≤ ∑ n ∈ Finset.range M, g n := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => Finset.mem_range.mpr (hM n hn))
            fun n _ _ => hg0 n
      _ = ∑ n ∈ Finset.Ioo N M, ((n : ℝ) ^ 2)⁻¹ := by
          rw [← Finset.sum_filter_add_sum_filter_not (Finset.range M) (fun n => N < n)]
          have h1 : ∑ n ∈ (Finset.range M).filter (fun n => ¬ N < n), g n = 0 :=
            Finset.sum_eq_zero fun n hn => by
              simp only [hg, if_neg (Finset.mem_filter.mp hn).2]
          rw [h1, add_zero]
          have hset : (Finset.range M).filter (fun n => N < n) = Finset.Ioo N M := by
            ext n
            simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioo]
            tauto
          rw [hset]
          refine Finset.sum_congr rfl fun n hn => ?_
          simp only [hg, if_pos (Finset.mem_Ioo.mp hn).1]
      _ ≤ 2 / ((N : ℝ) + 1) := sum_Ioo_inv_sq_le N M
      _ ≤ 2 / N := by
          have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
          exact div_le_div_of_nonneg_left (by norm_num) hN0 (by linarith)
  have hsumnorm : Summable fun n => ‖LSeries.term (hbTailCoeff N) s n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hgsum
  calc ‖LSeries (hbTailCoeff N) s‖ ≤ ∑' n, ‖LSeries.term (hbTailCoeff N) s n‖ :=
        norm_tsum_le_tsum_norm hsumnorm
    _ ≤ ∑' n, g n := hsumnorm.tsum_le_tsum hterm hgsum
    _ ≤ 2 / N := htsum

/-- `‖Ψ_N(s)‖ ≤ N` on `Re s ≥ 0`. -/
theorem norm_edPoly_hbCoeff_le {N : ℕ} (hN : 2 ≤ N) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖edPoly (hbCoeff N) (Finset.Icc 1 N) s‖ ≤ N := by
  unfold edPoly
  calc ‖∑ n ∈ Finset.Icc 1 N, hbCoeff N n * ((n : ℝ) : ℂ) ^ (-s)‖
      ≤ ∑ n ∈ Finset.Icc 1 N, ‖hbCoeff N n * ((n : ℝ) : ℂ) ^ (-s)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 N, (1 : ℝ) := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), Complex.neg_re]
        have h1 : (n : ℝ) ^ (-s.re) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
        calc ‖hbCoeff N n‖ * (n : ℝ) ^ (-s.re) ≤ 1 * 1 :=
              mul_le_mul (norm_hbCoeff_le hN hn) h1 (by positivity) zero_le_one
          _ = 1 := one_mul 1
    _ = N := by simp

theorem norm_hbVonMangoldtCoeff_le {N n : ℕ} (hN : 2 ≤ N) (hn : n ∈ Finset.Icc 1 N) :
    ‖hbVonMangoldtCoeff N n‖ ≤ 1 := by
  obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
  unfold hbVonMangoldtCoeff
  rw [Complex.norm_real, Real.norm_eq_abs]
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hΛ0 : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  have hΛ : ArithmeticFunction.vonMangoldt n ≤ Real.log N :=
    ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log (by exact_mod_cast (by omega : 0 < n)) (by exact_mod_cast hnN))
  rw [abs_of_nonneg (div_nonneg hΛ0 hlogN.le), div_le_one hlogN]
  exact hΛ

/-- `‖P_N(s)‖ ≤ N` on `Re s ≥ 0`. -/
theorem norm_edPoly_hbVonMangoldtCoeff_le {N : ℕ} (hN : 2 ≤ N) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖edPoly (hbVonMangoldtCoeff N) (Finset.Icc 1 N) s‖ ≤ N := by
  unfold edPoly
  calc ‖∑ n ∈ Finset.Icc 1 N, hbVonMangoldtCoeff N n * ((n : ℝ) : ℂ) ^ (-s)‖
      ≤ ∑ n ∈ Finset.Icc 1 N, ‖hbVonMangoldtCoeff N n * ((n : ℝ) : ℂ) ^ (-s)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 N, (1 : ℝ) := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), Complex.neg_re]
        have h1 : (n : ℝ) ^ (-s.re) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
        calc ‖hbVonMangoldtCoeff N n‖ * (n : ℝ) ^ (-s.re) ≤ 1 * 1 :=
              mul_le_mul (norm_hbVonMangoldtCoeff_le hN hn) h1 (by positivity) zero_le_one
          _ = 1 := one_mul 1
    _ = N := by simp

end RHTower
