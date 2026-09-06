import GaloisForLFunctions.RHTower.WeilLagFunctionGrowth
import GaloisForLFunctions.RHTower.WeilLagFunctionOmega
import GaloisForLFunctions.RHTower.WeilLagFunctionDense
import GaloisForLFunctions.RHTower.WeilLagFunctionFrontier
import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinHoheiselEveryBase

/-!
# Prime lags and a zero-free strip

The integer lag sequence `a_n = Φ(log n)` is Lipschitz over a gap: for `n ≤ m ≤ 2n`,
`|a_m − a_n| ≤ 8 (m−n+1)(log m + 2)²/√n`.  Between consecutive primes the gap is at most
`p^{71/100}` for large `p` (the corpus's unconditional Hoheisel-type theorem), so a bound
`a_p ≤ M` on the prime lags alone gives `Φ(L) ≤ M + C e^{(23/100) L}` on the whole half-line, and
the growth criterion excludes every zero with real part above `3/4`.
-/

open Complex Filter Topology Set Real
open scoped Chebyshev
open ArithmeticFunction (vonMangoldt)

namespace RHTower

noncomputable section

/-! ## Sums over a gap -/

theorem psi_sub_psi_eq {n m : ℕ} (hnm : n ≤ m) :
    Chebyshev.psi m - Chebyshev.psi n = ∑ k ∈ Finset.Ioc n m, vonMangoldt k := by
  rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast, Nat.floor_natCast,
    ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le m), ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le n),
    ← Finset.sum_Ioc_consecutive _ (Nat.zero_le n) hnm]
  ring

theorem mertensSum_sub_eq {n m : ℕ} (hnm : n ≤ m) :
    mertensSum m - mertensSum n = ∑ k ∈ Finset.Ioc n m, vonMangoldt k / (k : ℝ) := by
  rw [mertensSum_eq_Icc_zero, mertensSum_eq_Icc_zero,
    ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le m), ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le n),
    ← Finset.sum_Ioc_consecutive _ (Nat.zero_le n) hnm]
  ring

theorem psi_sub_psi_le {n m : ℕ} (hnm : n ≤ m) :
    Chebyshev.psi m - Chebyshev.psi n ≤ ((m - n : ℕ) : ℝ) * Real.log m := by
  rw [psi_sub_psi_eq hnm, ← Nat.card_Ioc, ← nsmul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun k hk => ?_
  have hk' := Finset.mem_Ioc.mp hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  exact ArithmeticFunction.vonMangoldt_le_log.trans
    (Real.log_le_log hk0 (by exact_mod_cast hk'.2))

theorem psi_sub_psi_nonneg {n m : ℕ} (hnm : n ≤ m) : 0 ≤ Chebyshev.psi m - Chebyshev.psi n := by
  rw [psi_sub_psi_eq hnm]
  exact Finset.sum_nonneg fun k _ => ArithmeticFunction.vonMangoldt_nonneg

theorem mertensSum_sub_le {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    mertensSum m - mertensSum n ≤ ((m - n : ℕ) : ℝ) * (Real.log m / n) := by
  rw [mertensSum_sub_eq hnm, ← Nat.card_Ioc, ← nsmul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun k hk => ?_
  have hk' := Finset.mem_Ioc.mp hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnk : (n : ℝ) ≤ k := by exact_mod_cast hk'.1.le
  have hΛ : vonMangoldt k ≤ Real.log m :=
    ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hk0 (by exact_mod_cast hk'.2))
  have hΛ0 : 0 ≤ vonMangoldt k := ArithmeticFunction.vonMangoldt_nonneg
  calc vonMangoldt k / (k : ℝ) ≤ vonMangoldt k / n := by gcongr
    _ ≤ Real.log m / n := by gcongr

theorem mertensSum_sub_nonneg {n m : ℕ} (hnm : n ≤ m) : 0 ≤ mertensSum m - mertensSum n := by
  rw [mertensSum_sub_eq hnm]
  exact Finset.sum_nonneg fun k _ =>
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)

/-! ## The integer bracket -/

/-- The integer-lag bracket `E(k) = (k − ψ(k)) + k(M(k) − log k + γ) − log 2π + S(k)`. -/
def lagBracket (k : ℕ) : ℝ :=
  ((k : ℝ) - Chebyshev.psi k) + k * (mertensSum k - Real.log k + eulerMascheroniConstant)
    - Real.log (2 * Real.pi) + trivialZeroSeriesReal k

theorem integerLag_eq_lagBracket {k : ℕ} (hk : 2 ≤ k) :
    integerLag k = lagBracket k / Real.sqrt k := by
  rw [integerLag_eq hk, lagBracket, one_div, inv_mul_eq_div]

theorem abs_mertensDeviation_le {k : ℕ} (hk : 2 ≤ k) :
    |mertensSum k - Real.log k + eulerMascheroniConstant| ≤ (Real.log k + 2) ^ 2 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hlog : 0 ≤ Real.log k := Real.log_nonneg hk1
  have hM0 := mertensSum_nonneg k
  have hMle := mertensSum_le hk
  have hγ : eulerMascheroniConstant ≤ 1 := by
    have := Real.eulerMascheroniConstant_lt_two_thirds; linarith
  have hγ0 : 0 ≤ eulerMascheroniConstant := by have := eulerMascheroniConstant_gt; linarith
  rw [abs_le]; constructor <;> nlinarith

theorem abs_lagBracket_le {k : ℕ} (hk : 2 ≤ k) : |lagBracket k| ≤ 4 * k * (Real.log k + 2) ^ 2 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hk0 : (0 : ℝ) < k := by linarith
  have hlog : 0 ≤ Real.log k := Real.log_nonneg hk1
  have hψ : Chebyshev.psi k ≤ 2 * k * Real.log k := psi_le_mul_log hk
  have hψ0 : 0 ≤ Chebyshev.psi k := by
    rw [Chebyshev.psi_eq_sum_Icc]
    exact Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
  have hdev := abs_mertensDeviation_le hk
  have hS0 : 0 ≤ trivialZeroSeriesReal k := trivialZeroSeriesReal_nonneg hk1
  have hS1 : trivialZeroSeriesReal k ≤ 1 := trivialZeroSeriesReal_le_one hk1
  have hlog2π : Real.log (2 * Real.pi) ≤ 6 := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)
    have := Real.pi_lt_d2
    linarith
  have hlog2π0 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hkdev : |(k : ℝ) * (mertensSum k - Real.log k + eulerMascheroniConstant)|
      ≤ k * (Real.log k + 2) ^ 2 := by
    rw [abs_mul, abs_of_pos hk0]
    exact mul_le_mul_of_nonneg_left hdev hk0.le
  have hsq : 4 + 4 * Real.log k ≤ (Real.log k + 2) ^ 2 := by nlinarith
  unfold lagBracket
  rw [abs_le]
  have h1 := (abs_le.mp hkdev).1
  have h2 := (abs_le.mp hkdev).2
  constructor <;> nlinarith

theorem abs_lagBracket_sub_le {n m : ℕ} (hn2 : 2 ≤ n) (hnm : n ≤ m) (hm2n : m ≤ 2 * n) :
    |lagBracket m - lagBracket n| ≤ 4 * ((m - n : ℕ) + 1) * (Real.log m + 2) ^ 2 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn0 : (0 : ℝ) < n := by linarith
  have hm2 : 2 ≤ m := le_trans hn2 hnm
  have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have hm2n' : (m : ℝ) ≤ 2 * n := by exact_mod_cast hm2n
  have hm0 : (0 : ℝ) < m := by linarith
  set g : ℝ := ((m - n : ℕ) : ℝ) with hg
  have hg_eq : g = (m : ℝ) - n := by rw [hg]; push_cast [Nat.cast_sub hnm]; ring
  have hg0 : 0 ≤ g := by rw [hg_eq]; linarith
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg (by linarith)
  have hlognm : Real.log n ≤ Real.log m := Real.log_le_log hn0 hnm'
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  -- the pieces
  have hψ := psi_sub_psi_le hnm
  have hψ0 := psi_sub_psi_nonneg hnm
  have hM := mertensSum_sub_le (by omega) hnm
  have hM0 := mertensSum_sub_nonneg hnm
  have hdevn := abs_mertensDeviation_le hn2
  have hlogdiff : Real.log m - Real.log n ≤ g / n := by
    rw [← Real.log_div hm0.ne' hn0.ne', hg_eq]
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < m / n by positivity)
    have e : (m : ℝ) / n - 1 = ((m : ℝ) - n) / n := by field_simp
    linarith
  have hlogdiff0 : 0 ≤ Real.log m - Real.log n := by linarith
  have hSm0 : 0 ≤ trivialZeroSeriesReal m := trivialZeroSeriesReal_nonneg (by linarith)
  have hSn1 : trivialZeroSeriesReal n ≤ 1 := trivialZeroSeriesReal_le_one hn1
  have hSanti : trivialZeroSeriesReal m ≤ trivialZeroSeriesReal n := trivialZeroSeriesReal_anti hn1 hnm'
  -- decomposition
  have hdecomp : lagBracket m - lagBracket n
      = ((m : ℝ) - n) - (Chebyshev.psi m - Chebyshev.psi n)
        + m * (mertensSum m - mertensSum n)
        + ((m : ℝ) - n) * (mertensSum n - Real.log n + eulerMascheroniConstant)
        - m * (Real.log m - Real.log n)
        + (trivialZeroSeriesReal m - trivialZeroSeriesReal n) := by
    unfold lagBracket; ring
  rw [hdecomp, ← hg_eq]
  -- bounds on each piece
  have hb1 : |g - (Chebyshev.psi m - Chebyshev.psi n)| ≤ g * (1 + Real.log m) := by
    rw [abs_le]; constructor <;> nlinarith
  have hb2 : (m : ℝ) * (mertensSum m - mertensSum n) ≤ 2 * g * Real.log m := by
    calc (m : ℝ) * (mertensSum m - mertensSum n) ≤ m * (g * (Real.log m / n)) :=
          mul_le_mul_of_nonneg_left hM hm0.le
      _ = (m / n) * (g * Real.log m) := by field_simp
      _ ≤ 2 * (g * Real.log m) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [div_le_iff₀ hn0]; linarith
      _ = 2 * g * Real.log m := by ring
  have hb2' : 0 ≤ (m : ℝ) * (mertensSum m - mertensSum n) := mul_nonneg hm0.le hM0
  have hb3 : |g * (mertensSum n - Real.log n + eulerMascheroniConstant)| ≤ g * (Real.log m + 2) ^ 2 := by
    rw [abs_mul, abs_of_nonneg hg0]
    apply mul_le_mul_of_nonneg_left _ hg0
    refine hdevn.trans ?_
    have : Real.log n + 2 ≤ Real.log m + 2 := by linarith
    exact pow_le_pow_left₀ (by linarith) this 2
  have hb4 : (m : ℝ) * (Real.log m - Real.log n) ≤ 2 * g := by
    calc (m : ℝ) * (Real.log m - Real.log n) ≤ m * (g / n) :=
          mul_le_mul_of_nonneg_left hlogdiff hm0.le
      _ = (m / n) * g := by field_simp
      _ ≤ 2 * g := by
          apply mul_le_mul_of_nonneg_right _ hg0
          rw [div_le_iff₀ hn0]; linarith
  have hb4' : 0 ≤ (m : ℝ) * (Real.log m - Real.log n) := mul_nonneg hm0.le hlogdiff0
  have hb5 : |trivialZeroSeriesReal m - trivialZeroSeriesReal n| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  have hsq : 4 + 4 * Real.log m ≤ (Real.log m + 2) ^ 2 := by nlinarith
  have hgsq : g * (4 + 4 * Real.log m) ≤ g * (Real.log m + 2) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hg0
  have hL2 : 0 ≤ (Real.log m + 2) ^ 2 := sq_nonneg _
  set A := g - (Chebyshev.psi m - Chebyshev.psi n) with hA
  set B := (m : ℝ) * (mertensSum m - mertensSum n) with hB
  set C := g * (mertensSum n - Real.log n + eulerMascheroniConstant) with hC
  set D := (m : ℝ) * (Real.log m - Real.log n) with hD
  set E := trivialZeroSeriesReal m - trivialZeroSeriesReal n with hE
  have hT : |A + B + C - D + E| ≤ |A| + |B| + |C| + |D| + |E| := by
    have h1 := abs_add_le (A + B + C - D) E
    have h2 := abs_sub (A + B + C) D
    have h3 := abs_add_le (A + B) C
    have h4 := abs_add_le A B
    linarith
  have hBabs : |B| = B := abs_of_nonneg hb2'
  have hDabs : |D| = D := abs_of_nonneg hb4'
  rw [hBabs, hDabs] at hT
  linarith

/-- `1/√n − 1/√m ≤ (m − n)/(2 n √n)` for `1 ≤ n ≤ m`. -/
theorem inv_sqrt_sub_inv_sqrt_le {n m : ℝ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    1 / Real.sqrt n - 1 / Real.sqrt m ≤ (m - n) / (2 * (n * Real.sqrt n)) := by
  have hn0 : 0 < n := by linarith
  have hm0 : 0 < m := by linarith
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
  have hle : Real.sqrt n ≤ Real.sqrt m := Real.sqrt_le_sqrt hnm
  have hsq_n : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
  have hsq_m : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm0.le
  rw [div_sub_div _ _ hsn.ne' hsm.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  have hdiff : (Real.sqrt m - Real.sqrt n) * (Real.sqrt m + Real.sqrt n) = m - n := by
    nlinarith [hsq_n, hsq_m]
  have hkey : 2 * (n * Real.sqrt n) ≤ (Real.sqrt m + Real.sqrt n) * (Real.sqrt n * Real.sqrt m) := by
    have e : (Real.sqrt m + Real.sqrt n) * (Real.sqrt n * Real.sqrt m)
        = m * Real.sqrt n + n * Real.sqrt m := by nlinarith [hsq_n, hsq_m]
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_right hnm hsn.le, mul_le_mul_of_nonneg_left hle hn0.le]
  have hge : 0 ≤ Real.sqrt m - Real.sqrt n := by linarith
  calc (1 * Real.sqrt m - Real.sqrt n * 1) * (2 * (n * Real.sqrt n))
      = (Real.sqrt m - Real.sqrt n) * (2 * (n * Real.sqrt n)) := by ring
    _ ≤ (Real.sqrt m - Real.sqrt n) * ((Real.sqrt m + Real.sqrt n) * (Real.sqrt n * Real.sqrt m)) :=
        mul_le_mul_of_nonneg_left hkey hge
    _ = (m - n) * (Real.sqrt n * Real.sqrt m) := by rw [← hdiff]; ring

/-- **Lipschitz bound for the integer lags over a gap.** -/
theorem abs_integerLag_sub_le {n m : ℕ} (hn2 : 2 ≤ n) (hnm : n ≤ m) (hm2n : m ≤ 2 * n) :
    |integerLag m - integerLag n| ≤ 8 * ((m - n : ℕ) + 1) * (Real.log m + 2) ^ 2 / Real.sqrt n := by
  have hm2 : 2 ≤ m := le_trans hn2 hnm
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn0 : (0 : ℝ) < n := by linarith
  have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have hm2n' : (m : ℝ) ≤ 2 * n := by exact_mod_cast hm2n
  have hm0 : (0 : ℝ) < m := by linarith
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
  have hsnm : Real.sqrt n ≤ Real.sqrt m := Real.sqrt_le_sqrt hnm'
  set g : ℝ := ((m - n : ℕ) : ℝ) with hg
  have hg_eq : g = (m : ℝ) - n := by rw [hg]; push_cast [Nat.cast_sub hnm]; ring
  have hg0 : 0 ≤ g := by rw [hg_eq]; linarith
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg (by linarith)
  have hEm := abs_lagBracket_le hm2
  have hEd := abs_lagBracket_sub_le hn2 hnm hm2n
  rw [← hg] at hEd
  have hinv := inv_sqrt_sub_inv_sqrt_le hn1 hnm'
  have hinv0 : 0 ≤ 1 / Real.sqrt n - 1 / Real.sqrt m := by
    have := one_div_le_one_div_of_le hsn hsnm; linarith
  rw [integerLag_eq_lagBracket hm2, integerLag_eq_lagBracket hn2]
  have hdecomp : lagBracket m / Real.sqrt m - lagBracket n / Real.sqrt n
      = -(lagBracket m * (1 / Real.sqrt n - 1 / Real.sqrt m))
        + (lagBracket m - lagBracket n) / Real.sqrt n := by
    field_simp
    ring
  rw [hdecomp]
  have hL2 : (Real.log m + 2) ^ 2 ≥ 0 := sq_nonneg _
  -- term 1
  have ht1 : |lagBracket m * (1 / Real.sqrt n - 1 / Real.sqrt m)|
      ≤ 4 * g * (Real.log m + 2) ^ 2 / Real.sqrt n := by
    rw [abs_mul, abs_of_nonneg hinv0]
    calc |lagBracket m| * (1 / Real.sqrt n - 1 / Real.sqrt m)
        ≤ (4 * m * (Real.log m + 2) ^ 2) * ((m - n) / (2 * (n * Real.sqrt n))) :=
          mul_le_mul hEm hinv hinv0 (by positivity)
      _ = (m / n) * (2 * ((m - n) * (Real.log m + 2) ^ 2) / Real.sqrt n) := by
          field_simp
          ring
      _ ≤ 2 * (2 * ((m - n) * (Real.log m + 2) ^ 2) / Real.sqrt n) := by
          apply mul_le_mul_of_nonneg_right _ (by
            have : (0:ℝ) ≤ m - n := by linarith
            positivity)
          rw [div_le_iff₀ hn0]; linarith
      _ = 4 * g * (Real.log m + 2) ^ 2 / Real.sqrt n := by rw [hg_eq]; ring
  -- term 2
  have ht2 : |(lagBracket m - lagBracket n) / Real.sqrt n|
      ≤ 4 * (g + 1) * (Real.log m + 2) ^ 2 / Real.sqrt n := by
    rw [abs_div, abs_of_pos hsn]
    exact div_le_div_of_nonneg_right hEd hsn.le
  calc |-(lagBracket m * (1 / Real.sqrt n - 1 / Real.sqrt m))
        + (lagBracket m - lagBracket n) / Real.sqrt n|
      ≤ |lagBracket m * (1 / Real.sqrt n - 1 / Real.sqrt m)|
        + |(lagBracket m - lagBracket n) / Real.sqrt n| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_neg]
    _ ≤ 4 * g * (Real.log m + 2) ^ 2 / Real.sqrt n
        + 4 * (g + 1) * (Real.log m + 2) ^ 2 / Real.sqrt n := add_le_add ht1 ht2
    _ ≤ 8 * (g + 1) * (Real.log m + 2) ^ 2 / Real.sqrt n := by
        rw [← add_div]
        apply div_le_div_of_nonneg_right _ hsn.le
        nlinarith

/-! ## From the lag function to the lag at the base of a gap -/

/-- For `log n ≤ L` with `⌊e^L⌋ ≤ 2n`, the lag function at `L` is within
`11 (⌊e^L⌋ − n + 1)(log 2n + 2)²/√n` of `a_n`. -/
theorem abs_weilLagFunctionReal_sub_integerLag_le_of_gap {n : ℕ} (hn2 : 2 ≤ n) {L : ℝ}
    (hL : Real.log n ≤ L) (hm2n : ⌊Real.exp L⌋₊ ≤ 2 * n) :
    |weilLagFunctionReal L - integerLag n|
      ≤ 11 * ((⌊Real.exp L⌋₊ - n : ℕ) + 1) * (Real.log (2 * n) + 2) ^ 2 / Real.sqrt n := by
  set m := ⌊Real.exp L⌋₊ with hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hnX : (n : ℝ) ≤ Real.exp L := by
    rw [← Real.exp_log hn0]; exact Real.exp_le_exp.mpr hL
  have hnm : n ≤ m := Nat.le_floor hnX
  have hL2 : Real.log 2 ≤ L := (Real.log_le_log two_pos (by exact_mod_cast hn2)).trans hL
  have h1 := abs_weilLagFunctionReal_sub_integerLag_le hL2
  rw [← hm] at h1
  have h2 := abs_integerLag_sub_le hn2 hnm hm2n
  have hm2 : 2 ≤ m := le_trans hn2 hnm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm2n' : (m : ℝ) ≤ 2 * n := by exact_mod_cast hm2n
  have hlog : Real.log m ≤ Real.log (2 * n) := Real.log_le_log hm0 hm2n'
  have hlogm0 : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
  have hsq : (Real.log m + 2) ^ 2 ≤ (Real.log (2 * n) + 2) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hsnm : Real.sqrt n ≤ Real.sqrt m := Real.sqrt_le_sqrt (by exact_mod_cast hnm)
  have hg0 : (0 : ℝ) ≤ ((m - n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hA : 3 * (Real.log m + 2) ^ 2 / Real.sqrt m ≤ 3 * (Real.log (2 * n) + 2) ^ 2 / Real.sqrt n := by
    calc 3 * (Real.log m + 2) ^ 2 / Real.sqrt m ≤ 3 * (Real.log (2 * n) + 2) ^ 2 / Real.sqrt m := by
          gcongr
      _ ≤ 3 * (Real.log (2 * n) + 2) ^ 2 / Real.sqrt n := by gcongr
  have hB : 8 * ((m - n : ℕ) + 1) * (Real.log m + 2) ^ 2 / Real.sqrt n
      ≤ 8 * ((m - n : ℕ) + 1) * (Real.log (2 * n) + 2) ^ 2 / Real.sqrt n := by gcongr
  calc |weilLagFunctionReal L - integerLag n|
      ≤ |weilLagFunctionReal L - integerLag m| + |integerLag m - integerLag n| := abs_sub_le _ _ _
    _ ≤ 3 * (Real.log (2 * n) + 2) ^ 2 / Real.sqrt n
        + 8 * ((m - n : ℕ) + 1) * (Real.log (2 * n) + 2) ^ 2 / Real.sqrt n :=
        add_le_add (h1.trans hA) (h2.trans hB)
    _ ≤ 11 * ((m - n : ℕ) + 1) * (Real.log (2 * n) + 2) ^ 2 / Real.sqrt n := by
        rw [← add_div]
        apply div_le_div_of_nonneg_right _ hsn.le
        have hL2 : 0 ≤ (Real.log (2 * n) + 2) ^ 2 := sq_nonneg _
        nlinarith

/-! ## The prime below `X` with a short gap -/

/-- From the corpus Hoheisel theorem: for large `X` there is a prime `p ≤ X` with
`⌊X⌋ < p + p^{71/100}`. -/
theorem exists_prime_short_gap :
    ∃ X₀ : ℝ, 4 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ X ∧ (⌊X⌋₊ : ℝ) < p + (p : ℝ) ^ (71 / 100 : ℝ) := by
  classical
  obtain ⟨z₀, hz₀⟩ := Filter.eventually_atTop.mp
    RHTower.Sieve.exists_eventually_routeT_prime_in_every_base_window
  refine ⟨max (2 * z₀ + 4) 4, le_max_right _ _, fun X hX => ?_⟩
  have hX4 : (4 : ℝ) ≤ X := le_trans (le_max_right _ _) hX
  have hXz : 2 * z₀ + 4 ≤ X := le_trans (le_max_left _ _) hX
  set n := ⌊X⌋₊ with hn
  have hn4 : 4 ≤ n := Nat.le_floor (by exact_mod_cast hX4)
  have hnX : (n : ℝ) ≤ X := Nat.floor_le (by linarith)
  have hXn : X < n + 1 := Nat.lt_floor_add_one X
  set S := (Finset.range (n + 1)).filter Nat.Prime with hS
  have hSne : S.Nonempty := ⟨2, by
    rw [hS, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, Nat.prime_two⟩⟩
  set p := S.max' hSne with hp
  have hpS : p ∈ S := S.max'_mem hSne
  have hpprime : p.Prime := (Finset.mem_filter.mp hpS).2
  have hpn : p ≤ n := by
    have := Finset.mem_range.mp (Finset.mem_filter.mp hpS).1; omega
  have hmax : ∀ q ∈ S, q ≤ p := fun q hq => S.le_max' q hq
  obtain ⟨q, hq, hq1, hq2⟩ := Nat.exists_prime_lt_and_le_two_mul (n / 2) (by omega)
  have hqS : q ∈ S := by
    rw [hS, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hq⟩
  have hpq : q ≤ p := hmax q hqS
  have hn2q : n ≤ 2 * q := by omega
  have hpz : z₀ ≤ (p : ℝ) := by
    have h1 : (n : ℝ) ≤ 2 * q := by exact_mod_cast hn2q
    have h2 : (q : ℝ) ≤ p := by exact_mod_cast hpq
    linarith
  obtain ⟨p', hp', hpp', hp'le⟩ := hz₀ (p : ℝ) hpz
  have hp'n : n < p' := by
    by_contra hle
    push Not at hle
    have hp'S : p' ∈ S := by
      rw [hS, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hp'⟩
    have h1 : (p' : ℝ) ≤ p := by exact_mod_cast hmax p' hp'S
    linarith
  refine ⟨p, hpprime, ?_, ?_⟩
  · calc (p : ℝ) ≤ n := by exact_mod_cast hpn
      _ ≤ X := hnX
  · calc (n : ℝ) < p' := by exact_mod_cast hp'n
      _ ≤ p + (p : ℝ) ^ (71 / 100 : ℝ) := by
          rw [RHTower.Sieve.routeTHoheiselEveryBaseExponent] at hp'le
          exact hp'le

/-! ## The exponent arithmetic -/

/-- The gap factor at a prime `p ≥ 2` is at most `457776 p^{23/100}`. -/
theorem gap_factor_le {p : ℝ} (hp : 2 ≤ p) :
    11 * (p ^ (71 / 100 : ℝ) + 1) * (Real.log (2 * p) + 2) ^ 2 / Real.sqrt p
      ≤ 457776 * p ^ (23 / 100 : ℝ) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 ≤ p := by linarith
  have h2p1 : (1 : ℝ) ≤ 2 * p := by linarith
  -- `log(2p) ≤ 100 (2p)^{1/100}`
  have hlog : Real.log (2 * p) ≤ 100 * (2 * p) ^ (1 / 100 : ℝ) := by
    have := Real.log_le_rpow_div (x := 2 * p) (by linarith) (by norm_num : (0:ℝ) < 1 / 100)
    rw [div_div_eq_mul_div, div_one] at this
    linarith
  have hr1 : (1 : ℝ) ≤ (2 * p) ^ (1 / 100 : ℝ) := Real.one_le_rpow h2p1 (by norm_num)
  have hr0 : 0 ≤ (2 * p) ^ (1 / 100 : ℝ) := by positivity
  have hsq : (Real.log (2 * p) + 2) ^ 2 ≤ 10404 * ((2 * p) ^ (1 / 100 : ℝ)) ^ 2 := by
    have h1 : Real.log (2 * p) + 2 ≤ 102 * (2 * p) ^ (1 / 100 : ℝ) := by linarith
    have h0 : 0 ≤ Real.log (2 * p) + 2 := by
      have := Real.log_nonneg h2p1; linarith
    calc (Real.log (2 * p) + 2) ^ 2 ≤ (102 * (2 * p) ^ (1 / 100 : ℝ)) ^ 2 :=
          pow_le_pow_left₀ h0 h1 2
      _ = 10404 * ((2 * p) ^ (1 / 100 : ℝ)) ^ 2 := by ring
  have hpow2 : ((2 * p) ^ (1 / 100 : ℝ)) ^ 2 = (2 * p) ^ (1 / 50 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  have hsplit : (2 * p) ^ (1 / 50 : ℝ) ≤ 2 * p ^ (1 / 50 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hp0.le]
    have : (2 : ℝ) ^ (1 / 50 : ℝ) ≤ 2 := Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have hA : p ^ (71 / 100 : ℝ) + 1 ≤ 2 * p ^ (71 / 100 : ℝ) := by
    have : (1 : ℝ) ≤ p ^ (71 / 100 : ℝ) := Real.one_le_rpow hp1 (by norm_num)
    linarith
  have hsqrt : Real.sqrt p = p ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow p
  have hsp : 0 < p ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hp0 _
  have hcomb : p ^ (71 / 100 : ℝ) * p ^ (1 / 50 : ℝ) / p ^ (1 / 2 : ℝ) = p ^ (23 / 100 : ℝ) := by
    rw [← Real.rpow_add hp0, ← Real.rpow_sub hp0]
    norm_num
  have hL0 : 0 ≤ (Real.log (2 * p) + 2) ^ 2 := sq_nonneg _
  have hP0 : 0 ≤ p ^ (71 / 100 : ℝ) := by positivity
  have hQ0 : 0 ≤ p ^ (1 / 50 : ℝ) := by positivity
  rw [hsqrt, div_le_iff₀ hsp]
  calc 11 * (p ^ (71 / 100 : ℝ) + 1) * (Real.log (2 * p) + 2) ^ 2
      ≤ 11 * (2 * p ^ (71 / 100 : ℝ)) * (10404 * (2 * p ^ (1 / 50 : ℝ))) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hA (by norm_num)) _ hL0 (by positivity)
        calc (Real.log (2 * p) + 2) ^ 2 ≤ 10404 * ((2 * p) ^ (1 / 100 : ℝ)) ^ 2 := hsq
          _ = 10404 * (2 * p) ^ (1 / 50 : ℝ) := by rw [hpow2]
          _ ≤ 10404 * (2 * p ^ (1 / 50 : ℝ)) := by gcongr
    _ = 457776 * (p ^ (71 / 100 : ℝ) * p ^ (1 / 50 : ℝ)) := by ring
    _ = 457776 * (p ^ (23 / 100 : ℝ) * p ^ (1 / 2 : ℝ)) := by
        rw [← hcomb, div_mul_cancel₀ _ hsp.ne']
    _ = 457776 * p ^ (23 / 100 : ℝ) * p ^ (1 / 2 : ℝ) := by ring

/-! ## Bounded prime lags force exponential control of the lag function -/

/-- If `a_p ≤ M` for every prime `p`, then `Φ(L) ≤ M₃ e^{L/4}` for all `L ≥ 0`. -/
theorem exists_growth_bound_of_primeLag_le {M : ℝ} (hM : ∀ p : ℕ, p.Prime → integerLag p ≤ M) :
    ∃ M₃ : ℝ, ∀ L : ℝ, 0 ≤ L → weilLagFunctionReal L ≤ M₃ * Real.exp (L / 4) := by
  obtain ⟨X₀, hX₀4, hX₀⟩ := exists_prime_short_gap
  set L₀ : ℝ := Real.log X₀ with hL₀
  have hL₀0 : 0 ≤ L₀ := Real.log_nonneg (by linarith)
  -- the compact part
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0:ℝ)) (b := L₀)).bddAbove_image
    continuous_weilLagFunctionReal.continuousOn
  refine ⟨|M| + 457776 + max B 0, fun L hL => ?_⟩
  have hE : 1 ≤ Real.exp (L / 4) := Real.one_le_exp (by linarith)
  have hE0 : 0 < Real.exp (L / 4) := Real.exp_pos _
  rcases le_or_gt L L₀ with hLL₀ | hLL₀
  · -- `L ∈ [0, L₀]`
    have h1 : weilLagFunctionReal L ≤ B := hB ⟨L, ⟨hL, hLL₀⟩, rfl⟩
    have h2 : B ≤ max B 0 := le_max_left _ _
    have h3 : max B 0 ≤ max B 0 * Real.exp (L / 4) :=
      le_mul_of_one_le_right (le_max_right _ _) hE
    have h4 : 0 ≤ (|M| + 457776) * Real.exp (L / 4) := by positivity
    nlinarith
  · -- `L > L₀`: the prime below `e^L`
    set X : ℝ := Real.exp L with hX
    have hXX₀ : X₀ ≤ X := by
      rw [hX, ← Real.exp_log (by linarith : (0:ℝ) < X₀)]
      exact Real.exp_le_exp.mpr hLL₀.le
    obtain ⟨p, hp, hpX, hgap⟩ := hX₀ X hXX₀
    have hp2 : 2 ≤ p := hp.two_le
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
    have hp2' : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    have hlogp : Real.log p ≤ L := by
      rw [← Real.log_exp L]; exact Real.log_le_log hp0 hpX
    have hpow_le : (p : ℝ) ^ (71 / 100 : ℝ) ≤ p := Real.rpow_le_self_of_one_le hp1 (by norm_num)
    have hm2p : ⌊X⌋₊ ≤ 2 * p := by
      have h1 : (⌊X⌋₊ : ℝ) < 2 * p := by linarith
      exact_mod_cast h1.le
    have hgapℕ : ((⌊X⌋₊ - p : ℕ) : ℝ) ≤ (p : ℝ) ^ (71 / 100 : ℝ) := by
      have hpm : p ≤ ⌊X⌋₊ := Nat.le_floor hpX
      rw [Nat.cast_sub hpm]
      linarith
    have hbound := abs_weilLagFunctionReal_sub_integerLag_le_of_gap hp2 hlogp hm2p
    rw [← hX] at hbound
    have hfactor : 11 * ((⌊X⌋₊ - p : ℕ) + 1) * (Real.log (2 * p) + 2) ^ 2 / Real.sqrt p
        ≤ 11 * ((p : ℝ) ^ (71 / 100 : ℝ) + 1) * (Real.log (2 * p) + 2) ^ 2 / Real.sqrt p := by
      gcongr
    have hgf := gap_factor_le hp2'
    have hpL : (p : ℝ) ^ (23 / 100 : ℝ) ≤ Real.exp ((23 / 100) * L) := by
      rw [Real.rpow_def_of_pos hp0, mul_comm]
      exact Real.exp_le_exp.mpr (by nlinarith)
    have hexp : Real.exp ((23 / 100) * L) ≤ Real.exp (L / 4) :=
      Real.exp_le_exp.mpr (by linarith)
    have hM' : M ≤ |M| * Real.exp (L / 4) := by
      have := le_abs_self M
      have : |M| ≤ |M| * Real.exp (L / 4) := le_mul_of_one_le_right (abs_nonneg M) hE
      linarith
    have h1 := (abs_le.mp hbound).2
    have hmax0 : 0 ≤ max B 0 * Real.exp (L / 4) := by positivity
    calc weilLagFunctionReal L ≤ integerLag p + 11 * ((⌊X⌋₊ - p : ℕ) + 1)
          * (Real.log (2 * p) + 2) ^ 2 / Real.sqrt p := by linarith
      _ ≤ M + 457776 * Real.exp (L / 4) := by
          have := hM p hp
          linarith
      _ ≤ (|M| + 457776 + max B 0) * Real.exp (L / 4) := by nlinarith

/-- **Bounded prime lags force a zero-free strip.**  If `a_p ≤ M` for every prime `p`, every zero
copy has real part at most `3/4`. -/
theorem re_le_three_quarters_of_primeLag_le {M : ℝ} (hM : ∀ p : ℕ, p.Prime → integerLag p ≤ M)
    (q : XiZeroCopy) : (q.1 : ℂ).re ≤ 3 / 4 := by
  obtain ⟨M₃, hM₃⟩ := exists_growth_bound_of_primeLag_le hM
  have := re_le_half_add_of_weilLagFunctionReal_le_exp (a := 1 / 4) (M := M₃) (by norm_num)
    (by norm_num) (fun L hL => by simpa [div_eq_mul_inv, mul_comm] using hM₃ L hL) q
  linarith

/-- By the reflection `ρ ↦ 1 − ρ`, also `Re ρ ≥ 1/4`. -/
theorem one_quarter_le_re_of_primeLag_le {M : ℝ} (hM : ∀ p : ℕ, p.Prime → integerLag p ≤ M)
    (q : XiZeroCopy) : 1 / 4 ≤ (q.1 : ℂ).re := by
  have := re_le_three_quarters_of_primeLag_le hM (xiZeroCopyReflectEquiv q)
  rw [xiZeroCopy_reflect_val, Complex.sub_re, Complex.one_re] at this
  linarith

end

end RHTower
