import GaloisForLFunctions.RHTower.WeilLagFunctionOneSided

/-!
# The integer lag inequality

Between consecutive integers `n ≤ e^L < n+1` the prime side of the lag function is an explicit
combination of monotone pieces, so `Φ(L) ≤ Φ(log n) + 30`.  Hence the one-sided lag criterion only
needs the integer lags: RH holds iff the sequence

`a_n = Φ(log n) = [(n − ψ(n)) + n(Σ_{m≤n} Λ(m)/m − log n + γ) − log 2π + S(n)] / √n`

is bounded above, and then it is bounded by `2 + γ − log 4π`.  Equivalently, RH is the single
inequality, for every `n ≥ 2`,

`(n − ψ(n)) + n(Σ_{m≤n} Λ(m)/m − log n + γ) − log 2π + S(n) ≤ (2 + γ − log 4π) √n`,

with `S(n) = Σ_{k≥1} n^{−2k}/(2k(2k+1))`.
-/

open Real Filter Topology
open ArithmeticFunction (vonMangoldt)

namespace RHTower

noncomputable section

/-! ## The real prime side -/

/-- The real trivial-zero series `S(X) = Σ_{k≥0} X^{−2(k+1)}/(2(k+1)(2k+3))`. -/
def trivialZeroSeriesReal (X : ℝ) : ℝ :=
  ∑' k : ℕ, (X ^ (2 * (k + 1)))⁻¹ / (2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 3))

theorem trivialZeroSeries_eq_real (X : ℝ) :
    trivialZeroSeries X = (trivialZeroSeriesReal X : ℂ) :=
  trivialZeroSeries_eq_ofReal X

theorem summable_trivialZeroSeriesReal_term {X : ℝ} (hX : 1 ≤ X) :
    Summable (fun k : ℕ => (X ^ (2 * (k + 1)))⁻¹ / (2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 3))) := by
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((Real.summable_one_div_nat_pow (p := 2)).mpr one_lt_two |> (summable_nat_add_iff 1).mpr)
  have hXk : (1 : ℝ) ≤ X ^ (2 * (k + 1)) := one_le_pow₀ hX
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  push_cast
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc (X ^ (2 * (k + 1)))⁻¹ * ((k : ℝ) + 1) ^ 2 ≤ 1 * ((k : ℝ) + 1) ^ 2 := by
        gcongr; exact inv_le_one_of_one_le₀ hXk
    _ ≤ 1 * (2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 3)) := by nlinarith

theorem trivialZeroSeriesReal_nonneg {X : ℝ} (hX : 1 ≤ X) : 0 ≤ trivialZeroSeriesReal X :=
  tsum_nonneg fun k =>
    div_nonneg (inv_nonneg.mpr (pow_nonneg (by linarith) _)) (by positivity)

theorem trivialZeroSeriesReal_anti {X Y : ℝ} (hX : 1 ≤ X) (hXY : X ≤ Y) :
    trivialZeroSeriesReal Y ≤ trivialZeroSeriesReal X := by
  refine (summable_trivialZeroSeriesReal_term (hX.trans hXY)).tsum_le_tsum (fun k => ?_)
    (summable_trivialZeroSeriesReal_term hX)
  have hX0 : (0:ℝ) < X := by linarith
  gcongr

/-- `S(1) = Σ_{k≥0} 1/(2(k+1)(2k+3)) = 1 − log 2`. -/
theorem trivialZeroSeriesReal_one : trivialZeroSeriesReal 1 = 1 - Real.log 2 := by
  have h := (Complex.hasSum_iff _ _).mp hasSum_inv_succ_mul_two_add_three
  have hre : HasSum (fun k : ℕ => 1 / (((k : ℝ) + 1) * (2 * (k : ℝ) + 3))) (2 - 2 * Real.log 2) := by
    have h1 := h.1
    have e1 : (fun k : ℕ => (1 / (((k : ℂ) + 1) * (2 * (k : ℂ) + 3))).re)
        = fun k : ℕ => 1 / (((k : ℝ) + 1) * (2 * (k : ℝ) + 3)) := by
      funext k
      rw [show (1 / (((k : ℂ) + 1) * (2 * (k : ℂ) + 3))) = ((1 / (((k : ℝ) + 1) * (2 * (k : ℝ) + 3)) : ℝ) : ℂ) by
        push_cast; ring]
      exact Complex.ofReal_re _
    have e2 : (2 - 2 * Complex.log 2).re = 2 - 2 * Real.log 2 := by
      rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, ← Complex.ofReal_log (by norm_num),
        ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.ofReal_re]
    rwa [e1, e2] at h1
  unfold trivialZeroSeriesReal
  have hf : (fun k : ℕ => ((1 : ℝ) ^ (2 * (k + 1)))⁻¹ / (2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 3)))
      = fun k : ℕ => (1 / 2 : ℝ) * (1 / (((k : ℝ) + 1) * (2 * (k : ℝ) + 3))) := by
    funext k; rw [one_pow, inv_one]; field_simp
  rw [hf, tsum_mul_left, hre.tsum_eq]; ring

theorem trivialZeroSeriesReal_le_one {X : ℝ} (hX : 1 ≤ X) : trivialZeroSeriesReal X ≤ 1 := by
  have h := trivialZeroSeriesReal_anti le_rfl hX
  rw [trivialZeroSeriesReal_one] at h
  have := Real.log_pos (by norm_num : (1:ℝ) < 2)
  linarith

/-- The Mertens sum `M(n) = Σ_{m≤n} Λ(m)/m`. -/
def mertensSum (n : ℕ) : ℝ := ∑ m ∈ Finset.Icc 1 n, vonMangoldt m / (m : ℝ)

/-- The real prime side of the lag function, `L > 0`, `X = e^L`. -/
theorem weilLagFunctionReal_eq_prime_side {L : ℝ} (hL : 0 < L) :
    weilLagFunctionReal L = Real.exp (-L / 2) *
      ((Real.exp L - Chebyshev.psi (Real.exp L)) +
        Real.exp L * (mertensSum ⌊Real.exp L⌋₊ - L + eulerMascheroniConstant)
        - Real.log (2 * π) + trivialZeroSeriesReal (Real.exp L)) := by
  apply Complex.ofReal_injective
  rw [← weilLagFunction_eq_ofReal, weilLagFunction_eq_prime_side hL, trivialZeroSeries_eq_real]
  unfold mertensSum
  push_cast
  ring

/-- The integer lag values `a_n = Φ(log n)`. -/
def integerLag (n : ℕ) : ℝ := weilLagFunctionReal (Real.log n)

theorem integerLag_eq {n : ℕ} (hn : 2 ≤ n) :
    integerLag n = (1 / Real.sqrt n) *
      (((n : ℝ) - Chebyshev.psi n) + n * (mertensSum n - Real.log n + eulerMascheroniConstant)
        - Real.log (2 * π) + trivialZeroSeriesReal n) := by
  unfold integerLag
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hL : 0 < Real.log n := Real.log_pos hn1
  rw [weilLagFunctionReal_eq_prime_side hL, Real.exp_log hn0, Nat.floor_natCast,
    show Real.exp (-Real.log n / 2) = 1 / Real.sqrt n by
      rw [neg_div, Real.exp_neg, Real.exp_half, Real.exp_log hn0, one_div]]

/-! ## Elementary bounds -/

theorem psi_le_mul_log {n : ℕ} (hn : 2 ≤ n) : Chebyshev.psi n ≤ 2 * n * Real.log n := by
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn1
  calc ∑ m ∈ Finset.Icc 0 n, vonMangoldt m ≤ ∑ m ∈ Finset.Icc 0 n, Real.log n := by
        refine Finset.sum_le_sum fun m hm => ?_
        rcases Nat.eq_zero_or_pos m with rfl | hm0
        · simp [hlog]
        · refine (ArithmeticFunction.vonMangoldt_le_log).trans (Real.log_le_log (by exact_mod_cast hm0) ?_)
          exact_mod_cast (Finset.mem_Icc.mp hm).2
    _ = (n + 1) * Real.log n := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
    _ ≤ 2 * n * Real.log n := by nlinarith

theorem mertensSum_nonneg (n : ℕ) : 0 ≤ mertensSum n :=
  Finset.sum_nonneg fun m _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg m)

theorem mertensSum_le {n : ℕ} (hn : 2 ≤ n) : mertensSum n ≤ Real.log n * (1 + Real.log n) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hH : ∑ m ∈ Finset.Icc 1 n, (1 / (m : ℝ)) ≤ 1 + Real.log n := by
    have h := harmonic_le_one_add_log n
    rw [harmonic_eq_sum_Icc] at h
    push_cast at h
    simpa [one_div] using h
  calc mertensSum n = ∑ m ∈ Finset.Icc 1 n, vonMangoldt m / (m : ℝ) := rfl
    _ ≤ ∑ m ∈ Finset.Icc 1 n, Real.log n * (1 / (m : ℝ)) := by
        refine Finset.sum_le_sum fun m hm => ?_
        have hm := Finset.mem_Icc.mp hm
        have hm0 : (0 : ℝ) < m := by exact_mod_cast hm.1
        rw [div_eq_mul_one_div]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact (ArithmeticFunction.vonMangoldt_le_log).trans (Real.log_le_log hm0 (by exact_mod_cast hm.2))
    _ = Real.log n * ∑ m ∈ Finset.Icc 1 n, (1 / (m : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ Real.log n * (1 + Real.log n) := by gcongr

theorem log_le_two_sqrt {x : ℝ} (hx : 0 ≤ x) : Real.log x ≤ 2 * Real.sqrt x := by
  have := Real.log_le_rpow_div hx (by norm_num : (0:ℝ) < 1 / 2)
  rw [Real.sqrt_eq_rpow]
  linarith

theorem log_le_four_rpow_quarter {x : ℝ} (hx : 0 ≤ x) : Real.log x ≤ 4 * x ^ (1 / 4 : ℝ) := by
  have := Real.log_le_rpow_div hx (by norm_num : (0:ℝ) < 1 / 4)
  linarith

theorem sq_log_add_two_le {n : ℕ} (hn : 2 ≤ n) : (Real.log n + 2) ^ 2 ≤ 36 * Real.sqrt n := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have h1 := log_le_four_rpow_quarter hn0
  have hq : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := Real.one_le_rpow hn1 (by norm_num)
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hsq : ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt n := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hn0]; norm_num
  have hle : Real.log n + 2 ≤ 4 * (n : ℝ) ^ (1 / 4 : ℝ) + 2 * (n : ℝ) ^ (1 / 4 : ℝ) := by linarith
  calc (Real.log n + 2) ^ 2 ≤ (4 * (n : ℝ) ^ (1 / 4 : ℝ) + 2 * (n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by linarith) hle 2
    _ = 36 * ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := by ring
    _ = 36 * Real.sqrt n := by rw [hsq]

/-- `√(n+1) − √n ≤ 1/(2√n)`. -/
theorem sqrt_succ_sub_sqrt_le {n : ℝ} (hn : 1 ≤ n) :
    Real.sqrt (n + 1) - Real.sqrt n ≤ 1 / (2 * Real.sqrt n) := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
  have hs1 : Real.sqrt n ≤ Real.sqrt (n + 1) := Real.sqrt_le_sqrt (by linarith)
  have hprod : (Real.sqrt (n + 1) - Real.sqrt n) * (Real.sqrt (n + 1) + Real.sqrt n) = 1 := by
    have h1 := Real.mul_self_sqrt (show (0:ℝ) ≤ n + 1 by linarith)
    have h2 := Real.mul_self_sqrt (show (0:ℝ) ≤ n by linarith)
    linear_combination h1 - h2
  have : Real.sqrt (n + 1) - Real.sqrt n = 1 / (Real.sqrt (n + 1) + Real.sqrt n) := by
    rw [eq_div_iff (by positivity)]; exact hprod
  rw [this, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- `1/√n − 1/√(n+1) ≤ 1/(2 n^{3/2})`, stated with `n * √n`. -/
theorem inv_sqrt_sub_inv_sqrt_succ_le {n : ℝ} (hn : 1 ≤ n) :
    1 / Real.sqrt n - 1 / Real.sqrt (n + 1) ≤ 1 / (2 * (n * Real.sqrt n)) := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
  have hs1 : 0 < Real.sqrt (n + 1) := Real.sqrt_pos.mpr (by linarith)
  have hle : Real.sqrt n ≤ Real.sqrt (n + 1) := Real.sqrt_le_sqrt (by linarith)
  have hd := sqrt_succ_sub_sqrt_le hn
  have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (by linarith)
  rw [div_sub_div _ _ hs.ne' hs1.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : (1 * Real.sqrt (n + 1) - Real.sqrt n * 1) ≤ 1 / (2 * Real.sqrt n) := by linarith
  calc (1 * Real.sqrt (n + 1) - Real.sqrt n * 1) * (2 * (n * Real.sqrt n))
      ≤ (1 / (2 * Real.sqrt n)) * (2 * (n * Real.sqrt n)) := by gcongr
    _ = n := by field_simp
    _ = 1 * (Real.sqrt n * Real.sqrt n) := by rw [hsq]; ring
    _ ≤ 1 * (Real.sqrt n * Real.sqrt (n + 1)) := by gcongr

/-! ## The interval bound -/

/-- The prime-side expression at `X ∈ [n, n+1)` differs from the one at `n` by at most `30`. -/
theorem lag_interval_core {X L : ℝ} {n : ℕ} (hn2 : 2 ≤ n) (hnX : (n : ℝ) ≤ X) (hXn : X < n + 1)
    (hlogn : Real.log n ≤ L) (hLlog' : L ≤ Real.log n + 1 / n) :
    (1 / Real.sqrt X) * ((X - Chebyshev.psi n) + X * (mertensSum n - L + eulerMascheroniConstant)
        - Real.log (2 * π) + trivialZeroSeriesReal X)
      ≤ (1 / Real.sqrt n) * (((n : ℝ) - Chebyshev.psi n)
          + n * (mertensSum n - Real.log n + eulerMascheroniConstant)
          - Real.log (2 * π) + trivialZeroSeriesReal n) + 30 ∧
    (1 / Real.sqrt n) * (((n : ℝ) - Chebyshev.psi n)
          + n * (mertensSum n - Real.log n + eulerMascheroniConstant)
          - Real.log (2 * π) + trivialZeroSeriesReal n) - 30
      ≤ (1 / Real.sqrt X) * ((X - Chebyshev.psi n) + X * (mertensSum n - L + eulerMascheroniConstant)
        - Real.log (2 * π) + trivialZeroSeriesReal X) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hinvn : (1 : ℝ) / n ≤ 1 := by rw [div_le_one hn0]; exact hn1
  have hLlog : L ≤ Real.log n + 1 := by linarith
  have hX0 : 0 < X := by linarith
  have hlog := log_le_two_sqrt hn0.le
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hψn : Chebyshev.psi n ≤ 2 * n * Real.log n := psi_le_mul_log hn2
  have hψ0 : 0 ≤ Chebyshev.psi n := by
    rw [Chebyshev.psi_eq_sum_Icc]
    exact Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
  have hM0 := mertensSum_nonneg n
  have hMle := mertensSum_le hn2
  have hγ : eulerMascheroniConstant ≤ 1 := by
    have := Real.eulerMascheroniConstant_lt_two_thirds; linarith
  have hγ0 : 0 ≤ eulerMascheroniConstant := by have := eulerMascheroniConstant_gt; linarith
  have hS0 : 0 ≤ trivialZeroSeriesReal n := trivialZeroSeriesReal_nonneg hn1
  have hSX0 : 0 ≤ trivialZeroSeriesReal X := trivialZeroSeriesReal_nonneg (hn1.trans hnX)
  have hSle : trivialZeroSeriesReal X ≤ trivialZeroSeriesReal n := trivialZeroSeriesReal_anti hn1 hnX
  have hS1 : trivialZeroSeriesReal n ≤ 1 := trivialZeroSeriesReal_le_one hn1
  have hlog2π : Real.log (2 * π) ≤ 6 := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < 2 * π)
    have := Real.pi_lt_d2
    linarith
  have hlog2π0 : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hsq36 := sq_log_add_two_le hn2
  have hgap := sqrt_succ_sub_sqrt_le hn1
  have hinv0 := inv_sqrt_sub_inv_sqrt_succ_le hn1
  have hsn_le : Real.sqrt n ≤ Real.sqrt X := Real.sqrt_le_sqrt hnX
  have hsX_lt : Real.sqrt X < Real.sqrt (n + 1) := Real.sqrt_lt_sqrt hX0.le hXn
  have hsXsq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
  have hsnsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
  have hsX0 : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX0
  have hsn0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hsn1 : 1 ≤ Real.sqrt n := by
    have := Real.sqrt_le_sqrt hn1; rwa [Real.sqrt_one] at this
  -- abbreviations
  set sX := Real.sqrt X with hsX
  set sn := Real.sqrt n with hsn
  set sn1 := Real.sqrt (n + 1) with hsn1'
  set ψ := Chebyshev.psi n with hψ
  set M := mertensSum n with hM
  set SX := trivialZeroSeriesReal X with hSX
  set Sn := trivialZeroSeriesReal n with hSn
  set l := Real.log (2 * π) with hl
  set γ := eulerMascheroniConstant with hγdef
  set ln := Real.log n with hln
  have hLln : L - ln ≤ 1 / (sn * sn) := by rw [hsnsq]; exact (by linarith : L - Real.log n ≤ 1 / n)
  clear_value sX sn sn1 ψ M SX Sn l γ ln
  have hgap' : sX - sn ≤ 1 / (2 * sn) := by linarith
  have hinv : 1 / sn - 1 / sX ≤ 1 / (2 * (n * sn)) := by
    have : 1 / sn1 ≤ 1 / sX := one_div_le_one_div_of_le hsX0 hsX_lt.le
    linarith
  have hinv_nonneg : 0 ≤ 1 / sn - 1 / sX := by
    have := one_div_le_one_div_of_le hsn0 hsn_le; linarith
  -- the five pieces
  have hP1 : sX - sn ≤ 1 := by
    have : 1 / (2 * sn) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    linarith
  have hP2 : ψ * (1 / sn - 1 / sX) ≤ 2 := by
    calc ψ * (1 / sn - 1 / sX) ≤ (2 * n * ln) * (1 / (2 * (n * sn))) :=
          mul_le_mul hψn hinv hinv_nonneg (by positivity)
      _ = ln / sn := by field_simp
      _ ≤ 2 := by rw [div_le_iff₀ hsn0]; linarith
  have hb : |M - L + γ| ≤ (ln + 2) ^ 2 := by
    rw [abs_le]; constructor <;> nlinarith
  have hgap0 : 0 ≤ sX - sn := by linarith
  have hP3 : (sX - sn) * (M - L + γ) ≤ 18 := by
    calc (sX - sn) * (M - L + γ) ≤ (sX - sn) * |M - L + γ| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) hgap0
      _ ≤ (1 / (2 * sn)) * (36 * sn) :=
          mul_le_mul hgap' (hb.trans hsq36) (abs_nonneg _) (by positivity)
      _ = 18 := by field_simp; ring
  have hP4 : l * (1 / sn - 1 / sX) ≤ 6 := by
    have h1 : 1 / sn - 1 / sX ≤ 1 := by
      have : 1 / sn ≤ 1 := by rw [div_le_one hsn0]; exact hsn1
      have : 0 < 1 / sX := by positivity
      linarith
    calc l * (1 / sn - 1 / sX) ≤ 6 * 1 := mul_le_mul hlog2π h1 hinv_nonneg (by norm_num)
      _ = 6 := by ring
  have hP5 : SX / sX ≤ Sn / sn := by
    have h1 : SX / sX ≤ Sn / sX := by gcongr
    have h2 : Sn / sX ≤ Sn / sn := by gcongr
    exact h1.trans h2
  have hP6 : sn * (ln - L) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hsn0.le (by linarith only [hlogn])
  -- lower bounds of the pieces
  have hQ1 : 0 ≤ sX - sn := by linarith
  have hQ2 : 0 ≤ ψ * (1 / sn - 1 / sX) := mul_nonneg hψ0 hinv_nonneg
  have hQ3 : -18 ≤ (sX - sn) * (M - L + γ) := by
    have h1 : (sX - sn) * (-|M - L + γ|) ≤ (sX - sn) * (M - L + γ) :=
      mul_le_mul_of_nonneg_left (neg_abs_le _) hgap0
    have h1' : (sX - sn) * (-|M - L + γ|) = -((sX - sn) * |M - L + γ|) := by ring
    have h2 : (sX - sn) * |M - L + γ| ≤ 18 := by
      calc (sX - sn) * |M - L + γ| ≤ (1 / (2 * sn)) * (36 * sn) :=
            mul_le_mul hgap' (hb.trans hsq36) (abs_nonneg _) (by positivity)
        _ = 18 := by field_simp; ring
    linarith only [h1, h1', h2]
  have hQ4 : 0 ≤ l * (1 / sn - 1 / sX) := mul_nonneg hlog2π0 hinv_nonneg
  have hQ5 : -1 ≤ SX / sX - Sn / sn := by
    have h1 : 0 ≤ SX / sX := by positivity
    have h2 : Sn / sn ≤ 1 := by rw [div_le_one hsn0]; linarith
    linarith
  have hQ6 : -1 ≤ sn * (ln - L) := by
    have h1 : sn * (L - ln) ≤ sn * (1 / (sn * sn)) := mul_le_mul_of_nonneg_left hLln hsn0.le
    have h2 : sn * (1 / (sn * sn)) = 1 / sn := by field_simp
    have h3 : 1 / sn ≤ 1 := by rw [div_le_one hsn0]; exact hsn1
    have h4 : sn * (ln - L) = -(sn * (L - ln)) := by ring
    linarith only [h1, h2, h3, h4]
  -- assemble
  have hexpand : (1 / sX) * ((X - ψ) + X * (M - L + γ) - l + SX)
      = sX - ψ / sX + sX * (M - L + γ) - l / sX + SX / sX := by
    rw [← hsXsq]; field_simp
  have hexpand' : (1 / sn) * (((n : ℝ) - ψ) + n * (M - ln + γ) - l + Sn)
      = sn - ψ / sn + sn * (M - ln + γ) - l / sn + Sn / sn := by
    rw [← hsnsq]; field_simp
  rw [hexpand, hexpand']
  have key : (sX - ψ / sX + sX * (M - L + γ) - l / sX + SX / sX)
      - (sn - ψ / sn + sn * (M - ln + γ) - l / sn + Sn / sn)
      = (sX - sn) + ψ * (1 / sn - 1 / sX) + (sX - sn) * (M - L + γ) + sn * (ln - L)
        + l * (1 / sn - 1 / sX) + (SX / sX - Sn / sn) := by ring
  have hP5' : SX / sX - Sn / sn ≤ 0 := by linarith only [hP5]
  have hup : (sX - sn) + ψ * (1 / sn - 1 / sX) + (sX - sn) * (M - L + γ) + sn * (ln - L)
        + l * (1 / sn - 1 / sX) + (SX / sX - Sn / sn) ≤ 30 := by
    calc (sX - sn) + ψ * (1 / sn - 1 / sX) + (sX - sn) * (M - L + γ) + sn * (ln - L)
          + l * (1 / sn - 1 / sX) + (SX / sX - Sn / sn)
        ≤ (1 : ℝ) + 2 + 18 + 0 + 6 + 0 :=
          add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hP1 hP2) hP3) hP6) hP4) hP5'
      _ ≤ 30 := by norm_num
  have hlow : -30 ≤ (sX - sn) + ψ * (1 / sn - 1 / sX) + (sX - sn) * (M - L + γ) + sn * (ln - L)
        + l * (1 / sn - 1 / sX) + (SX / sX - Sn / sn) := by
    calc (-30 : ℝ) ≤ 0 + 0 + (-18) + (-1) + 0 + (-1) := by norm_num
      _ ≤ (sX - sn) + ψ * (1 / sn - 1 / sX) + (sX - sn) * (M - L + γ) + sn * (ln - L)
          + l * (1 / sn - 1 / sX) + (SX / sX - Sn / sn) :=
          add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hQ1 hQ2) hQ3) hQ6) hQ4) hQ5
  constructor
  · linarith only [key, hup]
  · linarith only [key, hlow]

/-- For `L ≥ log 2` with `n = ⌊e^L⌋`, `|Φ(L) − Φ(log n)| ≤ 30`. -/
theorem weilLagFunctionReal_integerLag_interval {L : ℝ} (hL : Real.log 2 ≤ L) :
    weilLagFunctionReal L ≤ integerLag ⌊Real.exp L⌋₊ + 30 ∧
      integerLag ⌊Real.exp L⌋₊ - 30 ≤ weilLagFunctionReal L := by
  have hX2 : (2 : ℝ) ≤ Real.exp L := by
    rw [← Real.exp_log (by norm_num : (0:ℝ) < 2)]; exact Real.exp_le_exp.mpr hL
  have hX0 : 0 < Real.exp L := Real.exp_pos L
  have hnX : (⌊Real.exp L⌋₊ : ℝ) ≤ Real.exp L := Nat.floor_le hX0.le
  have hXn : Real.exp L < ⌊Real.exp L⌋₊ + 1 := Nat.lt_floor_add_one _
  have hn2 : 2 ≤ ⌊Real.exp L⌋₊ := Nat.le_floor (by exact_mod_cast hX2)
  have hn0 : (0 : ℝ) < ⌊Real.exp L⌋₊ := by exact_mod_cast (by omega : 0 < ⌊Real.exp L⌋₊)
  have hn1 : (1 : ℝ) ≤ ⌊Real.exp L⌋₊ := by exact_mod_cast (by omega : 1 ≤ ⌊Real.exp L⌋₊)
  have hL0 : 0 < L := by
    have := Real.log_pos (by norm_num : (1:ℝ) < 2); linarith
  have hlogn : Real.log ⌊Real.exp L⌋₊ ≤ L := by
    have := Real.log_le_log hn0 hnX; rwa [Real.log_exp] at this
  have hLlog : L ≤ Real.log ⌊Real.exp L⌋₊ + 1 / ⌊Real.exp L⌋₊ := by
    have h2 : Real.log (Real.exp L) - Real.log ⌊Real.exp L⌋₊
        = Real.log (Real.exp L / ⌊Real.exp L⌋₊) := by
      rw [Real.log_div hX0.ne' hn0.ne']
    have h3 : Real.log (Real.exp L / ⌊Real.exp L⌋₊) ≤ Real.exp L / ⌊Real.exp L⌋₊ - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h4 : Real.exp L / ⌊Real.exp L⌋₊ - 1 < 1 / ⌊Real.exp L⌋₊ := by
      rw [div_sub_one hn0.ne', div_lt_div_iff_of_pos_right hn0]; linarith
    rw [Real.log_exp] at h2
    linarith
  have hψ : Chebyshev.psi (Real.exp L) = Chebyshev.psi ⌊Real.exp L⌋₊ := by
    rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
  rw [weilLagFunctionReal_eq_prime_side hL0, hψ, integerLag_eq hn2,
    show Real.exp (-L / 2) = 1 / Real.sqrt (Real.exp L) by
      rw [neg_div, Real.exp_neg, Real.exp_half, one_div]]
  exact lag_interval_core hn2 hnX hXn hlogn hLlog

theorem weilLagFunctionReal_le_integerLag_add {L : ℝ} (hL : Real.log 2 ≤ L) :
    weilLagFunctionReal L ≤ integerLag ⌊Real.exp L⌋₊ + 30 :=
  (weilLagFunctionReal_integerLag_interval hL).1

theorem integerLag_sub_le_weilLagFunctionReal {L : ℝ} (hL : Real.log 2 ≤ L) :
    integerLag ⌊Real.exp L⌋₊ - 30 ≤ weilLagFunctionReal L :=
  (weilLagFunctionReal_integerLag_interval hL).2

/-! ## The integer criteria -/

theorem weilLagFunctionReal_neg (L : ℝ) : weilLagFunctionReal (-L) = weilLagFunctionReal L := by
  unfold weilLagFunctionReal; rw [weilLagFunction_neg]

/-- A bound on the integer lags bounds the lag function everywhere. -/
theorem weilLagFunctionReal_le_of_integerLag_le {M : ℝ}
    (hM : ∀ n : ℕ, 2 ≤ n → integerLag n ≤ M) (L : ℝ) :
    weilLagFunctionReal L ≤ max (M + 30) (Real.exp (Real.log 2 / 2) * lagWeightTotal) := by
  -- reduce to `L ≥ 0`
  suffices h : ∀ L : ℝ, 0 ≤ L →
      weilLagFunctionReal L ≤ max (M + 30) (Real.exp (Real.log 2 / 2) * lagWeightTotal) by
    rcases le_or_gt 0 L with hL | hL
    · exact h L hL
    · rw [← weilLagFunctionReal_neg]; exact h (-L) (by linarith)
  intro L hL
  rcases le_or_gt (Real.log 2) L with hL2 | hL2
  · refine le_max_of_le_left ?_
    have h1 := weilLagFunctionReal_le_integerLag_add hL2
    have hn2 : 2 ≤ ⌊Real.exp L⌋₊ := Nat.le_floor (by
      rw [Nat.cast_ofNat, ← Real.exp_log (by norm_num : (0:ℝ) < 2)]
      exact Real.exp_le_exp.mpr hL2)
    linarith [hM _ hn2]
  · refine le_max_of_le_right ?_
    have h1 := abs_weilLagFunctionReal_le L
    rw [abs_of_nonneg hL] at h1
    have h2 : Real.exp (L / 2) ≤ Real.exp (Real.log 2 / 2) := Real.exp_le_exp.mpr (by linarith)
    calc weilLagFunctionReal L ≤ |weilLagFunctionReal L| := le_abs_self _
      _ ≤ Real.exp (L / 2) * lagWeightTotal := h1
      _ ≤ Real.exp (Real.log 2 / 2) * lagWeightTotal := by
          gcongr; exact lagWeightTotal_nonneg

/-- A lower bound on the integer lags bounds the lag function from below everywhere. -/
theorem le_weilLagFunctionReal_of_le_integerLag {M : ℝ}
    (hM : ∀ n : ℕ, 2 ≤ n → M ≤ integerLag n) (L : ℝ) :
    min (M - 30) (-(Real.exp (Real.log 2 / 2) * lagWeightTotal)) ≤ weilLagFunctionReal L := by
  suffices h : ∀ L : ℝ, 0 ≤ L →
      min (M - 30) (-(Real.exp (Real.log 2 / 2) * lagWeightTotal)) ≤ weilLagFunctionReal L by
    rcases le_or_gt 0 L with hL | hL
    · exact h L hL
    · rw [← weilLagFunctionReal_neg]; exact h (-L) (by linarith)
  intro L hL
  rcases le_or_gt (Real.log 2) L with hL2 | hL2
  · refine min_le_of_left_le ?_
    have h1 := integerLag_sub_le_weilLagFunctionReal hL2
    have hn2 : 2 ≤ ⌊Real.exp L⌋₊ := Nat.le_floor (by
      rw [Nat.cast_ofNat, ← Real.exp_log (by norm_num : (0:ℝ) < 2)]
      exact Real.exp_le_exp.mpr hL2)
    linarith [hM _ hn2]
  · refine min_le_of_right_le ?_
    have h1 := abs_weilLagFunctionReal_le L
    rw [abs_of_nonneg hL] at h1
    have h2 : Real.exp (L / 2) ≤ Real.exp (Real.log 2 / 2) := Real.exp_le_exp.mpr (by linarith)
    have h3 : Real.exp (L / 2) * lagWeightTotal ≤ Real.exp (Real.log 2 / 2) * lagWeightTotal := by
      gcongr; exact lagWeightTotal_nonneg
    have h4 := neg_abs_le (weilLagFunctionReal L)
    linarith

/-- **RH ⟺ the integer lags are bounded below.** -/
theorem riemannHypothesis_iff_integerLag_bddBelow :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ n : ℕ, 2 ≤ n → M ≤ integerLag n := by
  constructor
  · intro h
    obtain ⟨M, hM⟩ := riemannHypothesis_iff_weilLagFunctionReal_bddBelow.mp h
    exact ⟨-M, fun n _ => hM _⟩
  · rintro ⟨M, hM⟩
    refine riemannHypothesis_of_le_weilLagFunctionReal
      (M := -(min (M - 30) (-(Real.exp (Real.log 2 / 2) * lagWeightTotal)))) (fun L => ?_)
    rw [neg_neg]
    exact le_weilLagFunctionReal_of_le_integerLag hM L

/-- **RH ⟺ the integer lags are bounded above.** -/
theorem riemannHypothesis_iff_integerLag_bddAbove :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ n : ℕ, 2 ≤ n → integerLag n ≤ M := by
  constructor
  · intro h
    obtain ⟨M, hM⟩ := riemannHypothesis_iff_weilLagFunctionReal_bddAbove.mp h
    exact ⟨M, fun n _ => hM _⟩
  · rintro ⟨M, hM⟩
    exact riemannHypothesis_of_weilLagFunctionReal_le (weilLagFunctionReal_le_of_integerLag_le hM)

/-- **The sharp integer lag criterion.**  RH holds iff `Φ(log n) ≤ 2 + γ − log 4π` for every
`n ≥ 2`. -/
theorem riemannHypothesis_iff_integerLag_le_sharp :
    RiemannHypothesis ↔ ∀ n : ℕ, 2 ≤ n → integerLag n ≤ poleSharpConstant := by
  constructor
  · intro h n _
    unfold integerLag
    have := norm_weilLagFunction_le_of_riemannHypothesis h (Real.log n)
    rw [weilLagFunction_eq_ofReal, Complex.norm_real, Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  · intro h
    exact riemannHypothesis_iff_integerLag_bddAbove.mpr ⟨poleSharpConstant, h⟩

/-- `a_1 = Φ(0) = 2 + γ − log 4π`. -/
theorem integerLag_one : integerLag 1 = poleSharpConstant := by
  unfold integerLag weilLagFunctionReal
  rw [Nat.cast_one, Real.log_one, weilLagFunction_zero, Complex.ofReal_re]

/-- Under RH every integer lag lies in `[−a_1, a_1]`. -/
theorem abs_integerLag_le_of_riemannHypothesis (h : RiemannHypothesis) (n : ℕ) :
    |integerLag n| ≤ poleSharpConstant := by
  unfold integerLag
  have := norm_weilLagFunction_le_of_riemannHypothesis h (Real.log n)
  rwa [weilLagFunction_eq_ofReal, Complex.norm_real, Real.norm_eq_abs] at this

/-- **RH ⟺ the integer lag sequence is maximised at `n = 1`.** -/
theorem riemannHypothesis_iff_integerLag_le_one :
    RiemannHypothesis ↔ ∀ n : ℕ, 1 ≤ n → integerLag n ≤ integerLag 1 := by
  rw [integerLag_one, riemannHypothesis_iff_integerLag_le_sharp]
  constructor
  · intro h n hn
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · have : n = 1 := by omega
      rw [this, integerLag_one]
    · exact h n h2
  · intro h n hn
    exact h n (by omega)

/-- **The integer lag dichotomy.**  Either every integer lag lies in `[−a_1, a_1]` (and RH holds),
or the integer lags are unbounded above and unbounded below (and RH fails). -/
theorem integerLag_dichotomy :
    (∀ n : ℕ, |integerLag n| ≤ poleSharpConstant) ∨
      ((∀ M : ℝ, ∃ n : ℕ, 2 ≤ n ∧ M < integerLag n) ∧
        (∀ M : ℝ, ∃ n : ℕ, 2 ≤ n ∧ integerLag n < M)) := by
  by_cases h : RiemannHypothesis
  · exact Or.inl (abs_integerLag_le_of_riemannHypothesis h)
  · refine Or.inr ⟨fun M => ?_, fun M => ?_⟩
    · by_contra hc
      push Not at hc
      exact h (riemannHypothesis_iff_integerLag_bddAbove.mpr ⟨M, hc⟩)
    · by_contra hc
      push Not at hc
      exact h (riemannHypothesis_iff_integerLag_bddBelow.mpr ⟨M, hc⟩)

/-- **The integer lag inequality.**  RH holds iff, for every `n ≥ 2`,

`(n − ψ(n)) + n·(Σ_{m≤n} Λ(m)/m − log n + γ) − log 2π + S(n) ≤ (2 + γ − log 4π)·√n`. -/
theorem riemannHypothesis_iff_integerLagInequality :
    RiemannHypothesis ↔ ∀ n : ℕ, 2 ≤ n →
      ((n : ℝ) - Chebyshev.psi n) + n * (mertensSum n - Real.log n + eulerMascheroniConstant)
        - Real.log (2 * π) + trivialZeroSeriesReal n ≤ poleSharpConstant * Real.sqrt n := by
  rw [riemannHypothesis_iff_integerLag_le_sharp]
  refine forall_congr' fun n => forall_congr' fun hn => ?_
  rw [integerLag_eq hn]
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  rw [one_div, inv_mul_le_iff₀ hs, mul_comm (Real.sqrt (n : ℝ)) poleSharpConstant]

end

end RHTower
