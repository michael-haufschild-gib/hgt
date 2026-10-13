import GaloisForLFunctions.RHTower.WeilLagPowerGapSampling
import GaloisForLFunctions.RHTower.WeilLagWindowMeanExceptional

/-!
# Endpoint-monotone lag slope and two-step exceptional power-gap sampling

This file refines the discrete lag-bracket slope law of `WeilLagPowerGapSampling` in two directions:

1. **Exact cancellation of linear drift and endpoint-only monotonicity:**
   In `lagBracketSlope_succ_sub`, the linear drift `−d/(d(d + 1)) + 1/(d + 1) = 0` cancels
   identically at every step `d`, leaving the exact difference
   `Q(d + 1) − Q(d) = ψ(d)/(d(d + 1)) − log((d + 1)/d)` (`lagBracketSlope_succ_sub_eq`).
   Telescoping over `k ≤ d < n` yields
   `Q(n) − Q(k) = (∑_{k ≤ d < n} ψ(d)/(d(d + 1))) − log(n/k)` (`lagBracketSlope_sub_eq_sum_psi`).
   Because `ψ(d) ≥ 0` is monotone nondecreasing and `∑_{k ≤ d < n} 1/(d(d + 1)) = (n − k)/(k n)`
   (`sum_Ico_inv_mul_succ`), the difference `Q(n) − Q(k)` is trapped between its left-endpoint and
   right-endpoint values with no dependence on interior primes `k < d < n`
   (`lagBracketSlope_sub_bounds_of_monotone`, `lagBracketSlope_sub_endpoint_sandwich`).
   Passing to the lag bracket `E(n)` and integer lag `a_n = Φ(log n)` gives the endpoint-only
   sandwiches `lagBracket_sub_ratio_mul_bounds_of_endpoints` and
   `integerLag_sub_ratio_mul_bounds_of_endpoints`.

2. **Two-step supremum fixed-point bootstrap with exponential exceptions:**
   Using the zero real-part supremum `α = zeroReSup − 1/2` and the exceptional growth criteria
   of `WeilLagWindowMeanExceptional`, we eliminate the `⌈1/δ⌉`-step induction of
   `WeilLagPowerGapSampling` and allow an exponentially thin set `S` of exceptional log-scales
   (`∫_S e^{κ u} du < ∞`, `κ > 0`) on which the power-gap sampling window
   `A ∩ [⌊e^u⌋ − K⌊e^u⌋^{1 − δ}, ⌊e^u⌋]` may fail to meet `A`:
   * **Step 1 (Chebyshev `β = 1`):** proves `α < 1/2`.
   * **Step 2 (Von Koch at `e = α < 1/2`):** proves `α ≤ max(max c 0, α − δ/2, α − κ, 0)`, which
     directly forces `α ≤ max(0, c)` (`abs_re_sub_half_le_of_powerGaps_integerLag_le_rpow_except`,
     `abs_re_sub_half_le_of_powerGaps_neg_rpow_le_integerLag_except`).
-/

open Real Filter Topology MeasureTheory Set
open ArithmeticFunction (vonMangoldt)

namespace RHTower

noncomputable section

/-! ## Exact positivity and endpoint monotonicity of `lagBracketSlope` -/

/-- Cancellation of the linear drift in `lagBracketSlope_succ_sub`:
`Q(d + 1) − Q(d) = ψ(d)/(d(d + 1)) − log((d + 1)/d)`. -/
theorem lagBracketSlope_succ_sub_eq {d : ℕ} (hd : 1 ≤ d) :
    lagBracketSlope (d + 1) - lagBracketSlope d =
      Chebyshev.psi d / ((d : ℝ) * (d + 1)) - Real.log (((d : ℝ) + 1) / d) := by
  rw [lagBracketSlope_succ_sub hd]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  field_simp
  ring

/-- Exact telescoping of `Q(n) − Q(k)` into the positive monotone sum `Σ_{k ≤ d < n} ψ(d)/(d(d+1))`
minus `log(n/k)`. -/
theorem lagBracketSlope_sub_eq_sum_psi {k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    lagBracketSlope n - lagBracketSlope k =
      (∑ d ∈ Finset.Ico k n, Chebyshev.psi d / ((d : ℝ) * (d + 1))) - Real.log ((n : ℝ) / k) := by
  induction n, hkn using Nat.le_induction with
  | base =>
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    simp [div_self hk0.ne']
  | succ n hkn ih =>
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hn1 : 1 ≤ n := le_trans hk hkn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hlog : Real.log (((n + 1 : ℕ) : ℝ) / k) =
        Real.log ((n : ℝ) / k) + Real.log (((n : ℝ) + 1) / n) := by
      push_cast
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1
      field_simp
    have hstep := lagBracketSlope_succ_sub_eq hn1
    rw [Finset.sum_Ico_succ_top hkn, hlog]
    linarith

/-- Exact telescoping of `Σ_{k ≤ d < n} 1/(d(d + 1)) = (n − k)/(k n)`. -/
theorem sum_Ico_inv_mul_succ {k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∑ d ∈ Finset.Ico k n, (1 / ((d : ℝ) * (d + 1))) = ((n : ℝ) - k) / ((k : ℝ) * n) := by
  induction n, hkn using Nat.le_induction with
  | base => simp
  | succ n hkn ih =>
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (le_trans hk hkn)
    rw [Finset.sum_Ico_succ_top hkn, ih]
    push_cast
    field_simp
    ring

/-- **Exact endpoint monotonicity sandwich for `lagBracketSlope`.**
Because `ψ(d)` is nondecreasing on `[k, n)` and `Σ 1/(d(d+1)) = (n − k)/(kn)`, the slope difference
`Q(n) − Q(k)` is trapped between its left-endpoint and right-endpoint values, with no dependence on
interior primes. -/
theorem lagBracketSlope_sub_bounds_of_monotone {k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    Chebyshev.psi k * (((n : ℝ) - k) / ((k : ℝ) * n)) - Real.log ((n : ℝ) / k) ≤
      lagBracketSlope n - lagBracketSlope k ∧
    lagBracketSlope n - lagBracketSlope k ≤
      Chebyshev.psi n * (((n : ℝ) - k) / ((k : ℝ) * n)) - Real.log ((n : ℝ) / k) := by
  rw [lagBracketSlope_sub_eq_sum_psi hk hkn]
  have hlow : ∀ d ∈ Finset.Ico k n,
      Chebyshev.psi k * (1 / ((d : ℝ) * (d + 1))) ≤ Chebyshev.psi d / ((d : ℝ) * (d + 1)) := by
    intro d hd
    obtain ⟨hkd, _⟩ := Finset.mem_Ico.mp hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (le_trans hk hkd)
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (Chebyshev.psi_mono (by exact_mod_cast hkd)) (by positivity)
  have hup : ∀ d ∈ Finset.Ico k n,
      Chebyshev.psi d / ((d : ℝ) * (d + 1)) ≤ Chebyshev.psi n * (1 / ((d : ℝ) * (d + 1))) := by
    intro d hd
    obtain ⟨hkd, hdn⟩ := Finset.mem_Ico.mp hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (le_trans hk hkd)
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (Chebyshev.psi_mono (by exact_mod_cast hdn.le)) (by positivity)
  have h1 := Finset.sum_le_sum hlow
  have h2 := Finset.sum_le_sum hup
  rw [← Finset.mul_sum, sum_Ico_inv_mul_succ hk hkn] at h1 h2
  exact ⟨by linarith, by linarith⟩

/-- For `1 ≤ k ≤ n`, `1 − k/n ≤ log(n/k) ≤ n/k − 1`. -/
theorem sub_le_log_div_and_log_div_le {k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    ((n : ℝ) - k) / n ≤ Real.log ((n : ℝ) / k) ∧
      Real.log ((n : ℝ) / k) ≤ ((n : ℝ) - k) / k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (le_trans hk hkn)
  constructor
  · have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (k : ℝ) / n by positivity)
    have hinv : Real.log ((k : ℝ) / n) = -Real.log ((n : ℝ) / k) := by
      rw [← Real.log_inv, inv_div]
    have hsub : (k : ℝ) / n - 1 = -(((n : ℝ) - k) / n) := by field_simp; ring
    linarith
  · have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (n : ℝ) / k by positivity)
    have hsub : (n : ℝ) / k - 1 = ((n : ℝ) - k) / k := by field_simp
    linarith

/-- **Quadratic-defect endpoint sandwich for `lagBracketSlope`.**
For `1 ≤ k ≤ n`, the lower bound on `Q(n) − Q(k)` depends ONLY on the left endpoint `ψ(k) − k`,
and the upper bound depends ONLY on the right endpoint `ψ(n) − n`, up to the quadratic log defect
`(n − k)²/(kn)`. -/
theorem lagBracketSlope_sub_endpoint_sandwich {k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    (Chebyshev.psi k - k) / k * (((n : ℝ) - k) / n) - ((n : ℝ) - k) ^ 2 / ((k : ℝ) * n) ≤
      lagBracketSlope n - lagBracketSlope k ∧
    lagBracketSlope n - lagBracketSlope k ≤
      (Chebyshev.psi n - n) / n * (((n : ℝ) - k) / k) + ((n : ℝ) - k) ^ 2 / ((k : ℝ) * n) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (le_trans hk hkn)
  obtain ⟨hm1, hm2⟩ := lagBracketSlope_sub_bounds_of_monotone hk hkn
  obtain ⟨hl1, hl2⟩ := sub_le_log_div_and_log_div_le hk hkn
  have e1 : Chebyshev.psi k * (((n : ℝ) - k) / ((k : ℝ) * n)) - ((n : ℝ) - k) / k =
      (Chebyshev.psi k - k) / k * (((n : ℝ) - k) / n) - ((n : ℝ) - k) ^ 2 / ((k : ℝ) * n) := by
    field_simp
    ring
  have e2 : Chebyshev.psi n * (((n : ℝ) - k) / ((k : ℝ) * n)) - ((n : ℝ) - k) / n =
      (Chebyshev.psi n - n) / n * (((n : ℝ) - k) / k) + ((n : ℝ) - k) ^ 2 / ((k : ℝ) * n) := by
    field_simp
    ring
  exact ⟨by linarith, by linarith⟩

/-- **Endpoint-only sandwich for the lag bracket `E(n) − (n/k) E(k)`.**
For `1 ≤ k ≤ n ≤ 2k`, the lower bound depends only on `ψ(k) − k` and the upper bound depends only
on `ψ(n) − n`, with no dependence on interior primes `k < d < n`. -/
theorem lagBracket_sub_ratio_mul_bounds_of_endpoints {k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (hn2k : n ≤ 2 * k) :
    (Chebyshev.psi k - k) / k * ((n : ℝ) - k) - ((n : ℝ) - k) ^ 2 / k - 18 ≤
      lagBracket n - ((n : ℝ) / k) * lagBracket k ∧
    lagBracket n - ((n : ℝ) / k) * lagBracket k ≤
      (Chebyshev.psi n - n) / k * ((n : ℝ) - k) + ((n : ℝ) - k) ^ 2 / k + 18 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (le_trans hk hkn)
  have hn2k' : (n : ℝ) ≤ 2 * k := by exact_mod_cast hn2k
  obtain ⟨hs1, hs2⟩ := lagBracketSlope_sub_endpoint_sandwich hk hkn
  have hm1 := mul_le_mul_of_nonneg_left hs1 hn0.le
  have hm2 := mul_le_mul_of_nonneg_left hs2 hn0.le
  have he1 : (n : ℝ) * ((Chebyshev.psi k - k) / k * (((n : ℝ) - k) / n) -
      ((n : ℝ) - k) ^ 2 / ((k : ℝ) * n)) =
      (Chebyshev.psi k - k) / k * ((n : ℝ) - k) - ((n : ℝ) - k) ^ 2 / k := by
    field_simp
  have he2 : (n : ℝ) * ((Chebyshev.psi n - n) / n * (((n : ℝ) - k) / k) +
      ((n : ℝ) - k) ^ 2 / ((k : ℝ) * n)) =
      (Chebyshev.psi n - n) / k * ((n : ℝ) - k) + ((n : ℝ) - k) ^ 2 / k := by
    field_simp
  rw [he1] at hm1
  rw [he2] at hm2
  have hE : ∀ j : ℕ, 1 ≤ j →
      lagBracket j = j * lagBracketSlope j + trivialZeroSeriesReal j - Real.log (2 * Real.pi) := by
    intro j hj
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
    unfold lagBracketSlope; field_simp; ring
  have hS : ∀ j : ℕ, 1 ≤ j → |trivialZeroSeriesReal j - Real.log (2 * Real.pi)| ≤ 6 := by
    intro j hj
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have h0 := trivialZeroSeriesReal_nonneg hj1
    have h1 := trivialZeroSeriesReal_le_one hj1
    have hlog2π : Real.log (2 * Real.pi) ≤ 6 := by
      have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)
      have := Real.pi_lt_d2
      linarith
    have hlog2π0 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
    rw [abs_le]; constructor <;> linarith
  have hdecomp : lagBracket n - ((n : ℝ) / k) * lagBracket k =
      n * (lagBracketSlope n - lagBracketSlope k) +
        (trivialZeroSeriesReal n - Real.log (2 * Real.pi)) -
          ((n : ℝ) / k) * (trivialZeroSeriesReal k - Real.log (2 * Real.pi)) := by
    rw [hE n (le_trans hk hkn), hE k hk]; field_simp; ring
  have hratio : (n : ℝ) / k ≤ 2 := by rw [div_le_iff₀ hk0]; linarith
  have hratio0 : 0 ≤ (n : ℝ) / k := by positivity
  have hB1 := abs_le.mp (hS n (le_trans hk hkn))
  have hB2 : |((n : ℝ) / k) * (trivialZeroSeriesReal k - Real.log (2 * Real.pi))| ≤ 12 := by
    rw [abs_mul, abs_of_nonneg hratio0]
    nlinarith [hS k hk, abs_nonneg (trivialZeroSeriesReal k - Real.log (2 * Real.pi))]
  have hB2' := abs_le.mp hB2
  rw [hdecomp]
  exact ⟨by linarith, by linarith⟩

/-- **Endpoint-only sandwich for the integer lag `a_n − (√n/√k) a_k`.**
For `2 ≤ k ≤ n ≤ 2k`, the lower bound depends only on the left endpoint `ψ(k) − k` and the upper
bound depends only on the right endpoint `ψ(n) − n`. -/
theorem integerLag_sub_ratio_mul_bounds_of_endpoints {k n : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n)
    (hn2k : n ≤ 2 * k) :
    ((Chebyshev.psi k - k) / k * ((n : ℝ) - k) - ((n : ℝ) - k) ^ 2 / k - 18) / Real.sqrt n ≤
      integerLag n - (Real.sqrt n / Real.sqrt k) * integerLag k ∧
    integerLag n - (Real.sqrt n / Real.sqrt k) * integerLag k ≤
      ((Chebyshev.psi n - n) / k * ((n : ℝ) - k) + ((n : ℝ) - k) ^ 2 / k + 18) / Real.sqrt n := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (le_trans (by omega : 1 ≤ k) hkn)
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk0
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hid : integerLag n - (Real.sqrt n / Real.sqrt k) * integerLag k =
      (lagBracket n - ((n : ℝ) / k) * lagBracket k) / Real.sqrt n := by
    rw [integerLag_eq_lagBracket hk, integerLag_eq_lagBracket (le_trans hk hkn)]
    have hnn : (n : ℝ) = Real.sqrt n * Real.sqrt n := (Real.mul_self_sqrt hn0.le).symm
    have hkk : (k : ℝ) = Real.sqrt k * Real.sqrt k := (Real.mul_self_sqrt hk0.le).symm
    rw [show ((n : ℝ) / k) = (Real.sqrt n * Real.sqrt n) / (Real.sqrt k * Real.sqrt k) by
      rw [← hnn, ← hkk]]
    field_simp
  rw [hid]
  obtain ⟨h1, h2⟩ := lagBracket_sub_ratio_mul_bounds_of_endpoints (by omega) hkn hn2k
  exact ⟨div_le_div_of_nonneg_right h1 hsn.le, div_le_div_of_nonneg_right h2 hsn.le⟩

/-! ## Exceptional power-gap transport and two-step fixed-point bootstrap -/

/-- **Pointwise power-gap transport of `integerLag`.**
At a single integer `n` satisfying `4 ≤ n` and `K n^{−δ} ≤ ½`, if `k ≤ n` satisfies
`n − k ≤ K n^{1−δ}` and `|ψ(d) − d| ≤ C d^β` for `1 ≤ d`, then `2 ≤ k`, `√n/√k ≤ 2`, and
`|a_n − (√n/√k) a_k| ≤ (20 + 4KC)(1 + n^{β − ½ − δ})`. -/
theorem abs_integerLag_sub_le_rpow_of_sample {K δ C β : ℝ} {k n : ℕ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hβ : 0 ≤ β) (hn4 : 4 ≤ n)
    (hKn : K * (n : ℝ) ^ (-δ) ≤ 1 / 2) (hkn : k ≤ n)
    (hgapn : (n : ℝ) - k ≤ K * (n : ℝ) ^ (1 - δ))
    (hψ : ∀ N : ℕ, 1 ≤ N → |Chebyshev.psi N - N| ≤ C * (N : ℝ) ^ β) :
    2 ≤ k ∧ Real.sqrt n / Real.sqrt k ≤ 2 ∧
      |integerLag n - (Real.sqrt n / Real.sqrt k) * integerLag k| ≤
        (20 + 4 * K * C) + (20 + 4 * K * C) * (n : ℝ) ^ (β - 1 / 2 - δ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hsplit : (n : ℝ) ^ (1 - δ) = (n : ℝ) ^ (-δ) * n := by
    rw [show (1 : ℝ) - δ = -δ + 1 by ring, Real.rpow_add hn0, Real.rpow_one]
  have hhalf : K * (n : ℝ) ^ (1 - δ) ≤ n / 2 := by
    rw [hsplit, ← mul_assoc]; nlinarith
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hn2k' : (n : ℝ) ≤ 2 * k := by linarith
  have hn2k : n ≤ 2 * k := by exact_mod_cast hn2k'
  have hk2 : 2 ≤ k := by
    have : (2 : ℝ) ≤ k := by
      have : (4 : ℝ) ≤ n := by exact_mod_cast hn4
      linarith
    exact_mod_cast this
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  refine ⟨hk2, sqrt_div_sqrt_le_two_of_le_two_mul (by omega) hn2k, ?_⟩
  have hB : ∀ d : ℕ, k ≤ d → d < n → |Chebyshev.psi d - d| ≤ C * (n : ℝ) ^ β := by
    intro d hkd hdn
    refine (hψ d (by omega)).trans (mul_le_mul_of_nonneg_left ?_ hC)
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hdn.le) hβ
  have hw := abs_integerLag_sub_ratio_mul_le hk2 hkn hn2k (by positivity) hB
  set y : ℝ := (n : ℝ) ^ (β - 1 / 2 - δ) with hy
  have hy0 : 0 ≤ y := by positivity
  have hsn : Real.sqrt n = (n : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have hsn0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hsn1 : 1 ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hn1
  have hkey : (n : ℝ) ^ (1 - δ) * (n : ℝ) ^ β = y * ((n : ℝ) * Real.sqrt n) := by
    rw [hy, hsn, ← Real.rpow_add hn0, show (n : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) =
      (n : ℝ) ^ ((1 : ℝ) + 1 / 2) by rw [Real.rpow_add hn0, Real.rpow_one],
      ← Real.rpow_add hn0]
    ring_nf
  have herr : 2 * ((n : ℝ) - k) * (C * (n : ℝ) ^ β) / k / Real.sqrt n ≤ 4 * K * C * y := by
    rw [div_div, div_le_iff₀ (by positivity)]
    calc 2 * ((n : ℝ) - k) * (C * (n : ℝ) ^ β)
        ≤ 2 * (K * (n : ℝ) ^ (1 - δ)) * (C * (n : ℝ) ^ β) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity); linarith
      _ = 2 * K * C * ((n : ℝ) ^ (1 - δ) * (n : ℝ) ^ β) := by ring
      _ = 2 * K * C * y * ((n : ℝ) * Real.sqrt n) := by rw [hkey]; ring
      _ ≤ 2 * K * C * y * ((2 * k) * Real.sqrt n) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right hn2k' hsn0.le
      _ = 4 * K * C * y * (k * Real.sqrt n) := by ring
  have h20 : 20 / Real.sqrt n ≤ 20 := by
    rw [div_le_iff₀ hsn0]; nlinarith
  rw [add_div] at hw
  have hKC : 0 ≤ K * C := mul_nonneg hK hC
  have hy1 : 4 * K * C * y ≤ (20 + 4 * K * C) * y := by
    apply mul_le_mul_of_nonneg_right _ hy0; linarith
  linarith

/-- **One round of exceptional power-gap upper transport.**
Given `|ψ(N) − N| ≤ C N^β` (`β ≥ 0`) and `a_k ≤ M + M k^c` on `A` (`M ≥ 0`), if outside `S` the
integer `⌊e^u⌋` eventually has a sample in `A ∩ [⌊e^u⌋ − K⌊e^u⌋^{1−δ}, ⌊e^u⌋]`, then
`Φ(L) ≤ M' e^{max(max c 0, max(β − ½ − δ, 0)) L}` for all `L ≥ 0` outside `S`. -/
theorem exists_weilLagFunctionReal_le_exp_of_powerGaps_except {A : Set ℕ} {M c K δ C β : ℝ}
    {S : Set ℝ} (hM0 : 0 ≤ M) (hδ : 0 < δ) (hK : 0 ≤ K) (hC : 0 ≤ C) (hβ : 0 ≤ β)
    (hA : ∀ k ∈ A, 2 ≤ k → integerLag k ≤ M + M * (k : ℝ) ^ c)
    (hψ : ∀ N : ℕ, 1 ≤ N → |Chebyshev.psi N - N| ≤ C * (N : ℝ) ^ β)
    (hgap : ∀ᶠ u : ℝ in atTop, u ∉ S →
      ∃ k ∈ A, k ≤ ⌊Real.exp u⌋₊ ∧
        (⌊Real.exp u⌋₊ : ℝ) - k ≤ K * (⌊Real.exp u⌋₊ : ℝ) ^ (1 - δ)) :
    ∃ M' : ℝ, ∀ L : ℝ, 0 ≤ L → L ∉ S →
      weilLagFunctionReal L ≤ M' * Real.exp (max (max c 0) (max (β - 1 / 2 - δ) 0) * L) := by
  set a := max (max c 0) (max (β - 1 / 2 - δ) 0) with hadef
  have ha0 : 0 ≤ a := le_trans (le_max_right _ _) (le_max_right _ _)
  have hca : c ≤ a := le_trans (le_max_left _ _) (le_max_left _ _)
  have hba : β - 1 / 2 - δ ≤ a := le_trans (le_max_left _ _) (le_max_right _ _)
  have hlim : Tendsto (fun n : ℕ => K * (n : ℝ) ^ (-δ)) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop).const_mul K
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (hlim.eventually (eventually_le_nhds
    (show (0 : ℝ) < 1 / 2 by norm_num)))
  set u₁ : ℝ := Real.log (max (N₂ : ℝ) 4 + 1) with hu₁
  obtain ⟨u₀, hu₀⟩ := eventually_atTop.mp (hgap.and (eventually_ge_atTop u₁))
  set D : ℝ := 20 + 4 * K * C with hD
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hW := lagWeightTotal_nonneg
  refine ⟨max (4 * M + 2 * D + 30) (Real.exp (|u₀| / 2) * lagWeightTotal), fun L hL hLS => ?_⟩
  rcases le_or_gt u₀ L with hLu | hLu
  · obtain ⟨hgapL, hLu₁⟩ := hu₀ L hLu
    obtain ⟨k, hkA, hkn, hgapn⟩ := hgapL hLS
    set n : ℕ := ⌊Real.exp L⌋₊ with hn
    have hexp : max (N₂ : ℝ) 4 + 1 ≤ Real.exp L := by
      rw [← Real.exp_log (by positivity : (0 : ℝ) < max (N₂ : ℝ) 4 + 1)]
      exact Real.exp_le_exp.mpr hLu₁
    have hn_ge : max N₂ 4 ≤ n := by
      apply Nat.le_floor
      rw [Nat.cast_max, Nat.cast_ofNat]
      linarith
    have hn4 : 4 ≤ n := le_trans (le_max_right _ _) hn_ge
    have hnN₂ : N₂ ≤ n := le_trans (le_max_left _ _) hn_ge
    have hL2 : Real.log 2 ≤ L := by
      have : (2 : ℝ) ≤ max (N₂ : ℝ) 4 + 1 := by linarith [le_max_right (N₂ : ℝ) 4]
      exact (Real.log_le_log (by norm_num) this).trans hLu₁
    obtain ⟨hk2, hr, habs⟩ := abs_integerLag_sub_le_rpow_of_sample hK hC hβ hn4 (hN₂ n hnN₂)
      hkn hgapn hψ
    have hr0 : 0 ≤ Real.sqrt n / Real.sqrt k := by positivity
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have hnL : (n : ℝ) ≤ Real.exp L := Nat.floor_le (Real.exp_pos L).le
    have hkc : (k : ℝ) ^ c ≤ Real.exp (a * L) := by
      calc (k : ℝ) ^ c ≤ (k : ℝ) ^ a := Real.rpow_le_rpow_of_exponent_le hk1 hca
        _ ≤ (n : ℝ) ^ a := Real.rpow_le_rpow (by positivity) (by exact_mod_cast hkn) ha0
        _ ≤ (Real.exp L) ^ a := Real.rpow_le_rpow (by positivity) hnL ha0
        _ = Real.exp (a * L) := by rw [← Real.exp_mul, mul_comm]
    have hnb : (n : ℝ) ^ (β - 1 / 2 - δ) ≤ Real.exp (a * L) := by
      calc (n : ℝ) ^ (β - 1 / 2 - δ) ≤ (n : ℝ) ^ a := Real.rpow_le_rpow_of_exponent_le hn1 hba
        _ ≤ (Real.exp L) ^ a := Real.rpow_le_rpow (by positivity) hnL ha0
        _ = Real.exp (a * L) := by rw [← Real.exp_mul, mul_comm]
    have he1 : 1 ≤ Real.exp (a * L) := Real.one_le_exp (mul_nonneg ha0 hL)
    have hak : integerLag k ≤ 2 * M * Real.exp (a * L) := by
      have := hA k hkA hk2
      nlinarith
    have h1 : (Real.sqrt n / Real.sqrt k) * integerLag k ≤ 4 * M * Real.exp (a * L) := by
      have h1a := mul_le_mul_of_nonneg_left hak hr0
      have h1b : (Real.sqrt n / Real.sqrt k) * (2 * M * Real.exp (a * L)) ≤
          2 * (2 * M * Real.exp (a * L)) :=
        mul_le_mul_of_nonneg_right hr (by positivity)
      linarith
    have h2 : integerLag n ≤ (4 * M + 2 * D) * Real.exp (a * L) := by
      have := (abs_le.mp habs).2
      rw [← hD] at this
      nlinarith
    have hcmp := weilLagFunctionReal_le_integerLag_add hL2
    have h3 : weilLagFunctionReal L ≤ (4 * M + 2 * D + 30) * Real.exp (a * L) := by nlinarith
    exact h3.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · have h1 := abs_weilLagFunctionReal_le L
    rw [abs_of_nonneg hL] at h1
    have h2 : Real.exp (L / 2) ≤ Real.exp (|u₀| / 2) :=
      Real.exp_le_exp.mpr (by linarith [le_abs_self u₀])
    have h3 : 1 ≤ Real.exp (a * L) := Real.one_le_exp (mul_nonneg ha0 hL)
    have h4 : weilLagFunctionReal L ≤ Real.exp (|u₀| / 2) * lagWeightTotal :=
      (le_abs_self _).trans (h1.trans (mul_le_mul_of_nonneg_right h2 hW))
    have h5 : 0 ≤ max (4 * M + 2 * D + 30) (Real.exp (|u₀| / 2) * lagWeightTotal) :=
      le_trans (by positivity) (le_max_right _ _)
    calc weilLagFunctionReal L
        ≤ max (4 * M + 2 * D + 30) (Real.exp (|u₀| / 2) * lagWeightTotal) :=
          h4.trans (le_max_right _ _)
      _ ≤ max (4 * M + 2 * D + 30) (Real.exp (|u₀| / 2) * lagWeightTotal) * Real.exp (a * L) :=
          le_mul_of_one_le_right h5 h3

/-- **Power-gap upper lag sampling with exponential exceptions forces the zero-free half-plane.**
Let `a_k ≤ M + M k^c` on `A` (`M ≥ 0`), and suppose outside a measurable set `S` of log-scales with
`∫_S e^{κu} du < ∞` (`κ > 0`) the integer `⌊e^u⌋` eventually has a sample in
`A ∩ [⌊e^u⌋ − K⌊e^u⌋^{1−δ}, ⌊e^u⌋]` (`δ > 0`). Then every zero satisfies
`|Re ρ − ½| ≤ max(0, c)`. -/
theorem abs_re_sub_half_le_of_powerGaps_integerLag_le_rpow_except {A : Set ℕ} {M c K δ κ : ℝ}
    {S : Set ℝ} (hM0 : 0 ≤ M) (hδ : 0 < δ) (hK : 0 ≤ K) (hκ : 0 < κ) (hS : MeasurableSet S)
    (hSint : IntegrableOn (fun u => Real.exp (κ * u)) S)
    (hA : ∀ k ∈ A, 2 ≤ k → integerLag k ≤ M + M * (k : ℝ) ^ c)
    (hgap : ∀ᶠ u : ℝ in atTop, u ∉ S →
      ∃ k ∈ A, k ≤ ⌊Real.exp u⌋₊ ∧
        (⌊Real.exp u⌋₊ : ℝ) - k ≤ K * (⌊Real.exp u⌋₊ : ℝ) ^ (1 - δ))
    (q : XiZeroCopy) : |(q.1 : ℂ).re - 1 / 2| ≤ max 0 c := by
  haveI : Nonempty XiZeroCopy := ⟨q⟩
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = zeroReSup - 1 / 2 := ⟨_, rfl⟩
  have hXi : XiZeroHalfPlaneBound α := by
    intro ρ hρ
    obtain ⟨q', rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
    have := re_le_zeroReSup q'
    rw [hαdef]; linarith
  have hαall : ∀ q' : XiZeroCopy, |(q'.1 : ℂ).re - 1 / 2| ≤ α :=
    abs_re_sub_half_le_of_xiZeroHalfPlaneBound hXi
  have hstrip : ∀ q' : XiZeroCopy, (q'.1 : ℂ).re ≤ 1 / 2 + α := fun q' => by
    linarith [(abs_le.mp (hαall q')).2]
  have hα0 : 0 ≤ α := le_trans (abs_nonneg _) (hαall q)
  have hαh : α ≤ 1 / 2 := by
    have := zeroReSup_le (fun q' : XiZeroCopy => (xiZeroCopy_re_lt_one q').le)
    rw [hαdef]; linarith
  by_cases hc : 1 / 2 ≤ max 0 c
  · exact (hαall q).trans (by linarith)
  push Not at hc
  -- Step 1 (Chebyshev β = 1): prove α < 1/2
  have hψ1 : ∀ N : ℕ, 1 ≤ N → |Chebyshev.psi N - N| ≤ 6 * (N : ℝ) ^ (1 : ℝ) := by
    intro N _
    rw [Real.rpow_one]
    have h1 := psi_nat_le_six_mul N
    have h0 := psi_nat_nonneg N
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    rw [abs_le]; constructor <;> linarith
  obtain ⟨M₁, hM₁⟩ := exists_weilLagFunctionReal_le_exp_of_powerGaps_except hM0 hδ hK
    (by norm_num) (by norm_num) hA hψ1 hgap
  set a₁ := max (max c 0) (max ((1 : ℝ) - 1 / 2 - δ) 0) with ha₁
  have ha₁0 : 0 ≤ a₁ := le_trans (le_max_right _ _) (le_max_right _ _)
  have hg₁ : ∀ q' : XiZeroCopy, (q'.1 : ℂ).re ≤ 1 / 2 + max (max a₁ (α - κ)) 0 := fun q' =>
    re_le_half_add_of_weilLagFunctionReal_le_exp_except ha₁0 hS hSint hM₁
      (fun u hu => abs_weilLagFunctionReal_le_of_strip hstrip hu) q'
  have hsup₁ := zeroReSup_le hg₁
  have hle₁ : α ≤ max (max a₁ (α - κ)) 0 := by linarith
  have hαlt : α < 1 / 2 := by
    have hc1 : max c 0 < 1 / 2 := by rwa [max_comm]
    have hc2 : max ((1 : ℝ) - 1 / 2 - δ) 0 < 1 / 2 := max_lt (by linarith) (by norm_num)
    have hc3 : a₁ < 1 / 2 := max_lt hc1 hc2
    have hc4 : max a₁ (α - κ) < 1 / 2 := max_lt hc3 (by linarith)
    exact lt_of_le_of_lt hle₁ (max_lt hc4 (by norm_num))
  -- Step 2 (Von Koch at e = α < 1/2): prove α ≤ max 0 c
  obtain ⟨C₂, hC₂0, hC₂⟩ := Sieve.exists_chebyshev_error_power_bound_of_xiZeroHalfPlaneBound
    hα0 hαlt hXi (show 0 < δ / 2 by positivity)
  have hψ2 : ∀ N : ℕ, 1 ≤ N → |Chebyshev.psi N - N| ≤ C₂ * (N : ℝ) ^ (1 / 2 + α + δ / 2) := by
    intro N hN
    rw [psi_natCast_eq_sum_Icc_one]
    exact hC₂ N hN
  obtain ⟨M₂, hM₂⟩ := exists_weilLagFunctionReal_le_exp_of_powerGaps_except hM0 hδ hK
    hC₂0.le (by positivity) hA hψ2 hgap
  set a₂ := max (max c 0) (max (1 / 2 + α + δ / 2 - 1 / 2 - δ) 0) with ha₂
  have ha₂0 : 0 ≤ a₂ := le_trans (le_max_right _ _) (le_max_right _ _)
  have hg₂ : ∀ q' : XiZeroCopy, (q'.1 : ℂ).re ≤ 1 / 2 + max (max a₂ (α - κ)) 0 := fun q' =>
    re_le_half_add_of_weilLagFunctionReal_le_exp_except ha₂0 hS hSint hM₂
      (fun u hu => abs_weilLagFunctionReal_le_of_strip hstrip hu) q'
  have hsup₂ := zeroReSup_le hg₂
  have hle₂ : α ≤ max (max a₂ (α - κ)) 0 := by linarith
  have hαc : α ≤ max 0 c := by
    by_contra hlt
    push Not at hlt
    have hc1 : max c 0 < α := by rwa [max_comm]
    have hc2 : max (1 / 2 + α + δ / 2 - 1 / 2 - δ) 0 < α :=
      max_lt (by linarith) (lt_of_le_of_lt (le_max_left 0 c) hlt)
    have hc3 : a₂ < α := max_lt hc1 hc2
    have hc4 : max a₂ (α - κ) < α := max_lt hc3 (by linarith)
    have hc5 : max (max a₂ (α - κ)) 0 < α :=
      max_lt hc4 (lt_of_le_of_lt (le_max_left 0 c) hlt)
    linarith
  exact (hαall q).trans hαc

/-! ## Lower-bound mirror and RH equivalences -/

/-- **One round of exceptional power-gap lower transport.**
Given `|ψ(N) − N| ≤ C N^β` (`β ≥ 0`) and `−(M + M k^c) ≤ a_k` on `A` (`M ≥ 0`), if outside `S` the
integer `⌊e^u⌋` eventually has a sample in `A ∩ [⌊e^u⌋ − K⌊e^u⌋^{1−δ}, ⌊e^u⌋]`, then
`−(M' e^{max(max c 0, max(β − ½ − δ, 0)) L}) ≤ Φ(L)` for all `L ≥ 0` outside `S`. -/
theorem exists_neg_exp_le_weilLagFunctionReal_of_powerGaps_except {A : Set ℕ} {M c K δ C β : ℝ}
    {S : Set ℝ} (hM0 : 0 ≤ M) (hδ : 0 < δ) (hK : 0 ≤ K) (hC : 0 ≤ C) (hβ : 0 ≤ β)
    (hA : ∀ k ∈ A, 2 ≤ k → -(M + M * (k : ℝ) ^ c) ≤ integerLag k)
    (hψ : ∀ N : ℕ, 1 ≤ N → |Chebyshev.psi N - N| ≤ C * (N : ℝ) ^ β)
    (hgap : ∀ᶠ u : ℝ in atTop, u ∉ S →
      ∃ k ∈ A, k ≤ ⌊Real.exp u⌋₊ ∧
        (⌊Real.exp u⌋₊ : ℝ) - k ≤ K * (⌊Real.exp u⌋₊ : ℝ) ^ (1 - δ)) :
    ∃ M' : ℝ, ∀ L : ℝ, 0 ≤ L → L ∉ S →
      -(M' * Real.exp (max (max c 0) (max (β - 1 / 2 - δ) 0) * L)) ≤ weilLagFunctionReal L := by
  set a := max (max c 0) (max (β - 1 / 2 - δ) 0) with hadef
  have ha0 : 0 ≤ a := le_trans (le_max_right _ _) (le_max_right _ _)
  have hca : c ≤ a := le_trans (le_max_left _ _) (le_max_left _ _)
  have hba : β - 1 / 2 - δ ≤ a := le_trans (le_max_left _ _) (le_max_right _ _)
  have hlim : Tendsto (fun n : ℕ => K * (n : ℝ) ^ (-δ)) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop).const_mul K
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (hlim.eventually (eventually_le_nhds
    (show (0 : ℝ) < 1 / 2 by norm_num)))
  set u₁ : ℝ := Real.log (max (N₂ : ℝ) 4 + 1) with hu₁
  obtain ⟨u₀, hu₀⟩ := eventually_atTop.mp (hgap.and (eventually_ge_atTop u₁))
  set D : ℝ := 20 + 4 * K * C with hD
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hW := lagWeightTotal_nonneg
  refine ⟨max (4 * M + 2 * D + 30) (Real.exp (|u₀| / 2) * lagWeightTotal), fun L hL hLS => ?_⟩
  rcases le_or_gt u₀ L with hLu | hLu
  · obtain ⟨hgapL, hLu₁⟩ := hu₀ L hLu
    obtain ⟨k, hkA, hkn, hgapn⟩ := hgapL hLS
    set n : ℕ := ⌊Real.exp L⌋₊ with hn
    have hexp : max (N₂ : ℝ) 4 + 1 ≤ Real.exp L := by
      rw [← Real.exp_log (by positivity : (0 : ℝ) < max (N₂ : ℝ) 4 + 1)]
      exact Real.exp_le_exp.mpr hLu₁
    have hn_ge : max N₂ 4 ≤ n := by
      apply Nat.le_floor
      rw [Nat.cast_max, Nat.cast_ofNat]
      linarith
    have hn4 : 4 ≤ n := le_trans (le_max_right _ _) hn_ge
    have hnN₂ : N₂ ≤ n := le_trans (le_max_left _ _) hn_ge
    have hL2 : Real.log 2 ≤ L := by
      have : (2 : ℝ) ≤ max (N₂ : ℝ) 4 + 1 := by linarith [le_max_right (N₂ : ℝ) 4]
      exact (Real.log_le_log (by norm_num) this).trans hLu₁
    obtain ⟨hk2, hr, habs⟩ := abs_integerLag_sub_le_rpow_of_sample hK hC hβ hn4 (hN₂ n hnN₂)
      hkn hgapn hψ
    have hr0 : 0 ≤ Real.sqrt n / Real.sqrt k := by positivity
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have hnL : (n : ℝ) ≤ Real.exp L := Nat.floor_le (Real.exp_pos L).le
    have hkc : (k : ℝ) ^ c ≤ Real.exp (a * L) := by
      calc (k : ℝ) ^ c ≤ (k : ℝ) ^ a := Real.rpow_le_rpow_of_exponent_le hk1 hca
        _ ≤ (n : ℝ) ^ a := Real.rpow_le_rpow (by positivity) (by exact_mod_cast hkn) ha0
        _ ≤ (Real.exp L) ^ a := Real.rpow_le_rpow (by positivity) hnL ha0
        _ = Real.exp (a * L) := by rw [← Real.exp_mul, mul_comm]
    have hnb : (n : ℝ) ^ (β - 1 / 2 - δ) ≤ Real.exp (a * L) := by
      calc (n : ℝ) ^ (β - 1 / 2 - δ) ≤ (n : ℝ) ^ a := Real.rpow_le_rpow_of_exponent_le hn1 hba
        _ ≤ (Real.exp L) ^ a := Real.rpow_le_rpow (by positivity) hnL ha0
        _ = Real.exp (a * L) := by rw [← Real.exp_mul, mul_comm]
    have he1 : 1 ≤ Real.exp (a * L) := Real.one_le_exp (mul_nonneg ha0 hL)
    have hak : -(2 * M * Real.exp (a * L)) ≤ integerLag k := by
      have := hA k hkA hk2
      nlinarith
    have h1 : -(4 * M * Real.exp (a * L)) ≤ (Real.sqrt n / Real.sqrt k) * integerLag k := by
      have h1a := mul_le_mul_of_nonneg_left hak hr0
      have h1b : (Real.sqrt n / Real.sqrt k) * (2 * M * Real.exp (a * L)) ≤
          2 * (2 * M * Real.exp (a * L)) :=
        mul_le_mul_of_nonneg_right hr (by positivity)
      linarith
    have h2 : -((4 * M + 2 * D) * Real.exp (a * L)) ≤ integerLag n := by
      have := (abs_le.mp habs).1
      rw [← hD] at this
      nlinarith
    have hcmp := integerLag_sub_le_weilLagFunctionReal hL2
    have h3 : -((4 * M + 2 * D + 30) * Real.exp (a * L)) ≤ weilLagFunctionReal L := by nlinarith
    have h4 : -(max (4 * M + 2 * D + 30) (Real.exp (|u₀| / 2) * lagWeightTotal) *
        Real.exp (a * L)) ≤ -((4 * M + 2 * D + 30) * Real.exp (a * L)) := by
      rw [neg_le_neg_iff]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    exact h4.trans h3
  · have h1 := abs_weilLagFunctionReal_le L
    rw [abs_of_nonneg hL] at h1
    have h2 : Real.exp (L / 2) ≤ Real.exp (|u₀| / 2) :=
      Real.exp_le_exp.mpr (by linarith [le_abs_self u₀])
    have h3 : 1 ≤ Real.exp (a * L) := Real.one_le_exp (mul_nonneg ha0 hL)
    have h4 : -(Real.exp (|u₀| / 2) * lagWeightTotal) ≤ weilLagFunctionReal L := by
      have := (abs_le.mp (h1.trans (mul_le_mul_of_nonneg_right h2 hW))).1
      linarith
    have h5 : 0 ≤ max (4 * M + 2 * D + 30) (Real.exp (|u₀| / 2) * lagWeightTotal) :=
      le_trans (by positivity) (le_max_right _ _)
    have h6 : Real.exp (|u₀| / 2) * lagWeightTotal ≤
        max (4 * M + 2 * D + 30) (Real.exp (|u₀| / 2) * lagWeightTotal) * Real.exp (a * L) :=
      (le_max_right _ _).trans (le_mul_of_one_le_right h5 h3)
    linarith

/-- **Power-gap lower lag sampling with exponential exceptions forces the zero-free half-plane.**
Let `−(M + M k^c) ≤ a_k` on `A` (`M ≥ 0`), and suppose outside a measurable set `S` of log-scales
with `∫_S e^{κu} du < ∞` (`κ > 0`) the integer `⌊e^u⌋` eventually has a sample in
`A ∩ [⌊e^u⌋ − K⌊e^u⌋^{1−δ}, ⌊e^u⌋]` (`δ > 0`). Then every zero satisfies
`|Re ρ − ½| ≤ max(0, c)`. -/
theorem abs_re_sub_half_le_of_powerGaps_neg_rpow_le_integerLag_except {A : Set ℕ} {M c K δ κ : ℝ}
    {S : Set ℝ} (hM0 : 0 ≤ M) (hδ : 0 < δ) (hK : 0 ≤ K) (hκ : 0 < κ) (hS : MeasurableSet S)
    (hSint : IntegrableOn (fun u => Real.exp (κ * u)) S)
    (hA : ∀ k ∈ A, 2 ≤ k → -(M + M * (k : ℝ) ^ c) ≤ integerLag k)
    (hgap : ∀ᶠ u : ℝ in atTop, u ∉ S →
      ∃ k ∈ A, k ≤ ⌊Real.exp u⌋₊ ∧
        (⌊Real.exp u⌋₊ : ℝ) - k ≤ K * (⌊Real.exp u⌋₊ : ℝ) ^ (1 - δ))
    (q : XiZeroCopy) : |(q.1 : ℂ).re - 1 / 2| ≤ max 0 c := by
  haveI : Nonempty XiZeroCopy := ⟨q⟩
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = zeroReSup - 1 / 2 := ⟨_, rfl⟩
  have hXi : XiZeroHalfPlaneBound α := by
    intro ρ hρ
    obtain ⟨q', rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
    have := re_le_zeroReSup q'
    rw [hαdef]; linarith
  have hαall : ∀ q' : XiZeroCopy, |(q'.1 : ℂ).re - 1 / 2| ≤ α :=
    abs_re_sub_half_le_of_xiZeroHalfPlaneBound hXi
  have hstrip : ∀ q' : XiZeroCopy, (q'.1 : ℂ).re ≤ 1 / 2 + α := fun q' => by
    linarith [(abs_le.mp (hαall q')).2]
  have hα0 : 0 ≤ α := le_trans (abs_nonneg _) (hαall q)
  have hαh : α ≤ 1 / 2 := by
    have := zeroReSup_le (fun q' : XiZeroCopy => (xiZeroCopy_re_lt_one q').le)
    rw [hαdef]; linarith
  by_cases hc : 1 / 2 ≤ max 0 c
  · exact (hαall q).trans (by linarith)
  push Not at hc
  -- Step 1 (Chebyshev β = 1): prove α < 1/2
  have hψ1 : ∀ N : ℕ, 1 ≤ N → |Chebyshev.psi N - N| ≤ 6 * (N : ℝ) ^ (1 : ℝ) := by
    intro N _
    rw [Real.rpow_one]
    have h1 := psi_nat_le_six_mul N
    have h0 := psi_nat_nonneg N
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    rw [abs_le]; constructor <;> linarith
  obtain ⟨M₁, hM₁⟩ := exists_neg_exp_le_weilLagFunctionReal_of_powerGaps_except hM0 hδ hK
    (by norm_num) (by norm_num) hA hψ1 hgap
  set a₁ := max (max c 0) (max ((1 : ℝ) - 1 / 2 - δ) 0) with ha₁
  have ha₁0 : 0 ≤ a₁ := le_trans (le_max_right _ _) (le_max_right _ _)
  have hg₁ : ∀ q' : XiZeroCopy, (q'.1 : ℂ).re ≤ 1 / 2 + max (max a₁ (α - κ)) 0 := fun q' =>
    re_le_half_add_of_neg_exp_le_weilLagFunctionReal_except ha₁0 hS hSint hM₁
      (fun u hu => abs_weilLagFunctionReal_le_of_strip hstrip hu) q'
  have hsup₁ := zeroReSup_le hg₁
  have hle₁ : α ≤ max (max a₁ (α - κ)) 0 := by linarith
  have hαlt : α < 1 / 2 := by
    have hc1 : max c 0 < 1 / 2 := by rwa [max_comm]
    have hc2 : max ((1 : ℝ) - 1 / 2 - δ) 0 < 1 / 2 := max_lt (by linarith) (by norm_num)
    have hc3 : a₁ < 1 / 2 := max_lt hc1 hc2
    have hc4 : max a₁ (α - κ) < 1 / 2 := max_lt hc3 (by linarith)
    exact lt_of_le_of_lt hle₁ (max_lt hc4 (by norm_num))
  -- Step 2 (Von Koch at e = α < 1/2): prove α ≤ max 0 c
  obtain ⟨C₂, hC₂0, hC₂⟩ := Sieve.exists_chebyshev_error_power_bound_of_xiZeroHalfPlaneBound
    hα0 hαlt hXi (show 0 < δ / 2 by positivity)
  have hψ2 : ∀ N : ℕ, 1 ≤ N → |Chebyshev.psi N - N| ≤ C₂ * (N : ℝ) ^ (1 / 2 + α + δ / 2) := by
    intro N hN
    rw [psi_natCast_eq_sum_Icc_one]
    exact hC₂ N hN
  obtain ⟨M₂, hM₂⟩ := exists_neg_exp_le_weilLagFunctionReal_of_powerGaps_except hM0 hδ hK
    hC₂0.le (by positivity) hA hψ2 hgap
  set a₂ := max (max c 0) (max (1 / 2 + α + δ / 2 - 1 / 2 - δ) 0) with ha₂
  have ha₂0 : 0 ≤ a₂ := le_trans (le_max_right _ _) (le_max_right _ _)
  have hg₂ : ∀ q' : XiZeroCopy, (q'.1 : ℂ).re ≤ 1 / 2 + max (max a₂ (α - κ)) 0 := fun q' =>
    re_le_half_add_of_neg_exp_le_weilLagFunctionReal_except ha₂0 hS hSint hM₂
      (fun u hu => abs_weilLagFunctionReal_le_of_strip hstrip hu) q'
  have hsup₂ := zeroReSup_le hg₂
  have hle₂ : α ≤ max (max a₂ (α - κ)) 0 := by linarith
  have hαc : α ≤ max 0 c := by
    by_contra hlt
    push Not at hlt
    have hc1 : max c 0 < α := by rwa [max_comm]
    have hc2 : max (1 / 2 + α + δ / 2 - 1 / 2 - δ) 0 < α :=
      max_lt (by linarith) (lt_of_le_of_lt (le_max_left 0 c) hlt)
    have hc3 : a₂ < α := max_lt hc1 hc2
    have hc4 : max a₂ (α - κ) < α := max_lt hc3 (by linarith)
    have hc5 : max (max a₂ (α - κ)) 0 < α :=
      max_lt hc4 (lt_of_le_of_lt (le_max_left 0 c) hlt)
    linarith
  exact (hαall q).trans hαc

/-- **Power-gap upper lag sampling with exponential exceptions gives RH.** -/
theorem riemannHypothesis_of_powerGaps_integerLag_le_except {A : Set ℕ} {M K δ κ : ℝ}
    {S : Set ℝ} (hδ : 0 < δ) (hK : 0 ≤ K) (hκ : 0 < κ) (hS : MeasurableSet S)
    (hSint : IntegrableOn (fun u => Real.exp (κ * u)) S)
    (hgap : ∀ᶠ u : ℝ in atTop, u ∉ S →
      ∃ k ∈ A, k ≤ ⌊Real.exp u⌋₊ ∧
        (⌊Real.exp u⌋₊ : ℝ) - k ≤ K * (⌊Real.exp u⌋₊ : ℝ) ^ (1 - δ))
    (hA : ∀ k ∈ A, 2 ≤ k → integerLag k ≤ M) : RiemannHypothesis := by
  refine riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mpr fun ρ hρ => ?_
  obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  have hA' : ∀ k ∈ A, 2 ≤ k → integerLag k ≤ max M 0 + max M 0 * (k : ℝ) ^ (0 : ℝ) := by
    intro k hkA hk2
    rw [Real.rpow_zero, mul_one]
    linarith [hA k hkA hk2, le_max_left M 0, le_max_right M 0]
  have h := abs_re_sub_half_le_of_powerGaps_integerLag_le_rpow_except
    (le_max_right M 0) hδ hK hκ hS hSint hA' hgap q
  rw [max_self] at h
  linarith [(abs_le.mp h).2]

/-- **Power-gap lower lag sampling with exponential exceptions gives RH.** -/
theorem riemannHypothesis_of_powerGaps_le_integerLag_except {A : Set ℕ} {M K δ κ : ℝ}
    {S : Set ℝ} (hδ : 0 < δ) (hK : 0 ≤ K) (hκ : 0 < κ) (hS : MeasurableSet S)
    (hSint : IntegrableOn (fun u => Real.exp (κ * u)) S)
    (hgap : ∀ᶠ u : ℝ in atTop, u ∉ S →
      ∃ k ∈ A, k ≤ ⌊Real.exp u⌋₊ ∧
        (⌊Real.exp u⌋₊ : ℝ) - k ≤ K * (⌊Real.exp u⌋₊ : ℝ) ^ (1 - δ))
    (hA : ∀ k ∈ A, 2 ≤ k → M ≤ integerLag k) : RiemannHypothesis := by
  refine riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mpr fun ρ hρ => ?_
  obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  have hA' : ∀ k ∈ A, 2 ≤ k → -(max (-M) 0 + max (-M) 0 * (k : ℝ) ^ (0 : ℝ)) ≤ integerLag k := by
    intro k hkA hk2
    rw [Real.rpow_zero, mul_one]
    linarith [hA k hkA hk2, le_max_left (-M) 0, le_max_right (-M) 0]
  have h := abs_re_sub_half_le_of_powerGaps_neg_rpow_le_integerLag_except
    (le_max_right (-M) 0) hδ hK hκ hS hSint hA' hgap q
  rw [max_self] at h
  linarith [(abs_le.mp h).2]

/-- **RH ⟺ the lag dips below a fixed level in every power window off an exponentially thin set of
log-scales.** -/
theorem riemannHypothesis_iff_exists_powerWindow_integerLag_le_except :
    RiemannHypothesis ↔ ∃ δ : ℝ, 0 < δ ∧ ∃ κ : ℝ, 0 < κ ∧ ∃ M : ℝ, ∃ S : Set ℝ,
      MeasurableSet S ∧ IntegrableOn (fun u => Real.exp (κ * u)) S ∧
      ∀ᶠ u : ℝ in atTop, u ∉ S →
        ∃ k : ℕ, 2 ≤ k ∧ k ≤ ⌊Real.exp u⌋₊ ∧
          (⌊Real.exp u⌋₊ : ℝ) - k ≤ (⌊Real.exp u⌋₊ : ℝ) ^ (1 - δ) ∧ integerLag k ≤ M := by
  constructor
  · intro h
    obtain ⟨M, hM⟩ := riemannHypothesis_iff_integerLag_bddAbove.mp h
    refine ⟨1 / 2, by norm_num, 1, zero_lt_one, M, ∅, MeasurableSet.empty, integrableOn_empty, ?_⟩
    filter_upwards [eventually_ge_atTop (Real.log 2)] with u hu _
    have h2 : 2 ≤ ⌊Real.exp u⌋₊ := Nat.le_floor (by
      push_cast
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      exact Real.exp_le_exp.mpr hu)
    refine ⟨⌊Real.exp u⌋₊, h2, le_rfl, ?_, hM _ h2⟩
    rw [sub_self]; positivity
  · rintro ⟨δ, hδ, κ, hκ, M, S, hS, hSint, h⟩
    refine riemannHypothesis_of_powerGaps_integerLag_le_except
      (A := {k | 2 ≤ k ∧ integerLag k ≤ M}) (M := M) (K := 1) hδ zero_le_one hκ hS hSint ?_
      (fun k hk _ => hk.2)
    filter_upwards [h] with u hu huS
    obtain ⟨k, hk2, hkn, hgap, hk⟩ := hu huS
    exact ⟨k, ⟨hk2, hk⟩, hkn, by rw [one_mul]; exact hgap⟩

/-- **RH ⟺ the lag rises above a fixed level in every power window off an exponentially thin set of
log-scales.** -/
theorem riemannHypothesis_iff_exists_powerWindow_le_integerLag_except :
    RiemannHypothesis ↔ ∃ δ : ℝ, 0 < δ ∧ ∃ κ : ℝ, 0 < κ ∧ ∃ M : ℝ, ∃ S : Set ℝ,
      MeasurableSet S ∧ IntegrableOn (fun u => Real.exp (κ * u)) S ∧
      ∀ᶠ u : ℝ in atTop, u ∉ S →
        ∃ k : ℕ, 2 ≤ k ∧ k ≤ ⌊Real.exp u⌋₊ ∧
          (⌊Real.exp u⌋₊ : ℝ) - k ≤ (⌊Real.exp u⌋₊ : ℝ) ^ (1 - δ) ∧ M ≤ integerLag k := by
  constructor
  · intro h
    obtain ⟨M, hM⟩ := riemannHypothesis_iff_integerLag_bddBelow.mp h
    refine ⟨1 / 2, by norm_num, 1, zero_lt_one, M, ∅, MeasurableSet.empty, integrableOn_empty, ?_⟩
    filter_upwards [eventually_ge_atTop (Real.log 2)] with u hu _
    have h2 : 2 ≤ ⌊Real.exp u⌋₊ := Nat.le_floor (by
      push_cast
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      exact Real.exp_le_exp.mpr hu)
    refine ⟨⌊Real.exp u⌋₊, h2, le_rfl, ?_, hM _ h2⟩
    rw [sub_self]; positivity
  · rintro ⟨δ, hδ, κ, hκ, M, S, hS, hSint, h⟩
    refine riemannHypothesis_of_powerGaps_le_integerLag_except
      (A := {k | 2 ≤ k ∧ M ≤ integerLag k}) (M := M) (K := 1) hδ zero_le_one hκ hS hSint ?_
      (fun k hk _ => hk.2)
    filter_upwards [h] with u hu huS
    obtain ⟨k, hk2, hkn, hgap, hk⟩ := hu huS
    exact ⟨k, ⟨hk2, hk⟩, hkn, by rw [one_mul]; exact hgap⟩

end

end RHTower
