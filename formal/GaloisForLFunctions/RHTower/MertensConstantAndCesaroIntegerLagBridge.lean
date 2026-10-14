import GaloisForLFunctions.RHTower.ObserverJetFubiniAndIntegerLagBridge
import GaloisForLFunctions.RHTower.WeilLagTwoSidedMeshSampling
import GaloisForLFunctions.RHTower.CCMFUSuzukiSelbergOutgoingAbelWeld
import GaloisForLFunctions.RHTower.CCMUnitRieszProfileLimit
import GaloisForLFunctions.RHTower.Sieve.ChebyshevPsiBigO
import GaloisForLFunctions.RHTower.Sieve.SqrtLogTailIntegral

/-!
# Prime-Jump-Free Lag Lipschitz Laws, Exponential-`√(log d)` Mertens Decay, and the Cesàro Integer-Lag Bridge

This module advances the unconditional observer-jet / integer-lag programme in three directions:

1. **Section 1 (Prime-Jump-Free Uniform Lipschitz Laws for `lagBracket` and `integerLag`):**
   In `WeilLagFunctionPrimeGap.lean`, `|lagBracket m - lagBracket n|` paid a `(log m + 2)^2`
   factor because `-ψ` and `m * mertensSum` were bounded separately over `[n, m]`. In
   `WeilLagTwoSidedMeshSampling.lean`, removing `(log m + 2)^2` via Brun–Titchmarsh introduced an
   additive `3600 √n` error (`|integerLag m - integerLag n| ≤ 3620 (1 + (m - n)/√n)`), which does
   not even vanish when `m - n = o(√n)`.
   Using the prime-jump-free unit step `mul_lagBracketSlope_succ_sub` from
   `ObserverJetFubiniAndIntegerLagBridge` — where `Λ(d + 1)` cancels identically at each unit step
   `d ↦ d + 1` — together with Mertens' first theorem (`abs_mertensSum_sub_log_le`), we prove:
   - `|(d + 1) * lagBracketSlope (d + 1) - d * lagBracketSlope d| ≤ 7 + 1 / d ≤ 8` for all `d ≥ 1`.
   - `|m * lagBracketSlope m - n * lagBracketSlope n| ≤ 8 * (m - n)` for all `1 ≤ n ≤ m`.
   - `|lagBracket m - lagBracket n| ≤ 8 * (m - n) + 1` for all `1 ≤ n ≤ m` (no `m ≤ 2n`, no
     `(log m + 2)^2`, and no `√n` additive loss).
   - `|integerLag m - integerLag n| ≤ (28 * (m - n) + 1) / √n` for all `2 ≤ n ≤ m ≤ 2n`.
   - `|completedSourceObserverJetMass d| ≤ 24 + |2γ|` and
     `|completedSourceObserverJetMass (d + 1) - completedSourceObserverJetMass d| ≤ (31 + 2 * |2γ|) / d`
     for all `d ≥ 2`.

2. **Section 2 (Exponential-`√(log d)` Mertens Deviation, Observer-Jet Mass Decay, and Super-`√n` Lag Transport):**
   Combining `mertensDeviation_eq` (`WeilLagFunctionFrontier`) with `Sieve.chebyshevPsi_sub_id_isBigO`
   and `Sieve.sqrtLogTail_le`, we upgrade the unconditional Mertens deviation, integer-lag frontier,
   `lagBracketSlope`, `completedSourceObserverJetMass`, and the unit step of `d * lagBracketSlope d`
   from `exp(-c (log d)^{1/10})` to `exp(-c √(log d))`, obtaining global bounds valid for all `d ≥ 2`
   and an `o(1 / √n)`-Lipschitz law for `integerLag` over gaps:
   `|integerLag m - integerLag n| ≤ C * ((m - n) / √n) * exp(-c √(log n)) + 2 / √n`.

3. **Section 3 (Exact `(4/3) M * integerLag M - 2 * integerLagCesaroSum M` Bridge and Summation by Parts):**
   Using `unitRieszSqrtPrefixMass_lower` and `unitRieszSqrtPrefixMass_upper`, we evaluate the
   terminal coefficient `∑_{k < M - 2} 2 √(k + 2) = (4 / 3) M √M + O(√M)`. Multiplying by
   `integerLag M / √M` cancels `√M` identically both in the main term `(4 / 3) M * integerLag M` and
   in the error term `4 * |integerLag M| ≤ 80 √M`, reducing `completedSourceObserverJetSqrtMassAction M`
   and `integerLagSqrtRatioAction M` within `O(√M)` to:
   `integerLagLinearCesaroAction M := (4 / 3) * M * integerLag M - 2 * integerLagCesaroSum M`.
   Finally, we establish the exact Abel summation-by-parts identity expressing `integerLagCesaroSum M`
   in terms of `harmonicSqrtPrefix (M - 2) * lagBracket M` and the prime-jump-free unit steps of
   `lagBracket`.
-/

open Complex Filter Topology Set MeasureTheory Real
open scoped BigOperators Chebyshev
open ArithmeticFunction (vonMangoldt)

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

noncomputable section

/-! ## Section 1: Prime-Jump-Free Uniform Lipschitz Laws for `lagBracket` and `integerLag` -/

/-- Uniform bound `|mertensSum d - log d + γ| ≤ 7` for all `d ≥ 1` from Mertens' first theorem. -/
theorem abs_mertensDeviation_le_seven {d : ℕ} (hd : 1 ≤ d) :
    |mertensSum d - Real.log (d : ℝ) + Real.eulerMascheroniConstant| ≤ 7 := by
  have hM := abs_mertensSum_sub_log_le hd
  have hγ1 : Real.eulerMascheroniConstant ≤ 1 := by
    have := Real.eulerMascheroniConstant_lt_two_thirds
    linarith
  have hγ0 : 0 ≤ Real.eulerMascheroniConstant := by
    have := eulerMascheroniConstant_gt
    linarith
  rw [abs_le] at hM ⊢
  constructor <;> linarith [hM.1, hM.2]

/-- **Prime-Jump-Free Unit Step Bound:**
For every `d ≥ 1`, `|(d + 1) * lagBracketSlope (d + 1) - d * lagBracketSlope d| ≤ 7 + 1 / d ≤ 8`. -/
theorem abs_mul_lagBracketSlope_succ_sub_le {d : ℕ} (hd : 1 ≤ d) :
    |((d + 1 : ℕ) : ℝ) * lagBracketSlope (d + 1) - (d : ℝ) * lagBracketSlope d| ≤
      7 + 1 / (d : ℝ) := by
  have h1 := abs_mul_lagBracketSlope_succ_sub_mertensDeviation_le hd
  have h2 := abs_mertensDeviation_le_seven hd
  calc
    |((d + 1 : ℕ) : ℝ) * lagBracketSlope (d + 1) - (d : ℝ) * lagBracketSlope d| =
      |(((d + 1 : ℕ) : ℝ) * lagBracketSlope (d + 1) - (d : ℝ) * lagBracketSlope d -
          (mertensSum d - Real.log (d : ℝ) + Real.eulerMascheroniConstant)) +
        (mertensSum d - Real.log (d : ℝ) + Real.eulerMascheroniConstant)| := by ring_nf
    _ ≤ |((d + 1 : ℕ) : ℝ) * lagBracketSlope (d + 1) - (d : ℝ) * lagBracketSlope d -
          (mertensSum d - Real.log (d : ℝ) + Real.eulerMascheroniConstant)| +
        |mertensSum d - Real.log (d : ℝ) + Real.eulerMascheroniConstant| := abs_add_le _ _
    _ ≤ 1 / (d : ℝ) + 7 := add_le_add h1 h2
    _ = 7 + 1 / (d : ℝ) := by ring

theorem abs_mul_lagBracketSlope_succ_sub_le_eight {d : ℕ} (hd : 1 ≤ d) :
    |((d + 1 : ℕ) : ℝ) * lagBracketSlope (d + 1) - (d : ℝ) * lagBracketSlope d| ≤ 8 := by
  have h1 := abs_mul_lagBracketSlope_succ_sub_le hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hinv : 1 / (d : ℝ) ≤ 1 := div_le_self (by norm_num) hd1
  linarith

/-- Exact telescoping of `d * lagBracketSlope d` over `Finset.Ico n m`. -/
theorem mul_lagBracketSlope_sub_eq_sum_Ico {n m : ℕ} (hnm : n ≤ m) :
    (m : ℝ) * lagBracketSlope m - (n : ℝ) * lagBracketSlope n =
      ∑ d ∈ Finset.Ico n m,
        (((d + 1 : ℕ) : ℝ) * lagBracketSlope (d + 1) - (d : ℝ) * lagBracketSlope d) := by
  induction m, hnm using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [Finset.sum_Ico_succ_top hk, ← ih]
    ring

/-- **Prime-Jump-Free Multi-Step Lipschitz Bound for `d * lagBracketSlope d`:**
For all `1 ≤ n ≤ m` (without `m ≤ 2n`), `|m * lagBracketSlope m - n * lagBracketSlope n| ≤ 8 * (m - n)`. -/
theorem abs_mul_lagBracketSlope_sub_le {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    |(m : ℝ) * lagBracketSlope m - (n : ℝ) * lagBracketSlope n| ≤
      8 * ((m - n : ℕ) : ℝ) := by
  rw [mul_lagBracketSlope_sub_eq_sum_Ico hnm]
  calc
    |∑ d ∈ Finset.Ico n m,
        (((d + 1 : ℕ) : ℝ) * lagBracketSlope (d + 1) - (d : ℝ) * lagBracketSlope d)| ≤
      ∑ d ∈ Finset.Ico n m,
        |((d + 1 : ℕ) : ℝ) * lagBracketSlope (d + 1) - (d : ℝ) * lagBracketSlope d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ Finset.Ico n m, (8 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdn : n ≤ d := (Finset.mem_Ico.mp hd).1
      exact abs_mul_lagBracketSlope_succ_sub_le_eight (hn.trans hdn)
    _ = 8 * ((m - n : ℕ) : ℝ) := by
      simp [Nat.card_Ico, mul_comm]

/-- Relation `lagBracket d = d * lagBracketSlope d - log (2π) + trivialZeroSeriesReal d`. -/
theorem lagBracket_eq_mul_lagBracketSlope_sub (d : ℕ) :
    lagBracket d =
      (d : ℝ) * lagBracketSlope d - Real.log (2 * Real.pi) + trivialZeroSeriesReal d := by
  rcases eq_or_ne d 0 with rfl | hd0
  · unfold lagBracket lagBracketSlope
    simp [Chebyshev.psi_eq_sum_Icc]
  · have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
    have h2 : (d : ℝ) * lagBracketSlope d =
        lagBracket d - trivialZeroSeriesReal d + Real.log (2 * Real.pi) := by
      unfold lagBracketSlope
      exact mul_div_cancel₀ _ hdR
    rw [h2]
    ring

/-- **Prime-Jump-Free Unit Step of `lagBracket`:**
In `lagBracket (d + 1) - lagBracket d`, the prime-power jump `Λ(d + 1)` cancels identically. -/
theorem lagBracket_succ_sub_eq {d : ℕ} (hd : 1 ≤ d) :
    lagBracket (d + 1) - lagBracket d =
      (mertensSum d - Real.log (d : ℝ) + Real.eulerMascheroniConstant) -
        (((d + 1 : ℕ) : ℝ) * Real.log (((d + 1 : ℕ) : ℝ) / (d : ℝ)) - 1) +
        (trivialZeroSeriesReal (d + 1) - trivialZeroSeriesReal d) := by
  rw [lagBracket_eq_mul_lagBracketSlope_sub (d + 1), lagBracket_eq_mul_lagBracketSlope_sub d]
  have hstep := mul_lagBracketSlope_succ_sub hd
  push_cast at hstep ⊢
  linarith

/-- **Global Prime-Jump-Free Lipschitz Bound for `lagBracket`:**
For ALL `1 ≤ n ≤ m` (without `m ≤ 2n`, without `(log m + 2)^2`, and without Brun–Titchmarsh `√n`
window loss), `|lagBracket m - lagBracket n| ≤ 8 * (m - n) + 1`. -/
theorem abs_lagBracket_sub_le_linear_gap {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    |lagBracket m - lagBracket n| ≤ 8 * ((m - n : ℕ) : ℝ) + 1 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (hn.trans hnm)
  have hnmR : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have h1 := abs_mul_lagBracketSlope_sub_le hn hnm
  have hSm0 : 0 ≤ trivialZeroSeriesReal m := trivialZeroSeriesReal_nonneg hm1
  have hSn1 : trivialZeroSeriesReal n ≤ 1 := trivialZeroSeriesReal_le_one hn1
  have hSanti : trivialZeroSeriesReal m ≤ trivialZeroSeriesReal n :=
    trivialZeroSeriesReal_anti hn1 hnmR
  have hS : |trivialZeroSeriesReal m - trivialZeroSeriesReal n| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hsplit :
      lagBracket m - lagBracket n =
        ((m : ℝ) * lagBracketSlope m - (n : ℝ) * lagBracketSlope n) +
          (trivialZeroSeriesReal m - trivialZeroSeriesReal n) := by
    rw [lagBracket_eq_mul_lagBracketSlope_sub m, lagBracket_eq_mul_lagBracketSlope_sub n]
    ring
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add h1 hS)

/-- **Prime-Jump-Free `o(1)`-Scale Lipschitz Law for `integerLag`:**
For all `2 ≤ n ≤ m ≤ 2n`,
`|integerLag m - integerLag n| ≤ (28 * (m - n) + 1) / √n`.
Unlike `abs_integerLag_sub_le` in `WeilLagFunctionPrimeGap` (which has `(log m + 2)^2`) and
`abs_integerLag_sub_le_sqrt` in `WeilLagTwoSidedMeshSampling` (which has an additive constant
`3620`), this bound tends to `0` whenever `m - n = o(√n)`. -/
theorem abs_integerLag_sub_le_div_sqrt {n m : ℕ} (hn2 : 2 ≤ n) (hnm : n ≤ m) (hm2n : m ≤ 2 * n) :
    |integerLag m - integerLag n| ≤ (28 * ((m - n : ℕ) : ℝ) + 1) / Real.sqrt (n : ℝ) := by
  have hm2 : 2 ≤ m := hn2.trans hnm
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have hm2n' : (m : ℝ) ≤ 2 * n := by exact_mod_cast hm2n
  have hm0 : (0 : ℝ) < m := by linarith
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hsnm : Real.sqrt (n : ℝ) ≤ Real.sqrt (m : ℝ) := Real.sqrt_le_sqrt hnm'
  set g : ℝ := ((m - n : ℕ) : ℝ) with hg
  have hg_eq : g = (m : ℝ) - n := by rw [hg]; push_cast [Nat.cast_sub hnm]; ring
  have hg0 : 0 ≤ g := by rw [hg_eq]; linarith
  have hEm := abs_lagBracket_le_linear hm2
  have hEd := abs_lagBracket_sub_le_linear_gap (by omega : 1 ≤ n) hnm
  rw [← hg] at hEd
  have hinv := inv_sqrt_sub_inv_sqrt_le hn1 hnm'
  have hinv0 : 0 ≤ 1 / Real.sqrt (n : ℝ) - 1 / Real.sqrt (m : ℝ) := by
    have := one_div_le_one_div_of_le hsn hsnm
    linarith
  rw [integerLag_eq_lagBracket hm2, integerLag_eq_lagBracket hn2]
  have hdecomp :
      lagBracket m / Real.sqrt (m : ℝ) - lagBracket n / Real.sqrt (n : ℝ) =
        -(lagBracket m * (1 / Real.sqrt (n : ℝ) - 1 / Real.sqrt (m : ℝ))) +
          (lagBracket m - lagBracket n) / Real.sqrt (n : ℝ) := by
    field_simp
    ring
  rw [hdecomp]
  have ht1 : |lagBracket m * (1 / Real.sqrt (n : ℝ) - 1 / Real.sqrt (m : ℝ))| ≤
      20 * g / Real.sqrt (n : ℝ) := by
    rw [abs_mul, abs_of_nonneg hinv0]
    calc
      |lagBracket m| * (1 / Real.sqrt (n : ℝ) - 1 / Real.sqrt (m : ℝ)) ≤
        (20 * (m : ℝ)) * (((m : ℝ) - n) / (2 * ((n : ℝ) * Real.sqrt (n : ℝ)))) :=
        mul_le_mul hEm hinv hinv0 (by positivity)
      _ = 10 * ((m : ℝ) / n) * (g / Real.sqrt (n : ℝ)) := by
        rw [hg_eq]
        field_simp [hn0.ne', hsn.ne']
        ring
      _ ≤ 10 * 2 * (g / Real.sqrt (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        rw [div_le_iff₀ hn0]
        linarith
      _ = 20 * g / Real.sqrt (n : ℝ) := by ring
  have ht2 : |(lagBracket m - lagBracket n) / Real.sqrt (n : ℝ)| ≤
      (8 * g + 1) / Real.sqrt (n : ℝ) := by
    rw [abs_div, abs_of_pos hsn]
    exact div_le_div_of_nonneg_right hEd hsn.le
  calc
    |-(lagBracket m * (1 / Real.sqrt (n : ℝ) - 1 / Real.sqrt (m : ℝ))) +
        (lagBracket m - lagBracket n) / Real.sqrt (n : ℝ)| ≤
      |lagBracket m * (1 / Real.sqrt (n : ℝ) - 1 / Real.sqrt (m : ℝ))| +
        |(lagBracket m - lagBracket n) / Real.sqrt (n : ℝ)| := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_neg]
    _ ≤ 20 * g / Real.sqrt (n : ℝ) + (8 * g + 1) / Real.sqrt (n : ℝ) := add_le_add ht1 ht2
    _ = (28 * g + 1) / Real.sqrt (n : ℝ) := by ring

/-- Unit-step decay `|integerLag (n + 1) - integerLag n| ≤ 29 / √n` for all `n ≥ 2`. -/
theorem abs_integerLag_succ_sub_le {n : ℕ} (hn : 2 ≤ n) :
    |integerLag (n + 1) - integerLag n| ≤ 29 / Real.sqrt (n : ℝ) := by
  have h := abs_integerLag_sub_le_div_sqrt hn (by omega : n ≤ n + 1) (by omega : n + 1 ≤ 2 * n)
  have hsub : ((n + 1 - n : ℕ) : ℝ) = 1 := by norm_num
  rw [hsub] at h
  exact h.trans_eq (by ring)

/-- Explicit uniform bound `|integerLag d| ≤ 20 * √d` for all `d ≥ 2`. -/
theorem abs_integerLag_le_twenty_mul_sqrt {d : ℕ} (hd : 2 ≤ d) :
    |integerLag d| ≤ 20 * Real.sqrt (d : ℝ) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hsd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hd0
  have hsq : Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) = (d : ℝ) := Real.mul_self_sqrt hd0.le
  rw [integerLag_eq_lagBracket hd, abs_div, abs_of_pos hsd, div_le_iff₀ hsd]
  calc
    |lagBracket d| ≤ 20 * (d : ℝ) := abs_lagBracket_le_linear hd
    _ = 20 * (Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ)) := by rw [hsq]
    _ = 20 * Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) := by ring

/-! ## Section 2: Exponential-`√(log d)` Mertens Deviation, Mass Decay, and Super-`√n` Lag Transport -/

/-- **Upgraded Quantitative Mertens Deviation (`exp(-c √(log x))` rate):**
Combining `mertensDeviation_eq` (`WeilLagFunctionFrontier`) with `Sieve.chebyshevPsi_sub_id_isBigO`
and `Sieve.sqrtLogTail_le`, the von Mangoldt Mertens deviation around `-γ` decays like
`O(exp(-c √(log x)))`. -/
theorem exists_mertensDeviation_exp_sqrt_log_bound :
    ∃ c > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
      |(∑ k ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt k / (k : ℝ)) -
          Real.log x + Real.eulerMascheroniConstant| ≤
        C * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c, hc0, hbigO⟩ := Sieve.chebyshevPsi_sub_id_isBigO
  rw [Asymptotics.isBigO_iff] at hbigO
  obtain ⟨K, hKev⟩ := hbigO
  rw [eventually_atTop] at hKev
  obtain ⟨T₀, hT₀⟩ := hKev
  set T : ℝ := max T₀ 2 with hTdef
  have hT2 : (2 : ℝ) ≤ T := le_max_right _ _
  have hbdT : ∀ t : ℝ, T < t →
      |chebyshevError t| ≤ |K| * t * Real.exp (-c * Real.sqrt (Real.log t)) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans (by linarith) ht
    have h := hT₀ t (le_trans (le_max_left _ _) ht.le)
    have hgn : ‖t * Real.exp (-c * Real.sqrt (Real.log t))‖ =
        t * Real.exp (-c * Real.sqrt (Real.log t)) := by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [Pi.sub_apply, id_eq, Real.norm_eq_abs, hgn] at h
    unfold chebyshevError
    have hE : (0 : ℝ) < Real.exp (-c * Real.sqrt (Real.log t)) := Real.exp_pos _
    nlinarith [le_abs_self K, h, mul_pos ht0 hE]
  refine ⟨c / 2, by linarith, |K| + |K| * (4 / c ^ (2 : ℕ)), by positivity, ?_⟩
  filter_upwards [eventually_gt_atTop T, eventually_ge_atTop (2 : ℝ)] with x hxT hx2
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx1_lt : (1 : ℝ) < x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  rw [mertensDeviation_eq hx1]
  have hb1 : |chebyshevError x / x| ≤
      |K| * Real.exp (-(c / 2) * Real.sqrt (Real.log x)) := by
    have hb := hbdT x hxT
    rw [abs_div, abs_of_pos hx0, div_le_iff₀ hx0]
    calc
      |chebyshevError x| ≤ |K| * x * Real.exp (-c * Real.sqrt (Real.log x)) := hb
      _ ≤ |K| * x * Real.exp (-(c / 2) * Real.sqrt (Real.log x)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp.mpr
        have : 0 ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
        nlinarith
      _ = |K| * Real.exp (-(c / 2) * Real.sqrt (Real.log x)) * x := by ring
  have hEint : IntegrableOn (fun t : ℝ => chebyshevError t / t ^ (2 : ℕ)) (Ioi x) :=
    integrableOn_chebyshevError_div_sq.mono_set (Ioi_subset_Ioi hx1)
  have hmaj : IntegrableOn
      (fun t : ℝ => |K| * (Real.exp (-c * Real.sqrt (Real.log t)) / t)) (Ioi x) :=
    (Sieve.integrableOn_expSqrtLog_div_Ioi hc0 hx1_lt).const_mul |K|
  have hptwise : ∀ t ∈ Ioi x,
      |chebyshevError t / t ^ (2 : ℕ)| ≤
        |K| * (Real.exp (-c * Real.sqrt (Real.log t)) / t) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans hx0 ht
    have hsq : (0 : ℝ) < t ^ (2 : ℕ) := by positivity
    rw [abs_div, abs_of_pos hsq, div_le_iff₀ hsq]
    have hstep : |K| * (Real.exp (-c * Real.sqrt (Real.log t)) / t) * t ^ (2 : ℕ) =
        |K| * t * Real.exp (-c * Real.sqrt (Real.log t)) := by
      field_simp [ht0.ne']
    rw [hstep]
    exact hbdT t (lt_trans hxT ht)
  have hb2 : |∫ t in Ioi x, chebyshevError t / t ^ (2 : ℕ)| ≤
      |K| * (4 / c ^ (2 : ℕ)) * Real.exp (-(c / 2) * Real.sqrt (Real.log x)) := by
    have hstep1 : |∫ t in Ioi x, chebyshevError t / t ^ (2 : ℕ)| ≤
        ∫ t in Ioi x, |chebyshevError t / t ^ (2 : ℕ)| := by
      have hnorm := MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict (Ioi x))
        (fun t : ℝ => chebyshevError t / t ^ (2 : ℕ))
      simp_rw [Real.norm_eq_abs] at hnorm
      exact hnorm
    have hstep2 : ∫ t in Ioi x, |chebyshevError t / t ^ (2 : ℕ)| ≤
        ∫ t in Ioi x, |K| * (Real.exp (-c * Real.sqrt (Real.log t)) / t) :=
      setIntegral_mono_on hEint.abs hmaj measurableSet_Ioi hptwise
    have hstep3 : ∫ t in Ioi x, |K| * (Real.exp (-c * Real.sqrt (Real.log t)) / t) =
        |K| * Sieve.sqrtLogTail c x := by
      rw [MeasureTheory.integral_const_mul, Sieve.integral_expSqrtLog_div_Ioi hc0 hx1_lt]
    have hstep4 : |K| * Sieve.sqrtLogTail c x ≤
        |K| * (4 / c ^ (2 : ℕ)) * Real.exp (-(c / 2) * Real.sqrt (Real.log x)) := by
      have := mul_le_mul_of_nonneg_left (Sieve.sqrtLogTail_le (c := c) (t := x) hc0) (abs_nonneg K)
      linarith
    linarith
  calc
    |chebyshevError x / x - ∫ t in Ioi x, chebyshevError t / t ^ (2 : ℕ)| ≤
      |chebyshevError x / x| + |∫ t in Ioi x, chebyshevError t / t ^ (2 : ℕ)| := abs_sub _ _
    _ ≤ |K| * Real.exp (-(c / 2) * Real.sqrt (Real.log x)) +
        |K| * (4 / c ^ (2 : ℕ)) * Real.exp (-(c / 2) * Real.sqrt (Real.log x)) :=
      add_le_add hb1 hb2
    _ = (|K| + |K| * (4 / c ^ (2 : ℕ))) * Real.exp (-(c / 2) * Real.sqrt (Real.log x)) := by ring

/-- **Global Natural-Index Exponential-`√(log d)` Bound for the Mertens Deviation:**
There exist `c > 0` and `C ≥ 0` such that for ALL `d ≥ 1`,
`|mertensSum d - log d + γ| ≤ C * exp(-c * √(log d))`. -/
theorem exists_global_mertensDeviation_exp_sqrt_log_bound :
    ∃ c > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℕ, 1 ≤ d →
      |mertensSum d - Real.log (d : ℝ) + Real.eulerMascheroniConstant| ≤
        C * Real.exp (-c * Real.sqrt (Real.log (d : ℝ))) := by
  obtain ⟨c, hc0, C₀, hC₀, hev⟩ := exists_mertensDeviation_exp_sqrt_log_bound
  have hevNat := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hev
  rw [eventually_atTop] at hevNat
  obtain ⟨N₀, hN₀⟩ := hevNat
  let C₁ : ℝ := 7 * Real.exp (c * Real.sqrt (Real.log (max N₀ 1 : ℝ)))
  refine ⟨c, hc0, max C₀ C₁, le_max_of_le_left hC₀, fun d hd => ?_⟩
  rcases le_or_gt N₀ d with hdN | hdN
  · have h := hN₀ d hdN
    rw [Nat.floor_natCast, ← mertensSum_eq_Icc_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · have h7 := abs_mertensDeviation_le_seven hd
    have hlog : Real.log (d : ℝ) ≤ Real.log (max N₀ 1 : ℝ) := by
      apply Real.log_le_log (by exact_mod_cast hd)
      exact_mod_cast (show d ≤ max N₀ 1 by omega)
    have hsqrt : Real.sqrt (Real.log (d : ℝ)) ≤ Real.sqrt (Real.log (max N₀ 1 : ℝ)) :=
      Real.sqrt_le_sqrt hlog
    have hexp : 1 ≤ Real.exp (c * Real.sqrt (Real.log (max N₀ 1 : ℝ))) *
        Real.exp (-c * Real.sqrt (Real.log (d : ℝ))) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      nlinarith
    calc
      |mertensSum d - Real.log (d : ℝ) + Real.eulerMascheroniConstant| ≤ 7 := h7
      _ ≤ 7 * (Real.exp (c * Real.sqrt (Real.log (max N₀ 1 : ℝ))) *
          Real.exp (-c * Real.sqrt (Real.log (d : ℝ)))) :=
        le_mul_of_one_le_right (by norm_num) hexp
      _ = C₁ * Real.exp (-c * Real.sqrt (Real.log (d : ℝ))) := by dsimp [C₁]; ring
      _ ≤ max C₀ C₁ * Real.exp (-c * Real.sqrt (Real.log (d : ℝ))) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

/-- **Upgraded Exponential-`√ L` Frontier Bound for `weilLagFunctionReal`:**
`|weilLagFunctionReal L| ≤ C * exp(L / 2) * exp(-c * √L)` for large `L`, upgrading
`weilLagFunctionReal_frontier` from `L^{1/10}` to `√L`. -/
theorem weilLagFunctionReal_frontier_sqrt_log :
    ∃ c > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ L : ℝ in atTop,
      |weilLagFunctionReal L| ≤ C * Real.exp (L / 2) * Real.exp (-c * Real.sqrt L) := by
  obtain ⟨c₁, hc₁, hbigO⟩ := Sieve.chebyshevPsi_sub_id_isBigO
  rw [Asymptotics.isBigO_iff] at hbigO
  obtain ⟨K, hKev⟩ := hbigO
  obtain ⟨c₂, hc₂, C₂, hC₂0, hM⟩ := exists_mertensDeviation_exp_sqrt_log_bound
  set c : ℝ := min (min c₁ c₂) 1 with hc
  have hc0 : 0 < c := by positivity
  have hcc₁ : c ≤ c₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hcc₂ : c ≤ c₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hc1 : c ≤ 1 := min_le_right _ _
  have hl0 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  refine ⟨c, hc0, |K| + C₂ + (Real.log (2 * Real.pi) + 1), by linarith [abs_nonneg K], ?_⟩
  filter_upwards [Real.tendsto_exp_atTop.eventually hKev, Real.tendsto_exp_atTop.eventually hM,
    eventually_ge_atTop (1 : ℝ)] with L hEL hML hL1
  have hL0 : 0 < L := by linarith
  have hX1 : (1 : ℝ) ≤ Real.exp L := by
    have := Real.add_one_le_exp L; linarith
  have hsqrtL0 : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
  rw [weilLagFunctionReal_eq_prime_side hL0, mertensSum_eq_Icc_zero]
  rw [Real.log_exp] at hEL hML
  set D : ℝ := Real.exp (-c * Real.sqrt L) with hD
  have hDle : ∀ c' : ℝ, c ≤ c' → Real.exp (-c' * Real.sqrt L) ≤ D := by
    intro c' hc'
    rw [hD]; apply Real.exp_le_exp.mpr; nlinarith
  have hp1 : |Real.exp (-L / 2) * (Real.exp L - Chebyshev.psi (Real.exp L))| ≤
      |K| * Real.exp (L / 2) * D := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_sub_comm]
    have hgn : ‖Real.exp L * Real.exp (-c₁ * Real.sqrt L)‖ =
        Real.exp L * Real.exp (-c₁ * Real.sqrt L) := by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [Pi.sub_apply, id_eq, Real.norm_eq_abs, hgn] at hEL
    have hEL' : |Chebyshev.psi (Real.exp L) - Real.exp L| ≤
        |K| * (Real.exp L * Real.exp (-c₁ * Real.sqrt L)) :=
      hEL.trans (mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity))
    calc
      Real.exp (-L / 2) * |Chebyshev.psi (Real.exp L) - Real.exp L| ≤
        Real.exp (-L / 2) * (|K| * (Real.exp L * Real.exp (-c₁ * Real.sqrt L))) :=
        mul_le_mul_of_nonneg_left hEL' (Real.exp_pos _).le
      _ ≤ Real.exp (-L / 2) * (|K| * (Real.exp L * D)) := by
        gcongr
        exact hDle c₁ hcc₁
      _ = |K| * Real.exp (L / 2) * D := by
        rw [show Real.exp (-L / 2) * (|K| * (Real.exp L * D)) =
          |K| * (Real.exp (-L / 2) * Real.exp L) * D by ring, ← Real.exp_add]
        congr 2; ring
  have hp2 : |Real.exp (L / 2) * ((∑ k ∈ Finset.Icc 0 ⌊Real.exp L⌋₊, vonMangoldt k / (k : ℝ)) - L +
      Real.eulerMascheroniConstant)| ≤ C₂ * Real.exp (L / 2) * D := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (L / 2) * |(∑ k ∈ Finset.Icc 0 ⌊Real.exp L⌋₊, vonMangoldt k / (k : ℝ)) - L +
          Real.eulerMascheroniConstant| ≤
        Real.exp (L / 2) * (C₂ * Real.exp (-c₂ * Real.sqrt L)) := by gcongr
      _ ≤ Real.exp (L / 2) * (C₂ * D) := by gcongr; exact hDle c₂ hcc₂
      _ = C₂ * Real.exp (L / 2) * D := by ring
  have hp3 : |Real.exp (-L / 2) * (trivialZeroSeriesReal (Real.exp L) - Real.log (2 * Real.pi))| ≤
      (Real.log (2 * Real.pi) + 1) * Real.exp (L / 2) * D := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hS0 := trivialZeroSeriesReal_nonneg hX1
    have hS1 := trivialZeroSeriesReal_le_one hX1
    have habs : |trivialZeroSeriesReal (Real.exp L) - Real.log (2 * Real.pi)| ≤
        Real.log (2 * Real.pi) + 1 := by
      rw [abs_le]; constructor <;> linarith
    have hexp : Real.exp (-L / 2) ≤ Real.exp (L / 2) * D := by
      rw [hD, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
      have hs1 : 1 ≤ Real.sqrt L := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hL1
      nlinarith
    calc
      Real.exp (-L / 2) * |trivialZeroSeriesReal (Real.exp L) - Real.log (2 * Real.pi)| ≤
        (Real.exp (L / 2) * D) * (Real.log (2 * Real.pi) + 1) :=
        mul_le_mul hexp habs (abs_nonneg _) (by positivity)
      _ = (Real.log (2 * Real.pi) + 1) * Real.exp (L / 2) * D := by ring
  have hsplit : Real.exp (-L / 2) * ((Real.exp L - Chebyshev.psi (Real.exp L)) +
      Real.exp L * ((∑ k ∈ Finset.Icc 0 ⌊Real.exp L⌋₊, vonMangoldt k / (k : ℝ)) - L +
        Real.eulerMascheroniConstant) - Real.log (2 * Real.pi) + trivialZeroSeriesReal (Real.exp L)) =
      Real.exp (-L / 2) * (Real.exp L - Chebyshev.psi (Real.exp L)) +
        Real.exp (L / 2) * ((∑ k ∈ Finset.Icc 0 ⌊Real.exp L⌋₊, vonMangoldt k / (k : ℝ)) - L +
          Real.eulerMascheroniConstant) +
        Real.exp (-L / 2) * (trivialZeroSeriesReal (Real.exp L) - Real.log (2 * Real.pi)) := by
    have : Real.exp (-L / 2) * Real.exp L = Real.exp (L / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [← this]; ring
  rw [hsplit]
  calc
    _ ≤ |Real.exp (-L / 2) * (Real.exp L - Chebyshev.psi (Real.exp L))| +
        |Real.exp (L / 2) * ((∑ k ∈ Finset.Icc 0 ⌊Real.exp L⌋₊, vonMangoldt k / (k : ℝ)) - L +
          Real.eulerMascheroniConstant)| +
        |Real.exp (-L / 2) * (trivialZeroSeriesReal (Real.exp L) - Real.log (2 * Real.pi))| :=
      abs_add_three _ _ _
    _ ≤ |K| * Real.exp (L / 2) * D + C₂ * Real.exp (L / 2) * D +
        (Real.log (2 * Real.pi) + 1) * Real.exp (L / 2) * D :=
      add_le_add (add_le_add hp1 hp2) hp3
    _ = (|K| + C₂ + (Real.log (2 * Real.pi) + 1)) * Real.exp (L / 2) * D := by ring

/-- **Global Exponential-`√(log d)` Bound for `integerLag d`:**
There exist `c > 0` and `C ≥ 0` such that for ALL `d ≥ 2`,
`|integerLag d| ≤ C * √d * exp(-c * √(log d))`. -/
theorem exists_global_integerLag_exp_sqrt_log_bound :
    ∃ c > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℕ, 2 ≤ d →
      |integerLag d| ≤ C * Real.sqrt (d : ℝ) * Real.exp (-c * Real.sqrt (Real.log (d : ℝ))) := by
  obtain ⟨c, hc0, C₀, hC₀, hL⟩ := weilLagFunctionReal_frontier_sqrt_log
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp hL
  let N₀ : ℕ := ⌈Real.exp L₀⌉₊ + 2
  let C₁ : ℝ := 20 * Real.exp (c * Real.sqrt (Real.log (N₀ : ℝ)))
  refine ⟨c, hc0, max C₀ C₁, le_max_of_le_left hC₀, fun d hd => ?_⟩
  rcases le_or_gt N₀ d with hdN | hdN
  · have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have hlog : L₀ ≤ Real.log (d : ℝ) := by
      rw [← Real.log_exp L₀]
      apply Real.log_le_log (Real.exp_pos _)
      calc
        Real.exp L₀ ≤ ⌈Real.exp L₀⌉₊ := Nat.le_ceil _
        _ ≤ d := by exact_mod_cast (show ⌈Real.exp L₀⌉₊ ≤ d by omega)
    have h := hL₀ (Real.log (d : ℝ)) hlog
    have hsqrt : Real.exp (Real.log (d : ℝ) / 2) = Real.sqrt (d : ℝ) := by
      rw [Real.exp_half, Real.exp_log hd0]
    unfold integerLag
    rw [hsqrt] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)) (Real.exp_pos _).le)
  · have h20 := abs_integerLag_le_twenty_mul_sqrt hd
    have hlog : Real.log (d : ℝ) ≤ Real.log (N₀ : ℝ) := by
      apply Real.log_le_log (by exact_mod_cast (show 0 < d by omega))
      exact_mod_cast hdN.le
    have hsqrt : Real.sqrt (Real.log (d : ℝ)) ≤ Real.sqrt (Real.log (N₀ : ℝ)) :=
      Real.sqrt_le_sqrt hlog
    have hexp : 1 ≤ Real.exp (c * Real.sqrt (Real.log (N₀ : ℝ))) *
        Real.exp (-c * Real.sqrt (Real.log (d : ℝ))) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      nlinarith
    calc
      |integerLag d| ≤ 20 * Real.sqrt (d : ℝ) := h20
      _ ≤ 20 * Real.sqrt (d : ℝ) *
          (Real.exp (c * Real.sqrt (Real.log (N₀ : ℝ))) *
            Real.exp (-c * Real.sqrt (Real.log (d : ℝ)))) :=
        le_mul_of_one_le_right (by positivity) hexp
      _ = C₁ * Real.sqrt (d : ℝ) * Real.exp (-c * Real.sqrt (Real.log (d : ℝ))) := by
        dsimp [C₁]; ring
      _ ≤ max C₀ C₁ * Real.sqrt (d : ℝ) * Real.exp (-c * Real.sqrt (Real.log (d : ℝ))) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)) (Real.exp_pos _).le

/-- **Global Exponential-`√(log d)` Decay of `completedSourceObserverJetMass d`:**
There exist `c > 0` and `C ≥ 0` such that for ALL `d ≥ 2`,
`|completedSourceObserverJetMass d| ≤ C * exp(-c * √(log d))`. -/
theorem exists_global_completedSourceObserverJetMass_exp_sqrt_log_bound :
    ∃ c > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℕ, 2 ≤ d →
      |completedSourceObserverJetMass d| ≤
        C * Real.exp (-c * Real.sqrt (Real.log (d : ℝ))) := by
  obtain ⟨c, hc0, C₀, hC₀, hlag⟩ := exists_global_integerLag_exp_sqrt_log_bound
  have h1 := Sieve.one_div_le_exp_neg_sqrt_log hc0
  have h1Nat := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually h1
  rw [eventually_atTop] at h1Nat
  obtain ⟨N₀, hN₀⟩ := h1Nat
  let Cγ : ℝ := 7 + |2 * Real.eulerMascheroniConstant|
  let C₁ : ℝ := Cγ * Real.exp (c * Real.sqrt (Real.log (max N₀ 2 : ℝ)))
  refine ⟨c, hc0, C₀ + max Cγ C₁, by positivity, fun d hd => ?_⟩
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hsd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hd0
  have hbridge := abs_completedSourceObserverJetMass_sub_integerLag_div_sqrt_le hd
  have hterm1 : |integerLag d / Real.sqrt (d : ℝ)| ≤
      C₀ * Real.exp (-c * Real.sqrt (Real.log (d : ℝ))) := by
    rw [abs_div, abs_of_pos hsd, div_le_iff₀ hsd]
    have h := hlag d hd
    linarith
  have hterm2 : Cγ / (d : ℝ) ≤
      max Cγ C₁ * Real.exp (-c * Real.sqrt (Real.log (d : ℝ))) := by
    rcases le_or_gt N₀ d with hdN | hdN
    · have hdiv : 1 / (d : ℝ) ≤ Real.exp (-c * Real.sqrt (Real.log (d : ℝ))) := hN₀ d hdN
      calc
        Cγ / (d : ℝ) = Cγ * (1 / (d : ℝ)) := by ring
        _ ≤ Cγ * Real.exp (-c * Real.sqrt (Real.log (d : ℝ))) :=
          mul_le_mul_of_nonneg_left hdiv (by dsimp [Cγ]; positivity)
        _ ≤ max Cγ C₁ * Real.exp (-c * Real.sqrt (Real.log (d : ℝ))) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    · have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
      have hdiv1 : Cγ / (d : ℝ) ≤ Cγ := div_le_self (by dsimp [Cγ]; positivity) hd1
      have hlog : Real.log (d : ℝ) ≤ Real.log (max N₀ 2 : ℝ) := by
        apply Real.log_le_log hd0
        exact_mod_cast (show d ≤ max N₀ 2 by omega)
      have hsqrt : Real.sqrt (Real.log (d : ℝ)) ≤ Real.sqrt (Real.log (max N₀ 2 : ℝ)) :=
        Real.sqrt_le_sqrt hlog
      have hexp : 1 ≤ Real.exp (c * Real.sqrt (Real.log (max N₀ 2 : ℝ))) *
          Real.exp (-c * Real.sqrt (Real.log (d : ℝ))) := by
        rw [← Real.exp_add, Real.one_le_exp_iff]
        nlinarith
      calc
        Cγ / (d : ℝ) ≤ Cγ := hdiv1
        _ ≤ Cγ * (Real.exp (c * Real.sqrt (Real.log (max N₀ 2 : ℝ))) *
            Real.exp (-c * Real.sqrt (Real.log (d : ℝ)))) :=
          le_mul_of_one_le_right (by dsimp [Cγ]; positivity) hexp
        _ = C₁ * Real.exp (-c * Real.sqrt (Real.log (d : ℝ))) := by dsimp [C₁]; ring
        _ ≤ max Cγ C₁ * Real.exp (-c * Real.sqrt (Real.log (d : ℝ))) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  calc
    |completedSourceObserverJetMass d| =
      |(completedSourceObserverJetMass d - integerLag d / Real.sqrt (d : ℝ)) +
        integerLag d / Real.sqrt (d : ℝ)| := by ring_nf
    _ ≤ |completedSourceObserverJetMass d - integerLag d / Real.sqrt (d : ℝ)| +
        |integerLag d / Real.sqrt (d : ℝ)| := abs_add_le _ _
    _ ≤ Cγ / (d : ℝ) + C₀ * Real.exp (-c * Real.sqrt (Real.log (d : ℝ))) :=
      add_le_add hbridge hterm1
    _ ≤ max Cγ C₁ * Real.exp (-c * Real.sqrt (Real.log (d : ℝ))) +
        C₀ * Real.exp (-c * Real.sqrt (Real.log (d : ℝ))) := add_le_add hterm2 le_rfl
    _ = (C₀ + max Cγ C₁) * Real.exp (-c * Real.sqrt (Real.log (d : ℝ))) := by ring

/-- **Exponentially Damped Multi-Step Lipschitz Bound for `lagBracket` and `integerLag`:**
There exist `c > 0` and `C ≥ 0` such that for all `2 ≤ n ≤ m ≤ 2 * n`:
1. `|lagBracket m - lagBracket n| ≤ C * (m - n) * exp(-c * √(log n)) + 2`, and
2. `|integerLag m - integerLag n| ≤ C * ((m - n) / √n) * exp(-c * √(log n)) + 2 / √n`.
Consequently, `integerLag` varies by `o(1)` across any `O(√n)` window (such as between consecutive
perfect squares `[N^2, (N + 1)^2]`), and varies by `O(1)` across any super-`√n` window of length
`O(√n * exp(c * √(log n)))`. -/
theorem exists_exponentially_damped_integerLag_lipschitz :
    ∃ c > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ {n m : ℕ}, 2 ≤ n → n ≤ m → m ≤ 2 * n →
      |lagBracket m - lagBracket n| ≤
          C * ((m - n : ℕ) : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) + 2 ∧
        |integerLag m - integerLag n| ≤
          C * (((m - n : ℕ) : ℝ) / Real.sqrt (n : ℝ)) *
            Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) + 2 / Real.sqrt (n : ℝ) := by
  obtain ⟨c₁, hc₁, C₁, hC₁, hMert⟩ := exists_global_mertensDeviation_exp_sqrt_log_bound
  obtain ⟨c₂, hc₂, C₂, hC₂, hLag⟩ := exists_global_integerLag_exp_sqrt_log_bound
  let c : ℝ := min c₁ c₂
  have hc0 : 0 < c := lt_min hc₁ hc₂
  let C : ℝ := C₁ + C₂
  refine ⟨c, hc0, C, by dsimp [C]; positivity, fun {n m} hn2 hnm hm2n => ?_⟩
  have hm2 : 2 ≤ m := hn2.trans hnm
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hm0 : (0 : ℝ) < m := by linarith
  have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have hm2n' : (m : ℝ) ≤ 2 * n := by exact_mod_cast hm2n
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hsm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm0
  have hsnm : Real.sqrt (n : ℝ) ≤ Real.sqrt (m : ℝ) := Real.sqrt_le_sqrt hnm'
  set g : ℝ := ((m - n : ℕ) : ℝ) with hg
  have hg_eq : g = (m : ℝ) - n := by rw [hg]; push_cast [Nat.cast_sub hnm]; ring
  have hg0 : 0 ≤ g := by rw [hg_eq]; linarith
  let En : ℝ := Real.exp (-c * Real.sqrt (Real.log (n : ℝ)))
  have hEn_pos : 0 < En := Real.exp_pos _
  -- Step 1: bound `|m * lagBracketSlope m - n * lagBracketSlope n|`
  have hslope_diff :
      |(m : ℝ) * lagBracketSlope m - (n : ℝ) * lagBracketSlope n| ≤
        C₁ * g * En + 1 := by
    rw [mul_lagBracketSlope_sub_eq_sum_Ico hnm]
    have hterm : ∀ d ∈ Finset.Ico n m,
        |((d + 1 : ℕ) : ℝ) * lagBracketSlope (d + 1) - (d : ℝ) * lagBracketSlope d| ≤
          C₁ * En + 1 / (n : ℝ) := by
      intro d hd
      have hdn : n ≤ d := (Finset.mem_Ico.mp hd).1
      have hd1 : 1 ≤ d := by omega
      have hstep := abs_mul_lagBracketSlope_succ_sub_mertensDeviation_le hd1
      have hM := hMert d hd1
      have hlog : Real.sqrt (Real.log (n : ℝ)) ≤ Real.sqrt (Real.log (d : ℝ)) :=
        Real.sqrt_le_sqrt (Real.log_le_log hn0 (by exact_mod_cast hdn))
      have hexp : Real.exp (-c₁ * Real.sqrt (Real.log (d : ℝ))) ≤ En := by
        dsimp [En]
        apply Real.exp_le_exp.mpr
        have hc_le : c ≤ c₁ := min_le_left _ _
        have hsd0 : 0 ≤ Real.sqrt (Real.log (d : ℝ)) := Real.sqrt_nonneg _
        nlinarith
      have hinv : 1 / (d : ℝ) ≤ 1 / (n : ℝ) :=
        one_div_le_one_div_of_le hn0 (by exact_mod_cast hdn)
      calc
        |((d + 1 : ℕ) : ℝ) * lagBracketSlope (d + 1) - (d : ℝ) * lagBracketSlope d| =
          |(((d + 1 : ℕ) : ℝ) * lagBracketSlope (d + 1) - (d : ℝ) * lagBracketSlope d -
              (mertensSum d - Real.log (d : ℝ) + Real.eulerMascheroniConstant)) +
            (mertensSum d - Real.log (d : ℝ) + Real.eulerMascheroniConstant)| := by ring_nf
        _ ≤ |((d + 1 : ℕ) : ℝ) * lagBracketSlope (d + 1) - (d : ℝ) * lagBracketSlope d -
              (mertensSum d - Real.log (d : ℝ) + Real.eulerMascheroniConstant)| +
            |mertensSum d - Real.log (d : ℝ) + Real.eulerMascheroniConstant| := abs_add_le _ _
        _ ≤ 1 / (d : ℝ) + |mertensSum d - Real.log (d : ℝ) + Real.eulerMascheroniConstant| :=
          add_le_add hstep le_rfl
        _ ≤ 1 / (n : ℝ) + C₁ * Real.exp (-c₁ * Real.sqrt (Real.log (d : ℝ))) :=
          add_le_add hinv hM
        _ ≤ 1 / (n : ℝ) + C₁ * En := add_le_add le_rfl (mul_le_mul_of_nonneg_left hexp hC₁)
        _ = C₁ * En + 1 / (n : ℝ) := by ring
    have hg_div : g * (1 / (n : ℝ)) ≤ 1 := by
      rw [hg_eq, mul_one_div, div_le_one hn0]
      linarith
    calc
      |∑ d ∈ Finset.Ico n m,
          (((d + 1 : ℕ) : ℝ) * lagBracketSlope (d + 1) - (d : ℝ) * lagBracketSlope d)| ≤
        ∑ d ∈ Finset.Ico n m, (C₁ * En + 1 / (n : ℝ)) :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
      _ = g * (C₁ * En + 1 / (n : ℝ)) := by
        simp [Nat.card_Ico, hg]
        ring
      _ = C₁ * g * En + g * (1 / (n : ℝ)) := by ring
      _ ≤ C₁ * g * En + 1 := add_le_add le_rfl hg_div
  -- Step 2: bound `|lagBracket m - lagBracket n|`
  have hS : |trivialZeroSeriesReal m - trivialZeroSeriesReal n| ≤ 1 := by
    have hSm0 := trivialZeroSeriesReal_nonneg hm1
    have hSn1 := trivialZeroSeriesReal_le_one hn1
    have hSanti := trivialZeroSeriesReal_anti hn1 hnm'
    rw [abs_le]; constructor <;> linarith
  have hbracket_diff :
      |lagBracket m - lagBracket n| ≤ C * g * En + 2 := by
    have hsplit :
        lagBracket m - lagBracket n =
          ((m : ℝ) * lagBracketSlope m - (n : ℝ) * lagBracketSlope n) +
            (trivialZeroSeriesReal m - trivialZeroSeriesReal n) := by
      rw [lagBracket_eq_mul_lagBracketSlope_sub m, lagBracket_eq_mul_lagBracketSlope_sub n]
      ring
    rw [hsplit]
    have hleC : C₁ * g * En ≤ C * g * En := by
      dsimp [C]
      nlinarith [mul_nonneg hg0 hEn_pos.le]
    calc
      |((m : ℝ) * lagBracketSlope m - (n : ℝ) * lagBracketSlope n) +
          (trivialZeroSeriesReal m - trivialZeroSeriesReal n)| ≤
        |(m : ℝ) * lagBracketSlope m - (n : ℝ) * lagBracketSlope n| +
          |trivialZeroSeriesReal m - trivialZeroSeriesReal n| := abs_add_le _ _
      _ ≤ (C₁ * g * En + 1) + 1 := add_le_add hslope_diff hS
      _ ≤ C * g * En + 2 := by linarith
  refine ⟨hbracket_diff, ?_⟩
  -- Step 3: bound `|integerLag m - integerLag n|`
  have hEm : |lagBracket m| ≤ C₂ * (m : ℝ) * En := by
    have hL := hLag m hm2
    rw [integerLag_eq_lagBracket hm2, abs_div, abs_of_pos hsm, div_le_iff₀ hsm] at hL
    have hsq_m : Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) = (m : ℝ) := Real.mul_self_sqrt hm0.le
    have hlog : Real.sqrt (Real.log (n : ℝ)) ≤ Real.sqrt (Real.log (m : ℝ)) :=
      Real.sqrt_le_sqrt (Real.log_le_log hn0 hnm')
    have hexp : Real.exp (-c₂ * Real.sqrt (Real.log (m : ℝ))) ≤ En := by
      dsimp [En]
      apply Real.exp_le_exp.mpr
      have hc_le : c ≤ c₂ := min_le_right _ _
      have hsm0 : 0 ≤ Real.sqrt (Real.log (m : ℝ)) := Real.sqrt_nonneg _
      nlinarith
    calc
      |lagBracket m| ≤
        C₂ * Real.sqrt (m : ℝ) * Real.exp (-c₂ * Real.sqrt (Real.log (m : ℝ))) * Real.sqrt (m : ℝ) := hL
      _ = C₂ * (Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ)) *
          Real.exp (-c₂ * Real.sqrt (Real.log (m : ℝ))) := by ring
      _ = C₂ * (m : ℝ) * Real.exp (-c₂ * Real.sqrt (Real.log (m : ℝ))) := by rw [hsq_m]
      _ ≤ C₂ * (m : ℝ) * En := mul_le_mul_of_nonneg_left hexp (by positivity)
  have hinv := inv_sqrt_sub_inv_sqrt_le hn1 hnm'
  have hinv0 : 0 ≤ 1 / Real.sqrt (n : ℝ) - 1 / Real.sqrt (m : ℝ) := by
    have := one_div_le_one_div_of_le hsn hsnm
    linarith
  rw [integerLag_eq_lagBracket hm2, integerLag_eq_lagBracket hn2]
  have hdecomp :
      lagBracket m / Real.sqrt (m : ℝ) - lagBracket n / Real.sqrt (n : ℝ) =
        -(lagBracket m * (1 / Real.sqrt (n : ℝ) - 1 / Real.sqrt (m : ℝ))) +
          (lagBracket m - lagBracket n) / Real.sqrt (n : ℝ) := by
    field_simp
    ring
  rw [hdecomp]
  have ht1 : |lagBracket m * (1 / Real.sqrt (n : ℝ) - 1 / Real.sqrt (m : ℝ))| ≤
      C₂ * (g / Real.sqrt (n : ℝ)) * En := by
    rw [abs_mul, abs_of_nonneg hinv0]
    calc
      |lagBracket m| * (1 / Real.sqrt (n : ℝ) - 1 / Real.sqrt (m : ℝ)) ≤
        (C₂ * (m : ℝ) * En) * (((m : ℝ) - n) / (2 * ((n : ℝ) * Real.sqrt (n : ℝ)))) :=
        mul_le_mul hEm hinv hinv0 (by positivity)
      _ = (C₂ * En) * ((m : ℝ) / (2 * n)) * (g / Real.sqrt (n : ℝ)) := by
        rw [hg_eq]
        field_simp [hn0.ne', hsn.ne']
      _ ≤ (C₂ * En) * 1 * (g / Real.sqrt (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [div_le_one (by positivity)]
        linarith
      _ = C₂ * (g / Real.sqrt (n : ℝ)) * En := by ring
  have ht2 : |(lagBracket m - lagBracket n) / Real.sqrt (n : ℝ)| ≤
      C₁ * (g / Real.sqrt (n : ℝ)) * En + 2 / Real.sqrt (n : ℝ) := by
    rw [abs_div, abs_of_pos hsn]
    have hbd : |lagBracket m - lagBracket n| ≤ C₁ * g * En + 2 := by
      have hsplit :
          lagBracket m - lagBracket n =
            ((m : ℝ) * lagBracketSlope m - (n : ℝ) * lagBracketSlope n) +
              (trivialZeroSeriesReal m - trivialZeroSeriesReal n) := by
        rw [lagBracket_eq_mul_lagBracketSlope_sub m, lagBracket_eq_mul_lagBracketSlope_sub n]
        ring
      rw [hsplit]
      exact (abs_add_le _ _).trans ((add_le_add hslope_diff hS).trans_eq (by ring))
    calc
      |lagBracket m - lagBracket n| / Real.sqrt (n : ℝ) ≤
        (C₁ * g * En + 2) / Real.sqrt (n : ℝ) := div_le_div_of_nonneg_right hbd hsn.le
      _ = C₁ * (g / Real.sqrt (n : ℝ)) * En + 2 / Real.sqrt (n : ℝ) := by ring
  calc
    |-(lagBracket m * (1 / Real.sqrt (n : ℝ) - 1 / Real.sqrt (m : ℝ))) +
        (lagBracket m - lagBracket n) / Real.sqrt (n : ℝ)| ≤
      |lagBracket m * (1 / Real.sqrt (n : ℝ) - 1 / Real.sqrt (m : ℝ))| +
        |(lagBracket m - lagBracket n) / Real.sqrt (n : ℝ)| := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_neg]
    _ ≤ C₂ * (g / Real.sqrt (n : ℝ)) * En +
        (C₁ * (g / Real.sqrt (n : ℝ)) * En + 2 / Real.sqrt (n : ℝ)) := add_le_add ht1 ht2
    _ = C * (g / Real.sqrt (n : ℝ)) * En + 2 / Real.sqrt (n : ℝ) := by dsimp [C]; ring

/-! ## Section 3: Exact `(4/3) M * integerLag M - 2 * integerLagCesaroSum M` Bridge and
Summation by Parts of `integerLagCesaroSum` -/

/-- Exact relation `∑_{k < M - 2} 2 √(k + 2) = 2 * unitRieszSqrtPrefixMass (M - 1) - 2` for `M ≥ 2`. -/
theorem sum_range_two_mul_sqrt_add_two_eq_unitRieszSqrtPrefixMass {M : ℕ} (hM : 2 ≤ M) :
    (∑ k ∈ Finset.range (M - 2), 2 * Real.sqrt (k + 2 : ℕ)) =
      2 * unitRieszSqrtPrefixMass (M - 1) - 2 := by
  have hM1 : M - 1 = (M - 2) + 1 := by omega
  have hprefix :
      unitRieszSqrtPrefixMass (M - 1) =
        (∑ k ∈ Finset.range (M - 2), Real.sqrt (k + 2 : ℕ)) + 1 := by
    unfold unitRieszSqrtPrefixMass
    rw [hM1, Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_add, Real.sqrt_one]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    push_cast
    ring
  rw [hprefix, ← Finset.mul_sum]
  ring

/-- Sharp two-sided sandwich for `∑_{k < M - 2} 2 √(k + 2) - (4 / 3) M √M`:
for every `M ≥ 2`,
`-(4 / 3) * √M - 2 ≤ (∑_{k < M - 2} 2 √(k + 2)) - (4 / 3) * M * √M ≤ -2 ≤ 0`. -/
theorem sum_range_two_mul_sqrt_add_two_sub_four_thirds_bounds {M : ℕ} (hM : 2 ≤ M) :
    -(4 / 3 : ℝ) * Real.sqrt (M : ℝ) - 2 ≤
        (∑ k ∈ Finset.range (M - 2), 2 * Real.sqrt (k + 2 : ℕ)) -
          (4 / 3 : ℝ) * (M : ℝ) * Real.sqrt (M : ℝ) ∧
      (∑ k ∈ Finset.range (M - 2), 2 * Real.sqrt (k + 2 : ℕ)) -
          (4 / 3 : ℝ) * (M : ℝ) * Real.sqrt (M : ℝ) ≤ -2 := by
  rw [sum_range_two_mul_sqrt_add_two_eq_unitRieszSqrtPrefixMass hM]
  have hlower := unitRieszSqrtPrefixMass_lower (M - 1)
  have hupper := unitRieszSqrtPrefixMass_upper (M - 1)
  have hcast1 : ((M - 1 : ℕ) : ℝ) + 1 = (M : ℝ) := by
    exact_mod_cast (show M - 1 + 1 = M by omega)
  have hcast0 : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ M), Nat.cast_one]
  rw [hcast1, hcast0] at hlower
  rw [hcast1] at hupper
  constructor <;> linarith

/-- Uniform `O(√M)` bound `|(∑_{k < M - 2} 2 √(k + 2)) - (4 / 3) M √M| ≤ 4 * √M` for `M ≥ 2`. -/
theorem abs_sum_range_two_mul_sqrt_add_two_sub_four_thirds_le {M : ℕ} (hM : 2 ≤ M) :
    |(∑ k ∈ Finset.range (M - 2), 2 * Real.sqrt (k + 2 : ℕ)) -
        (4 / 3 : ℝ) * (M : ℝ) * Real.sqrt (M : ℝ)| ≤
      4 * Real.sqrt (M : ℝ) := by
  have hb := sum_range_two_mul_sqrt_add_two_sub_four_thirds_bounds hM
  have hs1 : (1 : ℝ) ≤ Real.sqrt (M : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ M by omega))
  rw [abs_le]
  constructor <;> linarith

/-- **Linear–Cesàro Integer-Lag Action:**
`integerLagLinearCesaroAction M = (4 / 3) * M * integerLag M - 2 * integerLagCesaroSum M`. -/
def integerLagLinearCesaroAction (M : ℕ) : ℝ :=
  (4 / 3 : ℝ) * (M : ℝ) * integerLag M - 2 * integerLagCesaroSum M

/-- **Exact `√M`-Cancellation in the Terminal Coefficient of `integerLagSqrtRatioAction`:**
When `(∑_{k < M - 2} 2 √(k + 2))` is replaced by `(4 / 3) M √M` in `integerLagSqrtRatioAction M`,
the `√M` factor cancels against the denominator of `integerLag M / √M` BOTH in the main term
`(4 / 3) M * integerLag M` and in the error term `4 * |integerLag M|`. -/
theorem abs_integerLagSqrtRatioAction_sub_linearCesaroAction_le_four_mul_abs {M : ℕ} (hM : 2 ≤ M) :
    |integerLagSqrtRatioAction M - integerLagLinearCesaroAction M| ≤
      4 * |integerLag M| := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hsM : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hM0
  rw [integerLagSqrtRatioAction_eq_terminal_sub_two_mul_cesaroSum, integerLagLinearCesaroAction]
  have hdiff :
      ((∑ k ∈ Finset.range (M - 2), 2 * Real.sqrt (k + 2 : ℕ)) *
          (integerLag M / Real.sqrt (M : ℝ)) - 2 * integerLagCesaroSum M) -
        ((4 / 3 : ℝ) * (M : ℝ) * integerLag M - 2 * integerLagCesaroSum M) =
      ((∑ k ∈ Finset.range (M - 2), 2 * Real.sqrt (k + 2 : ℕ)) -
          (4 / 3 : ℝ) * (M : ℝ) * Real.sqrt (M : ℝ)) *
        (integerLag M / Real.sqrt (M : ℝ)) := by
    have hcancel :
        (4 / 3 : ℝ) * (M : ℝ) * Real.sqrt (M : ℝ) * (integerLag M / Real.sqrt (M : ℝ)) =
          (4 / 3 : ℝ) * (M : ℝ) * integerLag M := by
      calc
        (4 / 3 : ℝ) * (M : ℝ) * Real.sqrt (M : ℝ) * (integerLag M / Real.sqrt (M : ℝ)) =
          (4 / 3 : ℝ) * (M : ℝ) * ((integerLag M / Real.sqrt (M : ℝ)) * Real.sqrt (M : ℝ)) := by ring
        _ = (4 / 3 : ℝ) * (M : ℝ) * integerLag M := by rw [div_mul_cancel₀ _ hsM.ne']
    calc
      ((∑ k ∈ Finset.range (M - 2), 2 * Real.sqrt (k + 2 : ℕ)) *
          (integerLag M / Real.sqrt (M : ℝ)) - 2 * integerLagCesaroSum M) -
        ((4 / 3 : ℝ) * (M : ℝ) * integerLag M - 2 * integerLagCesaroSum M) =
        (∑ k ∈ Finset.range (M - 2), 2 * Real.sqrt (k + 2 : ℕ)) *
          (integerLag M / Real.sqrt (M : ℝ)) -
          (4 / 3 : ℝ) * (M : ℝ) * integerLag M := by ring
      _ = (∑ k ∈ Finset.range (M - 2), 2 * Real.sqrt (k + 2 : ℕ)) *
          (integerLag M / Real.sqrt (M : ℝ)) -
          (4 / 3 : ℝ) * (M : ℝ) * Real.sqrt (M : ℝ) * (integerLag M / Real.sqrt (M : ℝ)) := by
        rw [hcancel]
      _ = ((∑ k ∈ Finset.range (M - 2), 2 * Real.sqrt (k + 2 : ℕ)) -
          (4 / 3 : ℝ) * (M : ℝ) * Real.sqrt (M : ℝ)) *
          (integerLag M / Real.sqrt (M : ℝ)) := by ring
  rw [hdiff, abs_mul, abs_div, abs_of_pos hsM]
  have hsum := abs_sum_range_two_mul_sqrt_add_two_sub_four_thirds_le hM
  calc
    |(∑ k ∈ Finset.range (M - 2), 2 * Real.sqrt (k + 2 : ℕ)) -
        (4 / 3 : ℝ) * (M : ℝ) * Real.sqrt (M : ℝ)| * (|integerLag M| / Real.sqrt (M : ℝ)) ≤
      (4 * Real.sqrt (M : ℝ)) * (|integerLag M| / Real.sqrt (M : ℝ)) :=
      mul_le_mul_of_nonneg_right hsum (by positivity)
    _ = 4 * ((|integerLag M| / Real.sqrt (M : ℝ)) * Real.sqrt (M : ℝ)) := by ring
    _ = 4 * |integerLag M| := by rw [div_mul_cancel₀ _ hsM.ne']

/-- Unconditional `80 √M` bound on `|integerLagSqrtRatioAction M - integerLagLinearCesaroAction M|`. -/
theorem abs_integerLagSqrtRatioAction_sub_linearCesaroAction_le_sqrt {M : ℕ} (hM : 2 ≤ M) :
    |integerLagSqrtRatioAction M - integerLagLinearCesaroAction M| ≤
      80 * Real.sqrt (M : ℝ) := by
  have h1 := abs_integerLagSqrtRatioAction_sub_linearCesaroAction_le_four_mul_abs hM
  have h2 := abs_integerLag_le_twenty_mul_sqrt hM
  linarith

/-- **Unconditional `O(√M)` Bridge Between `completedSourceObserverJetSqrtMassAction` and
`integerLagLinearCesaroAction`:**
For every `M ≥ 3`,
`|completedSourceObserverJetSqrtMassAction M - integerLagLinearCesaroAction M| ≤ (6 (7 + |2γ|) + 80) √M`. -/
theorem abs_completedSourceObserverJetSqrtMassAction_sub_linearCesaroAction_le {M : ℕ} (hM : 3 ≤ M) :
    |completedSourceObserverJetSqrtMassAction M - integerLagLinearCesaroAction M| ≤
      (6 * (7 + |2 * Real.eulerMascheroniConstant|) + 80) * Real.sqrt (M : ℝ) := by
  have h1 := abs_completedSourceObserverJetSqrtMassAction_sub_integerLagSqrtRatioAction_le hM
  have h2 := abs_integerLagSqrtRatioAction_sub_linearCesaroAction_le_sqrt (by omega : 2 ≤ M)
  calc
    |completedSourceObserverJetSqrtMassAction M - integerLagLinearCesaroAction M| =
      |(completedSourceObserverJetSqrtMassAction M - integerLagSqrtRatioAction M) +
        (integerLagSqrtRatioAction M - integerLagLinearCesaroAction M)| := by ring_nf
    _ ≤ |completedSourceObserverJetSqrtMassAction M - integerLagSqrtRatioAction M| +
        |integerLagSqrtRatioAction M - integerLagLinearCesaroAction M| := abs_add_le _ _
    _ ≤ 6 * (7 + |2 * Real.eulerMascheroniConstant|) * Real.sqrt (M : ℝ) +
        80 * Real.sqrt (M : ℝ) := add_le_add h1 h2
    _ = (6 * (7 + |2 * Real.eulerMascheroniConstant|) + 80) * Real.sqrt (M : ℝ) := by ring

/-- Uniform `O(M)` comparison between `mobiusDivisorSquareRootAbelMoment M` and
`(3 / 8) * integerLagLinearCesaroAction M = (1 / 2) * M * integerLag M - (3 / 4) * integerLagCesaroSum M`. -/
theorem exists_abs_mobiusDivisorSquareRootAbel_sub_linearCesaroAction_linear :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, 3 ≤ M →
      |mobiusDivisorSquareRootAbelMoment M -
        (3 / 8 : ℝ) * integerLagLinearCesaroAction M| ≤ B * (M : ℝ) := by
  obtain ⟨B₀, hB₀, h0⟩ := exists_abs_mobiusDivisorSquareRootAbel_sub_integerLagSqrtRatioAction_linear
  refine ⟨B₀ + 30, by positivity, fun M hM => ?_⟩
  have h1 := h0 M hM
  have h2 := abs_integerLagSqrtRatioAction_sub_linearCesaroAction_le_sqrt (by omega : 2 ≤ M)
  have hsqrt_le : Real.sqrt (M : ℝ) ≤ (M : ℝ) := by
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
    have hsq : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) := Real.mul_self_sqrt (by positivity)
    have hs1 : (1 : ℝ) ≤ Real.sqrt (M : ℝ) := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hM1
    nlinarith
  calc
    |mobiusDivisorSquareRootAbelMoment M -
        (3 / 8 : ℝ) * integerLagLinearCesaroAction M| =
      |(mobiusDivisorSquareRootAbelMoment M - (3 / 8 : ℝ) * integerLagSqrtRatioAction M) +
        (3 / 8 : ℝ) * (integerLagSqrtRatioAction M - integerLagLinearCesaroAction M)| := by ring_nf
    _ ≤ |mobiusDivisorSquareRootAbelMoment M - (3 / 8 : ℝ) * integerLagSqrtRatioAction M| +
        |(3 / 8 : ℝ) * (integerLagSqrtRatioAction M - integerLagLinearCesaroAction M)| :=
      abs_add_le _ _
    _ = |mobiusDivisorSquareRootAbelMoment M - (3 / 8 : ℝ) * integerLagSqrtRatioAction M| +
        (3 / 8 : ℝ) * |integerLagSqrtRatioAction M - integerLagLinearCesaroAction M| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 8)]
    _ ≤ B₀ * (M : ℝ) + (3 / 8 : ℝ) * (80 * Real.sqrt (M : ℝ)) :=
      add_le_add h1 (mul_le_mul_of_nonneg_left h2 (by norm_num))
    _ ≤ B₀ * (M : ℝ) + 30 * (M : ℝ) := by linarith
    _ = (B₀ + 30) * (M : ℝ) := by ring

/-- **One-sided upper RH equivalence for `integerLagLinearCesaroAction`:**
RH holds iff `(4 / 3) * M * integerLag M - 2 * integerLagCesaroSum M ≤ C * M` for all `M ≥ 3`. -/
theorem riemannHypothesis_iff_integerLagLinearCesaroAction_boundedAbove :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ M : ℕ, 3 ≤ M →
        integerLagLinearCesaroAction M ≤ C * (M : ℝ) := by
  obtain ⟨B, _hB0, hB⟩ := exists_abs_mobiusDivisorSquareRootAbel_sub_linearCesaroAction_linear
  rw [riemannHypothesis_iff_mobiusDivisorSquareRootAbel_boundedAbove]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨(8 / 3 : ℝ) * (C + B), fun M hM3 => ?_⟩
    have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    have h1 := (div_le_iff₀ hMpos).mp (hC M (by omega))
    have h2 := (abs_sub_le_iff.mp (hB M hM3)).2
    linarith
  · rintro ⟨C, hC⟩
    obtain ⟨M₀, hM2, hM3⟩ :
        ∃ M₀ : ℝ, mobiusDivisorSquareRootAbelMoment 2 / (2 : ℕ) ≤ M₀ ∧
          (3 / 8 : ℝ) * C + B ≤ M₀ :=
      ⟨max (mobiusDivisorSquareRootAbelMoment 2 / (2 : ℕ)) ((3 / 8 : ℝ) * C + B),
        le_max_left _ _, le_max_right _ _⟩
    refine ⟨M₀, fun M hM => ?_⟩
    by_cases hM_eq_2 : M = 2
    · subst M
      exact hM2
    · clear hM2
      have hM_ge_3 : 3 ≤ M := by omega
      have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
      have h1 := hC M hM_ge_3
      have h2 := (abs_sub_le_iff.mp (hB M hM_ge_3)).1
      have hdiv : mobiusDivisorSquareRootAbelMoment M / (M : ℝ) ≤ (3 / 8 : ℝ) * C + B :=
        (div_le_iff₀ hMpos).mpr (by linarith)
      exact hdiv.trans hM3

/-- **One-sided lower RH equivalence for `integerLagLinearCesaroAction`:**
RH holds iff `-C * M ≤ (4 / 3) * M * integerLag M - 2 * integerLagCesaroSum M` for all `M ≥ 3`. -/
theorem riemannHypothesis_iff_integerLagLinearCesaroAction_boundedBelow :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ M : ℕ, 3 ≤ M →
        -C * (M : ℝ) ≤ integerLagLinearCesaroAction M := by
  obtain ⟨B, _hB0, hB⟩ := exists_abs_mobiusDivisorSquareRootAbel_sub_linearCesaroAction_linear
  rw [riemannHypothesis_iff_mobiusDivisorSquareRootAbel_boundedBelow]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨(8 / 3 : ℝ) * (-C + B), fun M hM3 => ?_⟩
    have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    have h1 := (le_div_iff₀ hMpos).mp (hC M (by omega))
    have h2 := (abs_sub_le_iff.mp (hB M hM3)).1
    linarith
  · rintro ⟨C, hC⟩
    obtain ⟨M₀, hM2, hM3⟩ :
        ∃ M₀ : ℝ, -M₀ ≤ mobiusDivisorSquareRootAbelMoment 2 / (2 : ℕ) ∧
          (3 / 8 : ℝ) * C + B ≤ M₀ :=
      ⟨max (-mobiusDivisorSquareRootAbelMoment 2 / (2 : ℕ)) ((3 / 8 : ℝ) * C + B),
        by
          have h := neg_le_neg (le_max_left (-mobiusDivisorSquareRootAbelMoment 2 / (2 : ℕ))
            ((3 / 8 : ℝ) * C + B))
          simpa [neg_div] using h,
        le_max_right _ _⟩
    refine ⟨-M₀, fun M hM => ?_⟩
    by_cases hM_eq_2 : M = 2
    · subst M
      exact hM2
    · clear hM2
      have hM_ge_3 : 3 ≤ M := by omega
      have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
      have h1 := hC M hM_ge_3
      have h2 := (abs_sub_le_iff.mp (hB M hM_ge_3)).2
      have hdiv : -((3 / 8 : ℝ) * C + B) ≤ mobiusDivisorSquareRootAbelMoment M / (M : ℝ) :=
        (le_div_iff₀ hMpos).mpr (by linarith)
      exact (neg_le_neg hM3).trans hdiv

/-- **Polynomial-schedule (`M = N^m`) upper RH equivalence for `integerLagLinearCesaroAction`.** -/
theorem riemannHypothesis_iff_integerLagLinearCesaroAction_pow_bddAbove
    {m : ℕ} (hm : 1 ≤ m) :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ N : ℕ, 3 ≤ N →
        integerLagLinearCesaroAction (N ^ m) ≤ C * ((N ^ m : ℕ) : ℝ) := by
  obtain ⟨B, _hB0, hB⟩ := exists_abs_mobiusDivisorSquareRootAbel_sub_linearCesaroAction_linear
  rw [riemannHypothesis_iff_mobiusDivisorSquareRootAbel_pow_bddAbove hm]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨(8 / 3 : ℝ) * (C + B), fun N hN3 => ?_⟩
    have hNm3 : 3 ≤ N ^ m :=
      le_trans hN3 (Nat.le_self_pow (by omega : m ≠ 0) N)
    have hpos : (0 : ℝ) < (N ^ m : ℕ) := by exact_mod_cast (show 0 < N ^ m by omega)
    have h1 := (div_le_iff₀ hpos).mp (hC N (by omega))
    have h2 := (abs_sub_le_iff.mp (hB (N ^ m) hNm3)).2
    linarith
  · rintro ⟨C, hC⟩
    obtain ⟨M₀, hM2, hM3⟩ :
        ∃ M₀ : ℝ, mobiusDivisorSquareRootAbelMoment (2 ^ m) / (2 ^ m : ℕ) ≤ M₀ ∧
          (3 / 8 : ℝ) * C + B ≤ M₀ :=
      ⟨max (mobiusDivisorSquareRootAbelMoment (2 ^ m) / (2 ^ m : ℕ)) ((3 / 8 : ℝ) * C + B),
        le_max_left _ _, le_max_right _ _⟩
    refine ⟨M₀, fun N hN2 => ?_⟩
    have hN_ge_2 : 2 ≤ N := by
      by_contra hlt
      have hle1 : N ≤ 1 := by omega
      have hpow : N ^ m ≤ 1 ^ m := Nat.pow_le_pow_left hle1 m
      rw [one_pow] at hpow
      omega
    by_cases hN_eq_2 : N = 2
    · subst N
      exact hM2
    · clear hM2
      have hN3 : 3 ≤ N := by omega
      have hNm3 : 3 ≤ N ^ m :=
        le_trans hN3 (Nat.le_self_pow (by omega : m ≠ 0) N)
      have hpos : (0 : ℝ) < (N ^ m : ℕ) := by exact_mod_cast (show 0 < N ^ m by omega)
      have h1 := hC N hN3
      have h2 := (abs_sub_le_iff.mp (hB (N ^ m) hNm3)).1
      have hdiv : mobiusDivisorSquareRootAbelMoment (N ^ m) / (N ^ m : ℕ) ≤
          (3 / 8 : ℝ) * C + B :=
        (div_le_iff₀ hpos).mpr (by linarith)
      exact hdiv.trans hM3

/-- **Polynomial-schedule (`M = N^m`) lower RH equivalence for `integerLagLinearCesaroAction`.** -/
theorem riemannHypothesis_iff_integerLagLinearCesaroAction_pow_bddBelow
    {m : ℕ} (hm : 1 ≤ m) :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ N : ℕ, 3 ≤ N →
        -C * ((N ^ m : ℕ) : ℝ) ≤ integerLagLinearCesaroAction (N ^ m) := by
  obtain ⟨B, _hB0, hB⟩ := exists_abs_mobiusDivisorSquareRootAbel_sub_linearCesaroAction_linear
  rw [riemannHypothesis_iff_mobiusDivisorSquareRootAbel_pow_bddBelow hm]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨(8 / 3 : ℝ) * (-C + B), fun N hN3 => ?_⟩
    have hNm3 : 3 ≤ N ^ m :=
      le_trans hN3 (Nat.le_self_pow (by omega : m ≠ 0) N)
    have hpos : (0 : ℝ) < (N ^ m : ℕ) := by exact_mod_cast (show 0 < N ^ m by omega)
    have h1 := (le_div_iff₀ hpos).mp (hC N (by omega))
    have h2 := (abs_sub_le_iff.mp (hB (N ^ m) hNm3)).1
    linarith
  · rintro ⟨C, hC⟩
    obtain ⟨M₀, hM2, hM3⟩ :
        ∃ M₀ : ℝ, -M₀ ≤ mobiusDivisorSquareRootAbelMoment (2 ^ m) / (2 ^ m : ℕ) ∧
          (3 / 8 : ℝ) * C + B ≤ M₀ :=
      ⟨max (-mobiusDivisorSquareRootAbelMoment (2 ^ m) / (2 ^ m : ℕ)) ((3 / 8 : ℝ) * C + B),
        by
          have h := neg_le_neg (le_max_left
            (-mobiusDivisorSquareRootAbelMoment (2 ^ m) / (2 ^ m : ℕ))
            ((3 / 8 : ℝ) * C + B))
          simpa [neg_div] using h,
        le_max_right _ _⟩
    refine ⟨-M₀, fun N hN2 => ?_⟩
    have hN_ge_2 : 2 ≤ N := by
      by_contra hlt
      have hle1 : N ≤ 1 := by omega
      have hpow : N ^ m ≤ 1 ^ m := Nat.pow_le_pow_left hle1 m
      rw [one_pow] at hpow
      omega
    by_cases hN_eq_2 : N = 2
    · subst N
      exact hM2
    · clear hM2
      have hN3 : 3 ≤ N := by omega
      have hNm3 : 3 ≤ N ^ m :=
        le_trans hN3 (Nat.le_self_pow (by omega : m ≠ 0) N)
      have hpos : (0 : ℝ) < (N ^ m : ℕ) := by exact_mod_cast (show 0 < N ^ m by omega)
      have h1 := hC N hN3
      have h2 := (abs_sub_le_iff.mp (hB (N ^ m) hNm3)).2
      have hdiv : -((3 / 8 : ℝ) * C + B) ≤
          mobiusDivisorSquareRootAbelMoment (N ^ m) / (N ^ m : ℕ) :=
        (le_div_iff₀ hpos).mpr (by linarith)
      exact (neg_le_neg hM3).trans hdiv

/-- General summation by parts on `Finset.range N` for `(A (k + 1) - A k) * B k` when `A 0 = 0`. -/
theorem sum_range_diff_mul_eq_boundary_sub_sum_mul_diff
    (A B : ℕ → ℝ) (hA0 : A 0 = 0) (N : ℕ) :
    (∑ k ∈ Finset.range N, (A (k + 1) - A k) * B k) =
      A N * B N - ∑ k ∈ Finset.range N, A (k + 1) * (B (k + 1) - B k) := by
  induction N with
  | zero => simp [hA0]
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    ring

/-- Shifted harmonic square-root prefix `harmonicSqrtPrefix (k + 1) - 1 = ∑_{j=1}^k 1 / √(j + 1)`,
whose increments are `1 / √(k + 2)`. -/
def shiftedHarmonicSqrtPrefix (k : ℕ) : ℝ :=
  harmonicSqrtPrefix (k + 1) - 1

@[simp]
theorem shiftedHarmonicSqrtPrefix_zero : shiftedHarmonicSqrtPrefix 0 = 0 := by
  unfold shiftedHarmonicSqrtPrefix
  rw [harmonicSqrtPrefix_succ, harmonicSqrtPrefix_zero]
  simp

theorem shiftedHarmonicSqrtPrefix_succ_sub (k : ℕ) :
    shiftedHarmonicSqrtPrefix (k + 1) - shiftedHarmonicSqrtPrefix k =
      1 / Real.sqrt (k + 2 : ℕ) := by
  unfold shiftedHarmonicSqrtPrefix
  rw [harmonicSqrtPrefix_succ (k + 1)]
  ring

/-- **Exact Abel Summation-by-Parts Identity for `integerLagCesaroSum M`:**
Writing `integerLag (k + 2) = (1 / √(k + 2)) * lagBracket (k + 2)` and summing by parts against
`shiftedHarmonicSqrtPrefix` expresses `integerLagCesaroSum M` in terms of the terminal bracket
`shiftedHarmonicSqrtPrefix (M - 2) * lagBracket M` and the prime-jump-free unit steps
`lagBracket (k + 3) - lagBracket (k + 2)`. -/
theorem integerLagCesaroSum_eq_terminal_sub_sum_lagBracket_diff (M : ℕ) :
    integerLagCesaroSum M =
      shiftedHarmonicSqrtPrefix (M - 2) * lagBracket (M - 2 + 2) -
        ∑ k ∈ Finset.range (M - 2),
          shiftedHarmonicSqrtPrefix (k + 1) * (lagBracket (k + 3) - lagBracket (k + 2)) := by
  have hrewrite :
      integerLagCesaroSum M =
        ∑ k ∈ Finset.range (M - 2),
          (shiftedHarmonicSqrtPrefix (k + 1) - shiftedHarmonicSqrtPrefix k) *
            lagBracket (k + 2) := by
    unfold integerLagCesaroSum
    apply Finset.sum_congr rfl
    intro k _
    rw [shiftedHarmonicSqrtPrefix_succ_sub, integerLag_eq_lagBracket (by omega : 2 ≤ k + 2)]
    ring
  rw [hrewrite,
    sum_range_diff_mul_eq_boundary_sub_sum_mul_diff
      shiftedHarmonicSqrtPrefix (fun k => lagBracket (k + 2))
      shiftedHarmonicSqrtPrefix_zero (M - 2)]

end

end GaloisForLFunctions.RHTower
