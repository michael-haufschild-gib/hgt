import GaloisForLFunctions.RHTower.TerminalLagMertensActionAndSuperSqrtMesh

/-!
# Normalized Chebyshev Cesàro Sum and Square-Root Riesz Action Bridge

This module completes the double Abel summation-by-parts reduction of the observer-jet and
Möbius-divisor square-root Abel moment to a pure, boundary-free prefix sum of the normalized
Chebyshev error `(ψ(d) - d) / √d`:

1. **Summation by Parts of `mertensDeviationSqrtAction M` (`Section 1`):**
   - Summing `mertensDeviationSqrtAction M = ∑_{k < M - 2} 2 √(k + 2) * (mertensSum (k + 2) - log (k + 2) + γ)`
     by parts against `shiftedTwoSqrtPrefix k = ∑_{j < k} 2 √(j + 2)` (which lies within
     `4 √(k + 2)` of `(4 / 3) (k + 2) √(k + 2)`) cancels the `(k + 3)` denominator of the Mertens
     step `Λ(k + 3) / (k + 3)`, yielding for all `M ≥ 2`:
     `|mertensDeviationSqrtAction M - (4 / 3) * (M √M (mertensSum M - log M + γ) - ∑_{k < M - 2} √(k + 3) (Λ(k + 3) - 1))| ≤ 63 * M`.

2. **Exact Cancellation of the Terminal Mertens Deviation and Square-Root Riesz Action (`Section 2`):**
   - Combining `2 * mertensDeviationSqrtAction M` with `-(8 / 3) * M * integerLag M = -(8 / 3) * √M * lagBracket M`
     cancels `-(8 / 3) * M √M (mertensSum M - log M + γ)` against `+(8 / 3) * M √M (mertensSum M - log M + γ)`
     identically!
   - The remaining terms form `(8 / 3) * chebyshevSqrtDiffAction M`, which equals
     `(8 / 3) * vonMangoldtSqrtRieszAction M = (8 / 3) * ∑_{k < M - 2} (√M - √(k + 3)) (Λ(k + 3) - 1)`
     up to `(8 / 3) * √M * (ψ(2) - 2)`.
   - Multiplying by `3 / 8` proves that `mobiusDivisorSquareRootAbelMoment M` agrees with
     `vonMangoldtSqrtRieszAction M` within `O(M)` unconditionally (`exists_abs_mobiusDivisorSquareRootAbel_sub_vonMangoldtSqrtRieszAction_linear`).

3. **Boundary-Free Normalized Chebyshev Cesàro Sum `∑ (ψ(d) - d) / √d` (`Section 3`):**
   - Telescoping `√M (ψ(M) - M) - ∑_{k < M - 2} √(k + 3) (Λ(k + 3) - 1)` via the pointwise ring
     identity `(√(k + 3) E(k + 3) - √(k + 2) E(k + 2)) - √(k + 3) (E(k + 3) - E(k + 2)) = (√(k + 3) - √(k + 2)) E(k + 2)`
     eliminates the moving endpoint `√M` completely up to the `M`-independent constant `√2 (ψ(2) - 2)`.
   - Approximating `√(d + 1) - √d` by `1 / (2 √d)` with error at most `1 / (2 d)` and using
     `|ψ(d) - d| ≤ 6 d` reduces the action within `3 M` to `(1 / 2) * chebyshevNormalizedCesaroSum M`,
     where `chebyshevNormalizedCesaroSum M = ∑_{k < M - 2} (ψ(k + 2) - (k + 2)) / √(k + 2)` has
     summands completely independent of `M`, with no Mertens sum, no `γ`, and no moving endpoint.
   - We establish the one-sided and `M = N^m` RH equivalences for `chebyshevNormalizedCesaroSum`.
-/

open Complex Filter Topology Set MeasureTheory Real
open scoped BigOperators Chebyshev
open ArithmeticFunction (vonMangoldt)

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

noncomputable section

/-! ## Section 1: Summation by Parts of `mertensDeviationSqrtAction M` -/

/-- Shifted square-root prefix `∑_{j < k} 2 √(j + 2)`. -/
def shiftedTwoSqrtPrefix (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, 2 * Real.sqrt (j + 2 : ℕ)

@[simp]
theorem shiftedTwoSqrtPrefix_zero : shiftedTwoSqrtPrefix 0 = 0 := by
  simp [shiftedTwoSqrtPrefix]

theorem shiftedTwoSqrtPrefix_succ_sub (k : ℕ) :
    shiftedTwoSqrtPrefix (k + 1) - shiftedTwoSqrtPrefix k = 2 * Real.sqrt (k + 2 : ℕ) := by
  unfold shiftedTwoSqrtPrefix
  rw [Finset.sum_range_succ]
  ring

/-- Uniform `4 √(k + 2)` approximation of `shiftedTwoSqrtPrefix k` by `(4 / 3) (k + 2) √(k + 2)`. -/
theorem abs_shiftedTwoSqrtPrefix_sub_four_thirds_le (k : ℕ) :
    |shiftedTwoSqrtPrefix k - (4 / 3 : ℝ) * (k + 2 : ℕ) * Real.sqrt (k + 2 : ℕ)| ≤
      4 * Real.sqrt (k + 2 : ℕ) := by
  unfold shiftedTwoSqrtPrefix
  have h := abs_sum_range_two_mul_sqrt_add_two_sub_four_thirds_le (M := k + 2) (by omega)
  simpa using h

/-- Unit step of the Mertens deviation `mertensSum d - log d + γ`. -/
theorem mertensDeviation_succ_sub {d : ℕ} (hd : 1 ≤ d) :
    (mertensSum (d + 1) - Real.log (d + 1 : ℕ) + Real.eulerMascheroniConstant) -
      (mertensSum d - Real.log (d : ℝ) + Real.eulerMascheroniConstant) =
      vonMangoldt (d + 1) / (d + 1 : ℕ) - Real.log (((d + 1 : ℕ) : ℝ) / (d : ℝ)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hM : mertensSum (d + 1) - mertensSum d = vonMangoldt (d + 1) / (d + 1 : ℕ) := by
    have h := mertensSum_sub_eq (Nat.le_succ d)
    rw [Nat.Ioc_succ_singleton, Finset.sum_singleton] at h
    exact h
  have hlog : Real.log (((d + 1 : ℕ) : ℝ) / (d : ℝ)) =
      Real.log (d + 1 : ℕ) - Real.log (d : ℝ) :=
    Real.log_div (by positivity) hd0.ne'
  linarith

/-- Pointwise bound on the unit step of the Mertens deviation for `d ≥ 1`. -/
theorem abs_mertensDeviation_succ_sub_le {d : ℕ} (hd : 1 ≤ d) :
    |(mertensSum (d + 1) - Real.log (d + 1 : ℕ) + Real.eulerMascheroniConstant) -
        (mertensSum d - Real.log (d : ℝ) + Real.eulerMascheroniConstant)| ≤
      vonMangoldt (d + 1) / (d + 1 : ℕ) + 1 / (d : ℝ) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  rw [mertensDeviation_succ_sub hd]
  have hlog0 : 0 ≤ Real.log (((d + 1 : ℕ) : ℝ) / (d : ℝ)) := by
    apply Real.log_nonneg
    rw [ one_le_div hd0]
    exact_mod_cast Nat.le_succ d
  have hlog_le : Real.log (((d + 1 : ℕ) : ℝ) / (d : ℝ)) ≤ 1 / (d : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((d + 1 : ℕ) : ℝ) / d by positivity)
    have e : ((d + 1 : ℕ) : ℝ) / d - 1 = 1 / (d : ℝ) := by
      push_cast; field_simp; ring
    linarith
  have hΛ0 : 0 ≤ vonMangoldt (d + 1) / (d + 1 : ℕ) :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
  calc
    |vonMangoldt (d + 1) / (d + 1 : ℕ) - Real.log (((d + 1 : ℕ) : ℝ) / (d : ℝ))| ≤
      |vonMangoldt (d + 1) / (d + 1 : ℕ)| + |Real.log (((d + 1 : ℕ) : ℝ) / (d : ℝ))| :=
      abs_sub _ _
    _ = vonMangoldt (d + 1) / (d + 1 : ℕ) + Real.log (((d + 1 : ℕ) : ℝ) / (d : ℝ)) := by
      rw [abs_of_nonneg hΛ0, abs_of_nonneg hlog0]
    _ ≤ vonMangoldt (d + 1) / (d + 1 : ℕ) + 1 / (d : ℝ) := add_le_add le_rfl hlog_le

/-- Exact summation-by-parts identity for `mertensDeviationSqrtAction M`. -/
theorem mertensDeviationSqrtAction_eq_terminal_sub_sum_diff (M : ℕ) :
    mertensDeviationSqrtAction M =
      shiftedTwoSqrtPrefix (M - 2) *
          (mertensSum (M - 2 + 2) - Real.log (M - 2 + 2 : ℕ) + Real.eulerMascheroniConstant) -
        ∑ k ∈ Finset.range (M - 2),
          shiftedTwoSqrtPrefix (k + 1) *
            ((mertensSum (k + 3) - Real.log (k + 3 : ℕ) + Real.eulerMascheroniConstant) -
              (mertensSum (k + 2) - Real.log (k + 2 : ℕ) + Real.eulerMascheroniConstant)) := by
  have hrewrite :
      mertensDeviationSqrtAction M =
        ∑ k ∈ Finset.range (M - 2),
          (shiftedTwoSqrtPrefix (k + 1) - shiftedTwoSqrtPrefix k) *
            (mertensSum (k + 2) - Real.log (k + 2 : ℕ) + Real.eulerMascheroniConstant) := by
    unfold mertensDeviationSqrtAction
    apply Finset.sum_congr rfl
    intro k _
    rw [shiftedTwoSqrtPrefix_succ_sub]
  rw [hrewrite,
    sum_range_diff_mul_eq_boundary_sub_sum_mul_diff
      shiftedTwoSqrtPrefix
      (fun k => mertensSum (k + 2) - Real.log (k + 2 : ℕ) + Real.eulerMascheroniConstant)
      shiftedTwoSqrtPrefix_zero (M - 2)]

/-- Sum of `vonMangoldt (k + 3)` over `k ∈ Finset.range (M - 2)` is at most `6 * M`. -/
theorem sum_range_vonMangoldt_add_three_le (M : ℕ) :
    (∑ k ∈ Finset.range (M - 2), vonMangoldt (k + 3)) ≤ 6 * (M : ℝ) := by
  rcases lt_or_ge M 2 with hM2 | hM2
  · have h0 : M - 2 = 0 := by omega
    rw [h0]; simp
  · have htel :
        (∑ k ∈ Finset.range (M - 2), vonMangoldt (k + 3)) =
          Chebyshev.psi (M : ℝ) - Chebyshev.psi (2 : ℝ) := by
      have h := Finset.sum_range_sub (fun k => Chebyshev.psi (k + 2 : ℕ)) (M - 2)
      have hcongr :
          (∑ k ∈ Finset.range (M - 2),
              (Chebyshev.psi (k + 1 + 2 : ℕ) - Chebyshev.psi (k + 2 : ℕ))) =
            ∑ k ∈ Finset.range (M - 2), vonMangoldt (k + 3) := by
        apply Finset.sum_congr rfl
        intro k _
        have hstep := psi_sub_psi_eq (Nat.le_succ (k + 2))
        rw [Nat.Ioc_succ_singleton, Finset.sum_singleton] at hstep
        simpa [Nat.add_assoc] using hstep
      rw [hcongr, show (M - 2 + 2 : ℕ) = M by omega, show (0 + 2 : ℕ) = 2 by rfl] at h
      push_cast at h
      exact h
    rw [htel]
    have hψM := psi_nat_le_six_mul M
    have hψ2 := psi_nat_nonneg 2
    push_cast at hψ2
    linarith

/-- **Asymptotic Evaluation of `mertensDeviationSqrtAction M` via Summation by Parts:**
For all `M ≥ 2`, `mertensDeviationSqrtAction M` equals
`(4 / 3) * (M * √M * (mertensSum M - log M + γ) - ∑_{k < M - 2} √(k + 3) * (Λ(k + 3) - 1))`
within `63 * M`. -/
theorem abs_mertensDeviationSqrtAction_sub_four_thirds_terminal_sub_sum_le
    {M : ℕ} (hM : 2 ≤ M) :
    |mertensDeviationSqrtAction M -
        ((4 / 3 : ℝ) * (M : ℝ) * Real.sqrt (M : ℝ) *
            (mertensSum M - Real.log (M : ℝ) + Real.eulerMascheroniConstant) -
          (4 / 3 : ℝ) * ∑ k ∈ Finset.range (M - 2),
            Real.sqrt (k + 3 : ℕ) * (vonMangoldt (k + 3) - 1))| ≤
      63 * (M : ℝ) := by
  have hM2 : M - 2 + 2 = M := by omega
  have hsqrtM : Real.sqrt (M : ℝ) ≤ (M : ℝ) := by
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
    have hsq : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    have hs1 : (1 : ℝ) ≤ Real.sqrt (M : ℝ) := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hM1
    nlinarith
  -- 1. Boundary approximation error `≤ 28 * M`
  have hbd_err :
      |shiftedTwoSqrtPrefix (M - 2) *
          (mertensSum M - Real.log (M : ℝ) + Real.eulerMascheroniConstant) -
        (4 / 3 : ℝ) * (M : ℝ) * Real.sqrt (M : ℝ) *
          (mertensSum M - Real.log (M : ℝ) + Real.eulerMascheroniConstant)| ≤
        28 * (M : ℝ) := by
    have hdiff :
        shiftedTwoSqrtPrefix (M - 2) *
            (mertensSum M - Real.log (M : ℝ) + Real.eulerMascheroniConstant) -
          (4 / 3 : ℝ) * (M : ℝ) * Real.sqrt (M : ℝ) *
            (mertensSum M - Real.log (M : ℝ) + Real.eulerMascheroniConstant) =
        (shiftedTwoSqrtPrefix (M - 2) - (4 / 3 : ℝ) * (M : ℝ) * Real.sqrt (M : ℝ)) *
          (mertensSum M - Real.log (M : ℝ) + Real.eulerMascheroniConstant) := by ring
    rw [hdiff, abs_mul]
    have hW := abs_shiftedTwoSqrtPrefix_sub_four_thirds_le (M - 2)
    rw [hM2] at hW
    have hM7 := abs_mertensDeviation_le_seven (d := M) (by omega)
    calc
      |shiftedTwoSqrtPrefix (M - 2) - (4 / 3 : ℝ) * (M : ℝ) * Real.sqrt (M : ℝ)| *
          |mertensSum M - Real.log (M : ℝ) + Real.eulerMascheroniConstant| ≤
        (4 * Real.sqrt (M : ℝ)) * 7 :=
        mul_le_mul hW hM7 (abs_nonneg _) (by positivity)
      _ = 28 * Real.sqrt (M : ℝ) := by ring
      _ ≤ 28 * (M : ℝ) := mul_le_mul_of_nonneg_left hsqrtM (by norm_num)
  -- 2. Interior weight replacement error `≤ 32 * M`
  have hint_err1 :
      |(∑ k ∈ Finset.range (M - 2),
          shiftedTwoSqrtPrefix (k + 1) *
            ((mertensSum (k + 3) - Real.log (k + 3 : ℕ) + Real.eulerMascheroniConstant) -
              (mertensSum (k + 2) - Real.log (k + 2 : ℕ) + Real.eulerMascheroniConstant))) -
        ∑ k ∈ Finset.range (M - 2),
          (4 / 3 : ℝ) * (k + 3 : ℕ) * Real.sqrt (k + 3 : ℕ) *
            ((mertensSum (k + 3) - Real.log (k + 3 : ℕ) + Real.eulerMascheroniConstant) -
              (mertensSum (k + 2) - Real.log (k + 2 : ℕ) + Real.eulerMascheroniConstant))| ≤
        32 * (M : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    have hterm : ∀ k ∈ Finset.range (M - 2),
        |shiftedTwoSqrtPrefix (k + 1) *
            ((mertensSum (k + 3) - Real.log (k + 3 : ℕ) + Real.eulerMascheroniConstant) -
              (mertensSum (k + 2) - Real.log (k + 2 : ℕ) + Real.eulerMascheroniConstant)) -
          (4 / 3 : ℝ) * (k + 3 : ℕ) * Real.sqrt (k + 3 : ℕ) *
            ((mertensSum (k + 3) - Real.log (k + 3 : ℕ) + Real.eulerMascheroniConstant) -
              (mertensSum (k + 2) - Real.log (k + 2 : ℕ) + Real.eulerMascheroniConstant))| ≤
          4 * vonMangoldt (k + 3) + 8 := by
      intro k _
      have hfactor :
          shiftedTwoSqrtPrefix (k + 1) *
              ((mertensSum (k + 3) - Real.log (k + 3 : ℕ) + Real.eulerMascheroniConstant) -
                (mertensSum (k + 2) - Real.log (k + 2 : ℕ) + Real.eulerMascheroniConstant)) -
            (4 / 3 : ℝ) * (k + 3 : ℕ) * Real.sqrt (k + 3 : ℕ) *
              ((mertensSum (k + 3) - Real.log (k + 3 : ℕ) + Real.eulerMascheroniConstant) -
                (mertensSum (k + 2) - Real.log (k + 2 : ℕ) + Real.eulerMascheroniConstant)) =
          (shiftedTwoSqrtPrefix (k + 1) - (4 / 3 : ℝ) * (k + 3 : ℕ) * Real.sqrt (k + 3 : ℕ)) *
            ((mertensSum (k + 3) - Real.log (k + 3 : ℕ) + Real.eulerMascheroniConstant) -
              (mertensSum (k + 2) - Real.log (k + 2 : ℕ) + Real.eulerMascheroniConstant)) := by ring
      rw [hfactor, abs_mul]
      have hW := abs_shiftedTwoSqrtPrefix_sub_four_thirds_le (k + 1)
      rw [show k + 1 + 2 = k + 3 by omega] at hW
      have hstep := abs_mertensDeviation_succ_sub_le (d := k + 2) (by omega)
      rw [show k + 2 + 1 = k + 3 by omega] at hstep
      have hsk_le : Real.sqrt (k + 3 : ℕ) ≤ (k + 3 : ℕ) := by
        have hk1 : (1 : ℝ) ≤ (k + 3 : ℕ) := by exact_mod_cast (show 1 ≤ k + 3 by omega)
        have hsq : Real.sqrt (k + 3 : ℕ) * Real.sqrt (k + 3 : ℕ) = (k + 3 : ℕ) :=
          Real.mul_self_sqrt (by positivity)
        have hs1 : (1 : ℝ) ≤ Real.sqrt (k + 3 : ℕ) := by
          rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hk1
        nlinarith
      have hsk_div1 : Real.sqrt (k + 3 : ℕ) * (vonMangoldt (k + 3) / (k + 3 : ℕ)) ≤
          vonMangoldt (k + 3) := by
        have hk3_pos : (0 : ℝ) < (k + 3 : ℕ) := by positivity
        have hdiv : Real.sqrt (k + 3 : ℕ) / (k + 3 : ℕ) ≤ 1 :=
          (div_le_one hk3_pos).mpr hsk_le
        calc
          Real.sqrt (k + 3 : ℕ) * (vonMangoldt (k + 3) / (k + 3 : ℕ)) =
            (Real.sqrt (k + 3 : ℕ) / (k + 3 : ℕ)) * vonMangoldt (k + 3) := by ring
          _ ≤ 1 * vonMangoldt (k + 3) :=
            mul_le_mul_of_nonneg_right hdiv ArithmeticFunction.vonMangoldt_nonneg
          _ = vonMangoldt (k + 3) := one_mul _
      have hsk_div2 : Real.sqrt (k + 3 : ℕ) * (1 / (k + 2 : ℕ)) ≤ 2 := by
        have hk2_pos : (0 : ℝ) < (k + 2 : ℕ) := by positivity
        rw [mul_one_div, div_le_iff₀ hk2_pos]
        have hle : (k + 3 : ℕ) ≤ (2 * (k + 2) : ℕ) := by omega
        have hle' : ((k + 3 : ℕ) : ℝ) ≤ 2 * (k + 2 : ℕ) := by exact_mod_cast hle
        linarith
      calc
        |shiftedTwoSqrtPrefix (k + 1) - (4 / 3 : ℝ) * (k + 3 : ℕ) * Real.sqrt (k + 3 : ℕ)| *
            |(mertensSum (k + 3) - Real.log (k + 3 : ℕ) + Real.eulerMascheroniConstant) -
              (mertensSum (k + 2) - Real.log (k + 2 : ℕ) + Real.eulerMascheroniConstant)| ≤
          (4 * Real.sqrt (k + 3 : ℕ)) *
            (vonMangoldt (k + 3) / (k + 3 : ℕ) + 1 / (k + 2 : ℕ)) :=
          mul_le_mul hW hstep (abs_nonneg _) (by positivity)
        _ = 4 * (Real.sqrt (k + 3 : ℕ) * (vonMangoldt (k + 3) / (k + 3 : ℕ))) +
            4 * (Real.sqrt (k + 3 : ℕ) * (1 / (k + 2 : ℕ))) := by ring
        _ ≤ 4 * vonMangoldt (k + 3) + 8 := by linarith
    have hsumΛ := sum_range_vonMangoldt_add_three_le M
    have hleM : ((M - 2 : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.sub_le M 2
    calc
      |∑ k ∈ Finset.range (M - 2),
          (shiftedTwoSqrtPrefix (k + 1) *
              ((mertensSum (k + 3) - Real.log (k + 3 : ℕ) + Real.eulerMascheroniConstant) -
                (mertensSum (k + 2) - Real.log (k + 2 : ℕ) + Real.eulerMascheroniConstant)) -
            (4 / 3 : ℝ) * (k + 3 : ℕ) * Real.sqrt (k + 3 : ℕ) *
              ((mertensSum (k + 3) - Real.log (k + 3 : ℕ) + Real.eulerMascheroniConstant) -
                (mertensSum (k + 2) - Real.log (k + 2 : ℕ) + Real.eulerMascheroniConstant)))| ≤
        ∑ k ∈ Finset.range (M - 2), (4 * vonMangoldt (k + 3) + 8) :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
      _ = 4 * (∑ k ∈ Finset.range (M - 2), vonMangoldt (k + 3)) + 8 * ((M - 2 : ℕ) : ℝ) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp [mul_comm]
      _ ≤ 4 * (6 * (M : ℝ)) + 8 * (M : ℝ) := by linarith
      _ = 32 * (M : ℝ) := by ring
  -- 3. Cancellation of `(k + 3)` in `(k + 3) * √(k + 3) * (Λ(k + 3) / (k + 3) - log((k + 3)/(k + 2)))`
  have hint_err2 :
      |(∑ k ∈ Finset.range (M - 2),
          (4 / 3 : ℝ) * (k + 3 : ℕ) * Real.sqrt (k + 3 : ℕ) *
            ((mertensSum (k + 3) - Real.log (k + 3 : ℕ) + Real.eulerMascheroniConstant) -
              (mertensSum (k + 2) - Real.log (k + 2 : ℕ) + Real.eulerMascheroniConstant))) -
        (4 / 3 : ℝ) * ∑ k ∈ Finset.range (M - 2),
          Real.sqrt (k + 3 : ℕ) * (vonMangoldt (k + 3) - 1)| ≤
        3 * (M : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    have hterm : ∀ k ∈ Finset.range (M - 2),
        |(4 / 3 : ℝ) * (k + 3 : ℕ) * Real.sqrt (k + 3 : ℕ) *
            ((mertensSum (k + 3) - Real.log (k + 3 : ℕ) + Real.eulerMascheroniConstant) -
              (mertensSum (k + 2) - Real.log (k + 2 : ℕ) + Real.eulerMascheroniConstant)) -
          (4 / 3 : ℝ) * (Real.sqrt (k + 3 : ℕ) * (vonMangoldt (k + 3) - 1))| ≤ 3 := by
      intro k _
      have hk3_pos : (0 : ℝ) < (k + 3 : ℕ) := by positivity
      have hk2_pos : (0 : ℝ) < (k + 2 : ℕ) := by positivity
      have hstep := mertensDeviation_succ_sub (d := k + 2) (by omega)
      rw [show k + 2 + 1 = k + 3 by omega] at hstep
      have hident :
          (4 / 3 : ℝ) * (k + 3 : ℕ) * Real.sqrt (k + 3 : ℕ) *
              ((mertensSum (k + 3) - Real.log (k + 3 : ℕ) + Real.eulerMascheroniConstant) -
                (mertensSum (k + 2) - Real.log (k + 2 : ℕ) + Real.eulerMascheroniConstant)) -
            (4 / 3 : ℝ) * (Real.sqrt (k + 3 : ℕ) * (vonMangoldt (k + 3) - 1)) =
          -(4 / 3 : ℝ) * Real.sqrt (k + 3 : ℕ) *
            (((k + 3 : ℕ) : ℝ) * Real.log (((k + 3 : ℕ) : ℝ) / (k + 2 : ℕ)) - 1) := by
        rw [hstep]
        field_simp [hk3_pos.ne']
        ring
      rw [hident, abs_mul, abs_mul, show |(-(4 / 3 : ℝ))| = 4 / 3 by norm_num,
        abs_of_pos (Real.sqrt_pos.mpr hk3_pos)]
      have hcurv := mul_log_succ_div_sub_one_bounds (d := k + 2) (by omega)
      rw [show k + 2 + 1 = k + 3 by omega] at hcurv
      rw [abs_of_nonneg hcurv.1]
      have hsk_le : Real.sqrt (k + 3 : ℕ) ≤ (k + 3 : ℕ) := by
        have hk1 : (1 : ℝ) ≤ (k + 3 : ℕ) := by exact_mod_cast (show 1 ≤ k + 3 by omega)
        have hsq : Real.sqrt (k + 3 : ℕ) * Real.sqrt (k + 3 : ℕ) = (k + 3 : ℕ) :=
          Real.mul_self_sqrt (by positivity)
        have hs1 : (1 : ℝ) ≤ Real.sqrt (k + 3 : ℕ) := by
          rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hk1
        nlinarith
      have hsk_div2 : Real.sqrt (k + 3 : ℕ) * (1 / (k + 2 : ℕ)) ≤ 2 := by
        rw [mul_one_div, div_le_iff₀ hk2_pos]
        have hle : (k + 3 : ℕ) ≤ (2 * (k + 2) : ℕ) := by omega
        have hle' : ((k + 3 : ℕ) : ℝ) ≤ 2 * (k + 2 : ℕ) := by exact_mod_cast hle
        linarith
      calc
        (4 / 3 : ℝ) * Real.sqrt (k + 3 : ℕ) *
            (((k + 3 : ℕ) : ℝ) * Real.log (((k + 3 : ℕ) : ℝ) / (k + 2 : ℕ)) - 1) ≤
          (4 / 3 : ℝ) * Real.sqrt (k + 3 : ℕ) * (1 / (k + 2 : ℕ)) :=
          mul_le_mul_of_nonneg_left hcurv.2 (by positivity)
        _ = (4 / 3 : ℝ) * (Real.sqrt (k + 3 : ℕ) * (1 / (k + 2 : ℕ))) := by ring
        _ ≤ (4 / 3 : ℝ) * 2 := mul_le_mul_of_nonneg_left hsk_div2 (by norm_num)
        _ ≤ 3 := by norm_num
    have hleM : ((M - 2 : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.sub_le M 2
    calc
      |∑ k ∈ Finset.range (M - 2),
          ((4 / 3 : ℝ) * (k + 3 : ℕ) * Real.sqrt (k + 3 : ℕ) *
              ((mertensSum (k + 3) - Real.log (k + 3 : ℕ) + Real.eulerMascheroniConstant) -
                (mertensSum (k + 2) - Real.log (k + 2 : ℕ) + Real.eulerMascheroniConstant)) -
            (4 / 3 : ℝ) * (Real.sqrt (k + 3 : ℕ) * (vonMangoldt (k + 3) - 1)))| ≤
        ∑ k ∈ Finset.range (M - 2), (3 : ℝ) :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
      _ = 3 * ((M - 2 : ℕ) : ℝ) := by simp [mul_comm]
      _ ≤ 3 * (M : ℝ) := mul_le_mul_of_nonneg_left hleM (by norm_num)
  -- Combine all 3 pieces
  rw [mertensDeviationSqrtAction_eq_terminal_sub_sum_diff M, hM2]
  set A₁ := shiftedTwoSqrtPrefix (M - 2) *
    (mertensSum M - Real.log (M : ℝ) + Real.eulerMascheroniConstant)
  set A₂ := (4 / 3 : ℝ) * (M : ℝ) * Real.sqrt (M : ℝ) *
    (mertensSum M - Real.log (M : ℝ) + Real.eulerMascheroniConstant)
  set S₁ := ∑ k ∈ Finset.range (M - 2),
    shiftedTwoSqrtPrefix (k + 1) *
      ((mertensSum (k + 3) - Real.log (k + 3 : ℕ) + Real.eulerMascheroniConstant) -
        (mertensSum (k + 2) - Real.log (k + 2 : ℕ) + Real.eulerMascheroniConstant))
  set S₂ := ∑ k ∈ Finset.range (M - 2),
    (4 / 3 : ℝ) * (k + 3 : ℕ) * Real.sqrt (k + 3 : ℕ) *
      ((mertensSum (k + 3) - Real.log (k + 3 : ℕ) + Real.eulerMascheroniConstant) -
        (mertensSum (k + 2) - Real.log (k + 2 : ℕ) + Real.eulerMascheroniConstant))
  set S₃ := (4 / 3 : ℝ) * ∑ k ∈ Finset.range (M - 2),
    Real.sqrt (k + 3 : ℕ) * (vonMangoldt (k + 3) - 1)
  calc
    |A₁ - S₁ - (A₂ - S₃)| = |(A₁ - A₂) - (S₁ - S₂) - (S₂ - S₃)| := by ring_nf
    _ ≤ |(A₁ - A₂) - (S₁ - S₂)| + |S₂ - S₃| := abs_sub _ _
    _ ≤ |A₁ - A₂| + |S₁ - S₂| + |S₂ - S₃| := add_le_add (abs_sub _ _) le_rfl
    _ ≤ 28 * (M : ℝ) + 32 * (M : ℝ) + 3 * (M : ℝ) :=
      add_le_add (add_le_add hbd_err hint_err1) hint_err2
    _ = 63 * (M : ℝ) := by ring

/-! ## Section 2: Exact Cancellation of `M * √M * (mertensSum M - log M + γ)` and the
Square-Root Riesz Action of `Λ(d) - 1` -/

/-- **Chebyshev Square-Root Difference Action:**
`chebyshevSqrtDiffAction M = √M * (ψ(M) - M) - ∑_{k < M - 2} √(k + 3) * (Λ(k + 3) - 1)`. -/
def chebyshevSqrtDiffAction (M : ℕ) : ℝ :=
  Real.sqrt (M : ℝ) * (Chebyshev.psi (M : ℝ) - (M : ℝ)) -
    ∑ k ∈ Finset.range (M - 2), Real.sqrt (k + 3 : ℕ) * (vonMangoldt (k + 3) - 1)

/-- **Square-Root Riesz Action of `Λ(d) - 1`:**
`vonMangoldtSqrtRieszAction M = ∑_{k < M - 2} (√M - √(k + 3)) * (Λ(k + 3) - 1)`. -/
def vonMangoldtSqrtRieszAction (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (M - 2),
    (Real.sqrt (M : ℝ) - Real.sqrt (k + 3 : ℕ)) * (vonMangoldt (k + 3) - 1)

/-- **Exact Cancellation of the Terminal Mertens Deviation in `integerLagMertensSqrtAction`:**
When `-(8 / 3) * M * integerLag M` and `2 * mertensDeviationSqrtAction M` are added, the
terminal Mertens deviation `∓(8 / 3) * M * √M * (mertensSum M - log M + γ)` cancels identically,
leaving `(8 / 3) * chebyshevSqrtDiffAction M` within `142 * M` for all `M ≥ 2`. -/
theorem abs_integerLagMertensSqrtAction_sub_eight_thirds_chebyshevSqrtDiffAction_le
    {M : ℕ} (hM : 2 ≤ M) :
    |integerLagMertensSqrtAction M - (8 / 3 : ℝ) * chebyshevSqrtDiffAction M| ≤
      142 * (M : ℝ) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hsq : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) := Real.mul_self_sqrt hM0.le
  have hsqrtM : Real.sqrt (M : ℝ) ≤ (M : ℝ) := by
    have hs1 : (1 : ℝ) ≤ Real.sqrt (M : ℝ) := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hM1
    nlinarith
  have hlag :
      (M : ℝ) * integerLag M =
        Real.sqrt (M : ℝ) * ((M : ℝ) - Chebyshev.psi (M : ℝ)) +
          (M : ℝ) * Real.sqrt (M : ℝ) *
            (mertensSum M - Real.log (M : ℝ) + Real.eulerMascheroniConstant) +
          Real.sqrt (M : ℝ) * (trivialZeroSeriesReal M - Real.log (2 * Real.pi)) := by
    calc
      (M : ℝ) * integerLag M = (Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ)) * integerLag M := by
        rw [hsq]
      _ = Real.sqrt (M : ℝ) * (Real.sqrt (M : ℝ) * integerLag M) := by ring
      _ = Real.sqrt (M : ℝ) * lagBracket M := by rw [← lagBracket_eq_sqrt_mul_integerLag hM]
      _ = _ := by unfold lagBracket; ring
  have hident :
      integerLagMertensSqrtAction M - (8 / 3 : ℝ) * chebyshevSqrtDiffAction M =
        2 * (mertensDeviationSqrtAction M -
          ((4 / 3 : ℝ) * (M : ℝ) * Real.sqrt (M : ℝ) *
              (mertensSum M - Real.log (M : ℝ) + Real.eulerMascheroniConstant) -
            (4 / 3 : ℝ) * ∑ k ∈ Finset.range (M - 2),
              Real.sqrt (k + 3 : ℕ) * (vonMangoldt (k + 3) - 1))) -
          (8 / 3 : ℝ) * Real.sqrt (M : ℝ) *
            (trivialZeroSeriesReal M - Real.log (2 * Real.pi)) := by
    unfold integerLagMertensSqrtAction chebyshevSqrtDiffAction
    rw [mul_assoc (-(8 / 3 : ℝ)), hlag]
    ring
  rw [hident]
  have h1 := abs_mertensDeviationSqrtAction_sub_four_thirds_terminal_sub_sum_le hM
  have hS0 := trivialZeroSeriesReal_nonneg hM1
  have hS1 := trivialZeroSeriesReal_le_one hM1
  have hlog2π : Real.log (2 * Real.pi) ≤ 6 := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)
    have := Real.pi_lt_d2
    linarith
  have hlog2π0 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have htriv : |trivialZeroSeriesReal M - Real.log (2 * Real.pi)| ≤ 6 := by
    rw [abs_le]; constructor <;> linarith
  have h2 :
      |(8 / 3 : ℝ) * Real.sqrt (M : ℝ) *
          (trivialZeroSeriesReal M - Real.log (2 * Real.pi))| ≤
        16 * (M : ℝ) := by
    rw [abs_mul, abs_mul, show |(8 / 3 : ℝ)| = 8 / 3 by norm_num,
      abs_of_pos (Real.sqrt_pos.mpr hM0)]
    calc
      (8 / 3 : ℝ) * Real.sqrt (M : ℝ) * |trivialZeroSeriesReal M - Real.log (2 * Real.pi)| ≤
        (8 / 3 : ℝ) * (M : ℝ) * 6 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hsqrtM (by norm_num)) htriv (abs_nonneg _)
          (by positivity)
      _ = 16 * (M : ℝ) := by ring
  set E₁ := mertensDeviationSqrtAction M -
    ((4 / 3 : ℝ) * (M : ℝ) * Real.sqrt (M : ℝ) *
        (mertensSum M - Real.log (M : ℝ) + Real.eulerMascheroniConstant) -
      (4 / 3 : ℝ) * ∑ k ∈ Finset.range (M - 2),
        Real.sqrt (k + 3 : ℕ) * (vonMangoldt (k + 3) - 1))
  calc
    |2 * E₁ - (8 / 3 : ℝ) * Real.sqrt (M : ℝ) *
        (trivialZeroSeriesReal M - Real.log (2 * Real.pi))| ≤
      |2 * E₁| + |(8 / 3 : ℝ) * Real.sqrt (M : ℝ) *
        (trivialZeroSeriesReal M - Real.log (2 * Real.pi))| := abs_sub _ _
    _ = 2 * |E₁| + |(8 / 3 : ℝ) * Real.sqrt (M : ℝ) *
        (trivialZeroSeriesReal M - Real.log (2 * Real.pi))| := by
      rw [abs_mul, show |(2 : ℝ)| = 2 by norm_num]
    _ ≤ 2 * (63 * (M : ℝ)) + 16 * (M : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2
    _ = 142 * (M : ℝ) := by ring

/-- Exact telescoping of `ψ(M) - M` over `Finset.range (M - 2)` for `M ≥ 2`. -/
theorem chebyshevPsi_sub_eq_sum_range_vonMangoldt_sub_one {M : ℕ} (hM : 2 ≤ M) :
    Chebyshev.psi (M : ℝ) - (M : ℝ) =
      (Chebyshev.psi (2 : ℝ) - 2) +
        ∑ k ∈ Finset.range (M - 2), (vonMangoldt (k + 3) - 1) := by
  have h := Finset.sum_range_sub (fun k => Chebyshev.psi (k + 2 : ℕ) - (k + 2 : ℕ)) (M - 2)
  have hcongr :
      (∑ k ∈ Finset.range (M - 2),
          ((Chebyshev.psi (k + 1 + 2 : ℕ) - (k + 1 + 2 : ℕ)) -
            (Chebyshev.psi (k + 2 : ℕ) - (k + 2 : ℕ)))) =
        ∑ k ∈ Finset.range (M - 2), (vonMangoldt (k + 3) - 1) := by
    apply Finset.sum_congr rfl
    intro k _
    have hstep := psi_sub_psi_eq (Nat.le_succ (k + 2))
    rw [Nat.Ioc_succ_singleton, Finset.sum_singleton] at hstep
    rw [show k + 1 + 2 = k + 2 + 1 by omega, show k + 3 = k + 2 + 1 by omega]
    push_cast at hstep ⊢
    linarith
  rw [hcongr, show (M - 2 + 2 : ℕ) = M by omega, show (0 + 2 : ℕ) = 2 by rfl] at h
  push_cast at h
  linarith

/-- Exact identity `chebyshevSqrtDiffAction M = vonMangoldtSqrtRieszAction M + √M * (ψ(2) - 2)`
for `M ≥ 2`. -/
theorem chebyshevSqrtDiffAction_eq_vonMangoldtSqrtRieszAction_add {M : ℕ} (hM : 2 ≤ M) :
    chebyshevSqrtDiffAction M =
      vonMangoldtSqrtRieszAction M + Real.sqrt (M : ℝ) * (Chebyshev.psi (2 : ℝ) - 2) := by
  unfold chebyshevSqrtDiffAction vonMangoldtSqrtRieszAction
  rw [chebyshevPsi_sub_eq_sum_range_vonMangoldt_sub_one hM, mul_add, Finset.mul_sum,
    add_sub_assoc, ← Finset.sum_sub_distrib]
  have hsum :
      (∑ x ∈ Finset.range (M - 2),
          (Real.sqrt (M : ℝ) * (vonMangoldt (x + 3) - 1) -
            Real.sqrt (x + 3 : ℕ) * (vonMangoldt (x + 3) - 1))) =
        ∑ k ∈ Finset.range (M - 2),
          (Real.sqrt (M : ℝ) - Real.sqrt (k + 3 : ℕ)) * (vonMangoldt (k + 3) - 1) := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  linarith

/-- Bound `|ψ(2) - 2| ≤ 12`. -/
theorem abs_chebyshevPsi_two_sub_two_le : |Chebyshev.psi (2 : ℝ) - 2| ≤ 12 := by
  have h1 := psi_nat_le_six_mul 2
  have h2 := psi_nat_nonneg 2
  push_cast at h1 h2
  rw [abs_le]
  constructor <;> linarith

/-- **Direct `O(M)` Bridge Between `mobiusDivisorSquareRootAbelMoment M` and
`vonMangoldtSqrtRieszAction M`:**
There exists `B ≥ 0` such that for all `M ≥ 3`,
`|mobiusDivisorSquareRootAbelMoment M - vonMangoldtSqrtRieszAction M| ≤ B * M`. -/
theorem exists_abs_mobiusDivisorSquareRootAbel_sub_vonMangoldtSqrtRieszAction_linear :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, 3 ≤ M →
      |mobiusDivisorSquareRootAbelMoment M - vonMangoldtSqrtRieszAction M| ≤ B * (M : ℝ) := by
  obtain ⟨B₀, hB₀, h0⟩ :=
    exists_abs_mobiusDivisorSquareRootAbel_sub_neg_mul_integerLag_add_mertensSqrtAction_linear
  refine ⟨B₀ + 66, by positivity, fun M hM => ?_⟩
  have hM2 : 2 ≤ M := by omega
  have hsqrtM : Real.sqrt (M : ℝ) ≤ (M : ℝ) := by
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
    have hsq : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    have hs1 : (1 : ℝ) ≤ Real.sqrt (M : ℝ) := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hM1
    nlinarith
  have h1 := h0 M hM
  have hscale :
      -(M : ℝ) * integerLag M + (3 / 4 : ℝ) * mertensDeviationSqrtAction M =
        (3 / 8 : ℝ) * integerLagMertensSqrtAction M := by
    unfold integerLagMertensSqrtAction; ring
  rw [hscale] at h1
  have h2 := abs_integerLagMertensSqrtAction_sub_eight_thirds_chebyshevSqrtDiffAction_le hM2
  have h3 :
      |chebyshevSqrtDiffAction M - vonMangoldtSqrtRieszAction M| ≤ 12 * (M : ℝ) := by
    rw [chebyshevSqrtDiffAction_eq_vonMangoldtSqrtRieszAction_add hM2, add_sub_cancel_left,
      abs_mul, abs_of_pos (Real.sqrt_pos.mpr (by positivity))]
    calc
      Real.sqrt (M : ℝ) * |Chebyshev.psi (2 : ℝ) - 2| ≤ (M : ℝ) * 12 :=
        mul_le_mul hsqrtM abs_chebyshevPsi_two_sub_two_le (abs_nonneg _) (by positivity)
      _ = 12 * (M : ℝ) := by ring
  calc
    |mobiusDivisorSquareRootAbelMoment M - vonMangoldtSqrtRieszAction M| =
      |(mobiusDivisorSquareRootAbelMoment M - (3 / 8 : ℝ) * integerLagMertensSqrtAction M) +
        (3 / 8 : ℝ) * (integerLagMertensSqrtAction M - (8 / 3 : ℝ) * chebyshevSqrtDiffAction M) +
        (chebyshevSqrtDiffAction M - vonMangoldtSqrtRieszAction M)| := by ring_nf
    _ ≤ |mobiusDivisorSquareRootAbelMoment M - (3 / 8 : ℝ) * integerLagMertensSqrtAction M| +
        |(3 / 8 : ℝ) * (integerLagMertensSqrtAction M - (8 / 3 : ℝ) * chebyshevSqrtDiffAction M)| +
        |chebyshevSqrtDiffAction M - vonMangoldtSqrtRieszAction M| := abs_add_three _ _ _
    _ = |mobiusDivisorSquareRootAbelMoment M - (3 / 8 : ℝ) * integerLagMertensSqrtAction M| +
        (3 / 8 : ℝ) * |integerLagMertensSqrtAction M - (8 / 3 : ℝ) * chebyshevSqrtDiffAction M| +
        |chebyshevSqrtDiffAction M - vonMangoldtSqrtRieszAction M| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 8)]
    _ ≤ B₀ * (M : ℝ) + (3 / 8 : ℝ) * (142 * (M : ℝ)) + 12 * (M : ℝ) :=
      add_le_add (add_le_add h1 (mul_le_mul_of_nonneg_left h2 (by norm_num))) h3
    _ ≤ (B₀ + 66) * (M : ℝ) := by linarith

/-! ## Section 3: Exact Telescoping to the Boundary-Free Normalized Chebyshev Cesàro Sum -/

/-- **Chebyshev Square-Root-Increment Action:**
`chebyshevSqrtIncrementAction M = ∑_{k < M - 2} (√(k + 3) - √(k + 2)) * (ψ(k + 2) - (k + 2))`. -/
def chebyshevSqrtIncrementAction (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (M - 2),
    (Real.sqrt (k + 3 : ℕ) - Real.sqrt (k + 2 : ℕ)) *
      (Chebyshev.psi (k + 2 : ℕ) - (k + 2 : ℕ))

/-- **Boundary-Free Normalized Chebyshev Cesàro Sum:**
`chebyshevNormalizedCesaroSum M = ∑_{k < M - 2} (ψ(k + 2) - (k + 2)) / √(k + 2)`.
Every summand is completely independent of `M`, with no Mertens sum, no `γ`, and no moving
endpoint `M`. -/
def chebyshevNormalizedCesaroSum (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (M - 2),
    (Chebyshev.psi (k + 2 : ℕ) - (k + 2 : ℕ)) / Real.sqrt (k + 2 : ℕ)

/-- **Exact Telescoping Identity Between `chebyshevSqrtDiffAction` and `chebyshevSqrtIncrementAction`:**
For all `M ≥ 2`,
`chebyshevSqrtDiffAction M = chebyshevSqrtIncrementAction M + √2 * (ψ(2) - 2)`. -/
theorem chebyshevSqrtDiffAction_eq_chebyshevSqrtIncrementAction_add {M : ℕ} (hM : 2 ≤ M) :
    chebyshevSqrtDiffAction M =
      chebyshevSqrtIncrementAction M + Real.sqrt 2 * (Chebyshev.psi (2 : ℝ) - 2) := by
  have h := Finset.sum_range_sub
    (fun k => Real.sqrt (k + 2 : ℕ) * (Chebyshev.psi (k + 2 : ℕ) - (k + 2 : ℕ))) (M - 2)
  have hpointwise :
      (∑ k ∈ Finset.range (M - 2),
          (Real.sqrt (k + 1 + 2 : ℕ) * (Chebyshev.psi (k + 1 + 2 : ℕ) - (k + 1 + 2 : ℕ)) -
            Real.sqrt (k + 2 : ℕ) * (Chebyshev.psi (k + 2 : ℕ) - (k + 2 : ℕ)))) =
        (∑ k ∈ Finset.range (M - 2),
            Real.sqrt (k + 3 : ℕ) * (vonMangoldt (k + 3) - 1)) +
          chebyshevSqrtIncrementAction M := by
    unfold chebyshevSqrtIncrementAction
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    have hstep := psi_sub_psi_eq (Nat.le_succ (k + 2))
    rw [Nat.Ioc_succ_singleton, Finset.sum_singleton] at hstep
    rw [show k + 1 + 2 = k + 2 + 1 by omega, show k + 3 = k + 2 + 1 by omega]
    have hψ : Chebyshev.psi (k + 2 + 1 : ℕ) = Chebyshev.psi (k + 2 : ℕ) + vonMangoldt (k + 2 + 1) := by
      linarith
    rw [hψ]
    push_cast
    ring
  rw [hpointwise, show (M - 2 + 2 : ℕ) = M by omega, show (0 + 2 : ℕ) = 2 by rfl] at h
  unfold chebyshevSqrtDiffAction
  push_cast at h ⊢
  linarith

/-- Pointwise square-root increment approximation: for all `d ≥ 1`,
`0 ≤ 1 / (2 * √d) - (√(d + 1) - √d) ≤ 1 / (2 * d)`. -/
theorem inv_two_mul_sqrt_sub_sqrt_succ_sub_sqrt_bounds {d : ℕ} (hd : 1 ≤ d) :
    0 ≤ 1 / (2 * Real.sqrt (d : ℝ)) - (Real.sqrt (d + 1 : ℕ) - Real.sqrt (d : ℝ)) ∧
      1 / (2 * Real.sqrt (d : ℝ)) - (Real.sqrt (d + 1 : ℕ) - Real.sqrt (d : ℝ)) ≤
        1 / (2 * (d : ℝ)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (0 : ℝ) < (d + 1 : ℕ) := by positivity
  have hsd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hd0
  have hsd1 : 0 < Real.sqrt (d + 1 : ℕ) := Real.sqrt_pos.mpr hd1
  have hle : Real.sqrt (d : ℝ) ≤ Real.sqrt (d + 1 : ℕ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ d)
  have hsq_d : Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) = (d : ℝ) := Real.mul_self_sqrt hd0.le
  have hsq_d1 : Real.sqrt (d + 1 : ℕ) * Real.sqrt (d + 1 : ℕ) = (d + 1 : ℕ) :=
    Real.mul_self_sqrt hd1.le
  have hprod :
      (Real.sqrt (d + 1 : ℕ) - Real.sqrt (d : ℝ)) *
        (Real.sqrt (d + 1 : ℕ) + Real.sqrt (d : ℝ)) = 1 := by
    calc
      (Real.sqrt (d + 1 : ℕ) - Real.sqrt (d : ℝ)) *
          (Real.sqrt (d + 1 : ℕ) + Real.sqrt (d : ℝ)) =
        Real.sqrt (d + 1 : ℕ) * Real.sqrt (d + 1 : ℕ) -
          Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) := by ring
      _ = (d + 1 : ℕ) - (d : ℝ) := by rw [hsq_d1, hsq_d]
      _ = 1 := by push_cast; ring
  have hdiff_eq :
      Real.sqrt (d + 1 : ℕ) - Real.sqrt (d : ℝ) =
        1 / (Real.sqrt (d + 1 : ℕ) + Real.sqrt (d : ℝ)) := by
    rw [eq_div_iff (by positivity)]
    exact hprod
  constructor
  · rw [hdiff_eq, sub_nonneg]
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  · have hidentity :
        1 / (2 * Real.sqrt (d : ℝ)) - 1 / (Real.sqrt (d + 1 : ℕ) + Real.sqrt (d : ℝ)) =
          (Real.sqrt (d + 1 : ℕ) - Real.sqrt (d : ℝ)) /
            (2 * Real.sqrt (d : ℝ) * (Real.sqrt (d + 1 : ℕ) + Real.sqrt (d : ℝ))) := by
      field_simp
      ring
    rw [hdiff_eq, hidentity]
    have hidentity2 :
        (Real.sqrt (d + 1 : ℕ) - Real.sqrt (d : ℝ)) /
            (2 * Real.sqrt (d : ℝ) * (Real.sqrt (d + 1 : ℕ) + Real.sqrt (d : ℝ))) =
          1 / (2 * Real.sqrt (d : ℝ) * (Real.sqrt (d + 1 : ℕ) + Real.sqrt (d : ℝ)) ^ 2) := by
      rw [div_eq_iff (by positivity)]
      calc
        (Real.sqrt (d + 1 : ℕ) - Real.sqrt (d : ℝ)) =
          ((Real.sqrt (d + 1 : ℕ) - Real.sqrt (d : ℝ)) *
            (Real.sqrt (d + 1 : ℕ) + Real.sqrt (d : ℝ))) /
            (Real.sqrt (d + 1 : ℕ) + Real.sqrt (d : ℝ)) := by
          rw [mul_div_cancel_right₀ _ (by positivity)]
        _ = 1 / (Real.sqrt (d + 1 : ℕ) + Real.sqrt (d : ℝ)) := by rw [hprod]
        _ = 1 / (2 * Real.sqrt (d : ℝ) * (Real.sqrt (d + 1 : ℕ) + Real.sqrt (d : ℝ)) ^ 2) *
            (2 * Real.sqrt (d : ℝ) * (Real.sqrt (d + 1 : ℕ) + Real.sqrt (d : ℝ))) := by
          field_simp
    rw [hidentity2]
    apply one_div_le_one_div_of_le (by positivity)
    have hsum_ge : 2 * Real.sqrt (d : ℝ) ≤ Real.sqrt (d + 1 : ℕ) + Real.sqrt (d : ℝ) := by linarith
    have hsq_ge : 4 * (d : ℝ) ≤ (Real.sqrt (d + 1 : ℕ) + Real.sqrt (d : ℝ)) ^ 2 := by
      calc
        4 * (d : ℝ) = (2 * Real.sqrt (d : ℝ)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hd0.le]; ring
        _ ≤ (Real.sqrt (d + 1 : ℕ) + Real.sqrt (d : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hsum_ge 2
    have hsd1_ge : (1 : ℝ) ≤ Real.sqrt (d : ℝ) := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast hd)
    nlinarith

/-- Uniform `3 * M` comparison between `chebyshevSqrtIncrementAction M` and
`(1 / 2) * chebyshevNormalizedCesaroSum M`. -/
theorem abs_chebyshevSqrtIncrementAction_sub_half_normalizedCesaroSum_le (M : ℕ) :
    |chebyshevSqrtIncrementAction M - (1 / 2 : ℝ) * chebyshevNormalizedCesaroSum M| ≤
      3 * (M : ℝ) := by
  unfold chebyshevSqrtIncrementAction chebyshevNormalizedCesaroSum
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hterm : ∀ k ∈ Finset.range (M - 2),
      |(Real.sqrt (k + 3 : ℕ) - Real.sqrt (k + 2 : ℕ)) *
          (Chebyshev.psi (k + 2 : ℕ) - (k + 2 : ℕ)) -
        (1 / 2 : ℝ) * ((Chebyshev.psi (k + 2 : ℕ) - (k + 2 : ℕ)) / Real.sqrt (k + 2 : ℕ))| ≤ 3 := by
    intro k _
    have hk0 : (0 : ℝ) < (k + 2 : ℕ) := by positivity
    have hdiff :
        (Real.sqrt (k + 3 : ℕ) - Real.sqrt (k + 2 : ℕ)) *
            (Chebyshev.psi (k + 2 : ℕ) - (k + 2 : ℕ)) -
          (1 / 2 : ℝ) * ((Chebyshev.psi (k + 2 : ℕ) - (k + 2 : ℕ)) / Real.sqrt (k + 2 : ℕ)) =
        -(1 / (2 * Real.sqrt (k + 2 : ℕ)) - (Real.sqrt (k + 3 : ℕ) - Real.sqrt (k + 2 : ℕ))) *
          (Chebyshev.psi (k + 2 : ℕ) - (k + 2 : ℕ)) := by ring
    rw [hdiff, abs_mul, abs_neg]
    have hinc := inv_two_mul_sqrt_sub_sqrt_succ_sub_sqrt_bounds (d := k + 2) (by omega)
    rw [show k + 2 + 1 = k + 3 by omega] at hinc
    rw [abs_of_nonneg hinc.1]
    have hψ_le : |Chebyshev.psi (k + 2 : ℕ) - (k + 2 : ℕ)| ≤ 6 * (k + 2 : ℕ) := by
      have h1 := psi_nat_le_six_mul (k + 2)
      have h2 := psi_nat_nonneg (k + 2)
      rw [abs_le]
      constructor <;> linarith
    calc
      (1 / (2 * Real.sqrt (k + 2 : ℕ)) - (Real.sqrt (k + 3 : ℕ) - Real.sqrt (k + 2 : ℕ))) *
          |Chebyshev.psi (k + 2 : ℕ) - (k + 2 : ℕ)| ≤
        (1 / (2 * (k + 2 : ℕ))) * (6 * (k + 2 : ℕ)) :=
        mul_le_mul hinc.2 hψ_le (abs_nonneg _) (by positivity)
      _ = 3 := by field_simp; ring
  have hleM : ((M - 2 : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.sub_le M 2
  calc
    |∑ k ∈ Finset.range (M - 2),
        ((Real.sqrt (k + 3 : ℕ) - Real.sqrt (k + 2 : ℕ)) *
            (Chebyshev.psi (k + 2 : ℕ) - (k + 2 : ℕ)) -
          (1 / 2 : ℝ) * ((Chebyshev.psi (k + 2 : ℕ) - (k + 2 : ℕ)) / Real.sqrt (k + 2 : ℕ)))| ≤
      ∑ k ∈ Finset.range (M - 2), (3 : ℝ) :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
    _ = 3 * ((M - 2 : ℕ) : ℝ) := by simp [mul_comm]
    _ ≤ 3 * (M : ℝ) := mul_le_mul_of_nonneg_left hleM (by norm_num)

/-- **Direct Unconditional `O(M)` Bridge Between `mobiusDivisorSquareRootAbelMoment M` and
`(1 / 2) * chebyshevNormalizedCesaroSum M`:**
There exists `B ≥ 0` such that for all `M ≥ 3`,
`|mobiusDivisorSquareRootAbelMoment M - (1 / 2) * chebyshevNormalizedCesaroSum M| ≤ B * M`. -/
theorem exists_abs_mobiusDivisorSquareRootAbel_sub_half_chebyshevNormalizedCesaroSum_linear :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, 3 ≤ M →
      |mobiusDivisorSquareRootAbelMoment M -
        (1 / 2 : ℝ) * chebyshevNormalizedCesaroSum M| ≤ B * (M : ℝ) := by
  obtain ⟨B₀, hB₀, h0⟩ :=
    exists_abs_mobiusDivisorSquareRootAbel_sub_vonMangoldtSqrtRieszAction_linear
  refine ⟨B₀ + 27, by positivity, fun M hM => ?_⟩
  have hM2 : 2 ≤ M := by omega
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hsqrtM : Real.sqrt (M : ℝ) ≤ (M : ℝ) := by
    have hsq : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    have hs1 : (1 : ℝ) ≤ Real.sqrt (M : ℝ) := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hM1
    nlinarith
  have hsqrt2 : Real.sqrt 2 ≤ (M : ℝ) := by
    calc
      Real.sqrt 2 ≤ Real.sqrt (M : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hM2)
      _ ≤ (M : ℝ) := hsqrtM
  have h1 := h0 M hM
  have h2 :
      |vonMangoldtSqrtRieszAction M - chebyshevSqrtIncrementAction M| ≤ 24 * (M : ℝ) := by
    have heq :
        vonMangoldtSqrtRieszAction M - chebyshevSqrtIncrementAction M =
          (Real.sqrt 2 - Real.sqrt (M : ℝ)) * (Chebyshev.psi (2 : ℝ) - 2) := by
      have hA := chebyshevSqrtDiffAction_eq_vonMangoldtSqrtRieszAction_add hM2
      have hB := chebyshevSqrtDiffAction_eq_chebyshevSqrtIncrementAction_add hM2
      linarith
    rw [heq, abs_mul]
    have hsub : |Real.sqrt 2 - Real.sqrt (M : ℝ)| ≤ 2 * (M : ℝ) := by
      have hs0 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      have hsM0 : (0 : ℝ) ≤ Real.sqrt (M : ℝ) := Real.sqrt_nonneg M
      rw [abs_le]; constructor <;> linarith
    calc
      |Real.sqrt 2 - Real.sqrt (M : ℝ)| * |Chebyshev.psi (2 : ℝ) - 2| ≤
        (2 * (M : ℝ)) * 12 :=
        mul_le_mul hsub abs_chebyshevPsi_two_sub_two_le (abs_nonneg _) (by positivity)
      _ = 24 * (M : ℝ) := by ring
  have h3 := abs_chebyshevSqrtIncrementAction_sub_half_normalizedCesaroSum_le M
  calc
    |mobiusDivisorSquareRootAbelMoment M -
        (1 / 2 : ℝ) * chebyshevNormalizedCesaroSum M| =
      |(mobiusDivisorSquareRootAbelMoment M - vonMangoldtSqrtRieszAction M) +
        (vonMangoldtSqrtRieszAction M - chebyshevSqrtIncrementAction M) +
        (chebyshevSqrtIncrementAction M - (1 / 2 : ℝ) * chebyshevNormalizedCesaroSum M)| := by
      ring_nf
    _ ≤ |mobiusDivisorSquareRootAbelMoment M - vonMangoldtSqrtRieszAction M| +
        |vonMangoldtSqrtRieszAction M - chebyshevSqrtIncrementAction M| +
        |chebyshevSqrtIncrementAction M - (1 / 2 : ℝ) * chebyshevNormalizedCesaroSum M| :=
      abs_add_three _ _ _
    _ ≤ B₀ * (M : ℝ) + 24 * (M : ℝ) + 3 * (M : ℝ) := add_le_add (add_le_add h1 h2) h3
    _ = (B₀ + 27) * (M : ℝ) := by ring

/-- **One-Sided Upper RH Equivalence for the Pure Normalized Chebyshev Cesàro Sum:**
RH holds iff `∑_{k < M - 2} (ψ(k + 2) - (k + 2)) / √(k + 2) ≤ C * M` for all `M ≥ 3`. -/
theorem riemannHypothesis_iff_chebyshevNormalizedCesaroSum_boundedAbove :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ M : ℕ, 3 ≤ M →
        chebyshevNormalizedCesaroSum M ≤ C * (M : ℝ) := by
  obtain ⟨B, _hB0, hB⟩ :=
    exists_abs_mobiusDivisorSquareRootAbel_sub_half_chebyshevNormalizedCesaroSum_linear
  rw [riemannHypothesis_iff_mobiusDivisorSquareRootAbel_boundedAbove]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨2 * (C + B), fun M hM3 => ?_⟩
    have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    have h1 := (div_le_iff₀ hMpos).mp (hC M (by omega))
    have h2 := (abs_sub_le_iff.mp (hB M hM3)).2
    linarith
  · rintro ⟨C, hC⟩
    obtain ⟨M₀, hM2, hM3⟩ :
        ∃ M₀ : ℝ, mobiusDivisorSquareRootAbelMoment 2 / (2 : ℕ) ≤ M₀ ∧
          (1 / 2 : ℝ) * C + B ≤ M₀ :=
      ⟨max (mobiusDivisorSquareRootAbelMoment 2 / (2 : ℕ)) ((1 / 2 : ℝ) * C + B),
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
      have hdiv : mobiusDivisorSquareRootAbelMoment M / (M : ℝ) ≤ (1 / 2 : ℝ) * C + B :=
        (div_le_iff₀ hMpos).mpr (by linarith)
      exact hdiv.trans hM3

/-- **One-Sided Lower RH Equivalence for the Pure Normalized Chebyshev Cesàro Sum:**
RH holds iff `-C * M ≤ ∑_{k < M - 2} (ψ(k + 2) - (k + 2)) / √(k + 2)` for all `M ≥ 3`. -/
theorem riemannHypothesis_iff_chebyshevNormalizedCesaroSum_boundedBelow :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ M : ℕ, 3 ≤ M →
        -C * (M : ℝ) ≤ chebyshevNormalizedCesaroSum M := by
  obtain ⟨B, _hB0, hB⟩ :=
    exists_abs_mobiusDivisorSquareRootAbel_sub_half_chebyshevNormalizedCesaroSum_linear
  rw [riemannHypothesis_iff_mobiusDivisorSquareRootAbel_boundedBelow]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨2 * (-C + B), fun M hM3 => ?_⟩
    have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    have h1 := (le_div_iff₀ hMpos).mp (hC M (by omega))
    have h2 := (abs_sub_le_iff.mp (hB M hM3)).1
    linarith
  · rintro ⟨C, hC⟩
    obtain ⟨M₀, hM2, hM3⟩ :
        ∃ M₀ : ℝ, -M₀ ≤ mobiusDivisorSquareRootAbelMoment 2 / (2 : ℕ) ∧
          (1 / 2 : ℝ) * C + B ≤ M₀ :=
      ⟨max (-mobiusDivisorSquareRootAbelMoment 2 / (2 : ℕ)) ((1 / 2 : ℝ) * C + B),
        by
          have h := neg_le_neg (le_max_left (-mobiusDivisorSquareRootAbelMoment 2 / (2 : ℕ))
            ((1 / 2 : ℝ) * C + B))
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
      have hdiv : -((1 / 2 : ℝ) * C + B) ≤ mobiusDivisorSquareRootAbelMoment M / (M : ℝ) :=
        (le_div_iff₀ hMpos).mpr (by linarith)
      exact (neg_le_neg hM3).trans hdiv

/-- **Polynomial-Schedule (`M = N^m`) Upper RH Equivalence for `chebyshevNormalizedCesaroSum`.** -/
theorem riemannHypothesis_iff_chebyshevNormalizedCesaroSum_pow_bddAbove
    {m : ℕ} (hm : 1 ≤ m) :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ N : ℕ, 3 ≤ N →
        chebyshevNormalizedCesaroSum (N ^ m) ≤ C * ((N ^ m : ℕ) : ℝ) := by
  obtain ⟨B, _hB0, hB⟩ :=
    exists_abs_mobiusDivisorSquareRootAbel_sub_half_chebyshevNormalizedCesaroSum_linear
  rw [riemannHypothesis_iff_mobiusDivisorSquareRootAbel_pow_bddAbove hm]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨2 * (C + B), fun N hN3 => ?_⟩
    have hNm3 : 3 ≤ N ^ m :=
      le_trans hN3 (Nat.le_self_pow (by omega : m ≠ 0) N)
    have hpos : (0 : ℝ) < (N ^ m : ℕ) := by exact_mod_cast (show 0 < N ^ m by omega)
    have h1 := (div_le_iff₀ hpos).mp (hC N (by omega))
    have h2 := (abs_sub_le_iff.mp (hB (N ^ m) hNm3)).2
    linarith
  · rintro ⟨C, hC⟩
    obtain ⟨M₀, hM2, hM3⟩ :
        ∃ M₀ : ℝ, mobiusDivisorSquareRootAbelMoment (2 ^ m) / (2 ^ m : ℕ) ≤ M₀ ∧
          (1 / 2 : ℝ) * C + B ≤ M₀ :=
      ⟨max (mobiusDivisorSquareRootAbelMoment (2 ^ m) / (2 ^ m : ℕ)) ((1 / 2 : ℝ) * C + B),
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
          (1 / 2 : ℝ) * C + B :=
        (div_le_iff₀ hpos).mpr (by linarith)
      exact hdiv.trans hM3

/-- **Polynomial-Schedule (`M = N^m`) Lower RH Equivalence for `chebyshevNormalizedCesaroSum`.** -/
theorem riemannHypothesis_iff_chebyshevNormalizedCesaroSum_pow_bddBelow
    {m : ℕ} (hm : 1 ≤ m) :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ N : ℕ, 3 ≤ N →
        -C * ((N ^ m : ℕ) : ℝ) ≤ chebyshevNormalizedCesaroSum (N ^ m) := by
  obtain ⟨B, _hB0, hB⟩ :=
    exists_abs_mobiusDivisorSquareRootAbel_sub_half_chebyshevNormalizedCesaroSum_linear
  rw [riemannHypothesis_iff_mobiusDivisorSquareRootAbel_pow_bddBelow hm]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨2 * (-C + B), fun N hN3 => ?_⟩
    have hNm3 : 3 ≤ N ^ m :=
      le_trans hN3 (Nat.le_self_pow (by omega : m ≠ 0) N)
    have hpos : (0 : ℝ) < (N ^ m : ℕ) := by exact_mod_cast (show 0 < N ^ m by omega)
    have h1 := (le_div_iff₀ hpos).mp (hC N (by omega))
    have h2 := (abs_sub_le_iff.mp (hB (N ^ m) hNm3)).1
    linarith
  · rintro ⟨C, hC⟩
    obtain ⟨M₀, hM2, hM3⟩ :
        ∃ M₀ : ℝ, -M₀ ≤ mobiusDivisorSquareRootAbelMoment (2 ^ m) / (2 ^ m : ℕ) ∧
          (1 / 2 : ℝ) * C + B ≤ M₀ :=
      ⟨max (-mobiusDivisorSquareRootAbelMoment (2 ^ m) / (2 ^ m : ℕ)) ((1 / 2 : ℝ) * C + B),
        by
          have h := neg_le_neg (le_max_left
            (-mobiusDivisorSquareRootAbelMoment (2 ^ m) / (2 ^ m : ℕ))
            ((1 / 2 : ℝ) * C + B))
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
      have hdiv : -((1 / 2 : ℝ) * C + B) ≤
          mobiusDivisorSquareRootAbelMoment (N ^ m) / (N ^ m : ℕ) :=
        (le_div_iff₀ hpos).mpr (by linarith)
      exact (neg_le_neg hM3).trans hdiv

end

end GaloisForLFunctions.RHTower
