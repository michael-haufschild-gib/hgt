import GaloisForLFunctions.RHTower.MertensConstantAndCesaroIntegerLagBridge

/-!
# Terminal-Lag / Mertens-Deviation Action and Super-`√n` Lag Mesh Sampling

This module advances the observer-jet and Weil-lag programme in three directions:

1. **Exact Elimination of Interior Chebyshev `ψ` from `integerLagCesaroSum M` (`Section 1`):**
   - Combining the Abel summation-by-parts identity
     `integerLagCesaroSum_eq_terminal_sub_sum_lagBracket_diff` with the prime-jump-free unit step
     `lagBracket_succ_sub_eq` (where the prime-power jump `Λ(d + 1)` cancels identically between
     `-ψ(d + 1)` and `(d + 1) * mertensSum (d + 1)`), we eliminate all interior Chebyshev `ψ(k + 2)`
     terms from `integerLagCesaroSum M`.
   - The secondary logarithmic curvature sum is bounded by telescoping `shiftedHarmonicSqrtPrefix`
     within `[0, 4 √M]`, and the trivial-zero series sum telescopes by antitonicity within `2 √M`.
   - Consequently, for all `M ≥ 2`, `integerLagCesaroSum M` equals
     `shiftedHarmonicSqrtPrefix (M - 2) * lagBracket M - mertensDeviationHarmonicAction M`
     within an unconditional `6 √M` error (`abs_integerLagCesaroSum_sub_terminal_add_mertensDeviationHarmonicAction_le`),
     where `mertensDeviationHarmonicAction M = ∑_{k < M - 2} shiftedHarmonicSqrtPrefix (k + 1) * (mertensSum (k + 2) - log (k + 2) + γ)`
     depends only on the harmonic von Mangoldt Mertens deviation around `-γ`.

2. **Direct Terminal-Lag / Mertens-Deviation Action and `-M * integerLag M` Coupling (`Section 2`):**
   - Substituting into `integerLagLinearCesaroAction M = (4 / 3) M * integerLag M - 2 * integerLagCesaroSum M`
     shows that `completedSourceObserverJetSqrtMassAction M` agrees within `O(√M)` unconditionally
     with `integerLagMertensHarmonicAction M`
     (`abs_completedSourceObserverJetSqrtMassAction_sub_mertensHarmonicAction_le`).
   - Using `1 ≤ 2 √M - shiftedHarmonicSqrtPrefix (M - 2) ≤ 3` and `lagBracket M = √M * integerLag M`,
     the terminal coefficient simplifies via `(4 / 3) M - 2 * (2 √M) * √M = -(8 / 3) M`, reducing the
     action to `integerLagMertensCanonicalAction M = -(8 / 3) M * integerLag M + 2 * mertensDeviationHarmonicAction M`
     and `integerLagMertensSqrtAction M = -(8 / 3) M * integerLag M + 2 * mertensDeviationSqrtAction M`.
   - Multiplying by `3 / 8` cancels `-(8 / 3)` to `-1`, yielding the direct coupling
     `mobiusDivisorSquareRootAbelMoment M = -(M : ℝ) * integerLag M + (3 / 4) * mertensDeviationSqrtAction M + O(M)`
     (`exists_abs_mobiusDivisorSquareRootAbel_sub_neg_mul_integerLag_add_mertensSqrtAction_linear`)
     and exact one-sided and `M = N^m` RH equivalences.

3. **Prime-Jump-Free Mertens Bound for `lagPrimeChordCharge` and Super-`√n` Lag Mesh Sampling (`Section 3`):**
   - Keeping `1 / j` inside `lagPrimeChordCharge m n m u v` and bounding
     `min (u (j - n)) (v (m - j)) ≤ u * v * (m - n)` yields the Brun–Titchmarsh-free bound
     `lagPrimeChordCharge m n m u v ≤ u * v * (m - n) * (mertensSum m - mertensSum n)`
     (`lagPrimeChordCharge_le_mertensSum_sub`) and the corresponding lower chord interpolation
     `integerLag_ge_endpoint_floor_mertens`.
   - Combining `exists_exponentially_damped_integerLag_lipschitz` with single-endpoint transport
     yields one-sided RH equivalences along any super-`√n` sampling mesh with gaps up to
     `K * √k * exp(c * √(log k))` (`riemannHypothesis_iff_integerLag_bddAbove_of_exp_sqrt_log_samples`,
     `riemannHypothesis_iff_integerLag_bddBelow_of_exp_sqrt_log_samples`).
-/

open Complex Filter Topology Set MeasureTheory Real
open scoped BigOperators Chebyshev
open ArithmeticFunction (vonMangoldt)

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

noncomputable section

/-! ## Section 1: Sandwich for `shiftedHarmonicSqrtPrefix` and `6 √M` Elimination of Interior
Chebyshev `ψ` from `integerLagCesaroSum M` -/

/-- Nonnegativity of `shiftedHarmonicSqrtPrefix k = harmonicSqrtPrefix (k + 1) - 1`. -/
theorem shiftedHarmonicSqrtPrefix_nonneg (k : ℕ) : 0 ≤ shiftedHarmonicSqrtPrefix k := by
  induction k with
  | zero => simp
  | succ n ih =>
    have hstep := shiftedHarmonicSqrtPrefix_succ_sub n
    have hpos : (0 : ℝ) ≤ 1 / Real.sqrt (n + 2 : ℕ) := by positivity
    linarith

/-- Monotonicity of `shiftedHarmonicSqrtPrefix`. -/
theorem shiftedHarmonicSqrtPrefix_mono {a b : ℕ} (hab : a ≤ b) :
    shiftedHarmonicSqrtPrefix a ≤ shiftedHarmonicSqrtPrefix b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih =>
    have hstep := shiftedHarmonicSqrtPrefix_succ_sub k
    have hpos : (0 : ℝ) ≤ 1 / Real.sqrt (k + 2 : ℕ) := by positivity
    linarith

/-- Upper bound `shiftedHarmonicSqrtPrefix k ≤ 2 * √(k + 1) - 1`. -/
theorem shiftedHarmonicSqrtPrefix_le_two_mul_sqrt_succ_sub_one (k : ℕ) :
    shiftedHarmonicSqrtPrefix k ≤ 2 * Real.sqrt (k + 1 : ℕ) - 1 := by
  unfold shiftedHarmonicSqrtPrefix
  have h := harmonicSqrtPrefix_le_two_mul_sqrt (k + 1)
  linarith

/-- Upper bound `shiftedHarmonicSqrtPrefix k ≤ 2 * √(k + 1)`. -/
theorem shiftedHarmonicSqrtPrefix_le_two_mul_sqrt_succ (k : ℕ) :
    shiftedHarmonicSqrtPrefix k ≤ 2 * Real.sqrt (k + 1 : ℕ) := by
  have h := shiftedHarmonicSqrtPrefix_le_two_mul_sqrt_succ_sub_one k
  linarith

/-- Lower bound `2 * √(k + 2) - 3 ≤ shiftedHarmonicSqrtPrefix k`. -/
theorem two_mul_sqrt_add_two_sub_three_le_shiftedHarmonicSqrtPrefix (k : ℕ) :
    2 * Real.sqrt (k + 2 : ℕ) - 3 ≤ shiftedHarmonicSqrtPrefix k := by
  unfold shiftedHarmonicSqrtPrefix
  have h := two_mul_sqrt_succ_sub_two_le_harmonicSqrtPrefix (k + 1)
  linarith

/-- Sharp sandwich `1 ≤ 2 * √(k + 2) - shiftedHarmonicSqrtPrefix (k + 1) ≤ 3` for all `k : ℕ`. -/
theorem one_le_two_mul_sqrt_add_two_sub_shiftedHarmonicSqrtPrefix_succ (k : ℕ) :
    1 ≤ 2 * Real.sqrt (k + 2 : ℕ) - shiftedHarmonicSqrtPrefix (k + 1) := by
  have h := shiftedHarmonicSqrtPrefix_le_two_mul_sqrt_succ_sub_one (k + 1)
  linarith

theorem two_mul_sqrt_add_two_sub_shiftedHarmonicSqrtPrefix_succ_le_three (k : ℕ) :
    2 * Real.sqrt (k + 2 : ℕ) - shiftedHarmonicSqrtPrefix (k + 1) ≤ 3 := by
  have h := two_mul_sqrt_add_two_sub_three_le_shiftedHarmonicSqrtPrefix (k + 1)
  have hle : Real.sqrt (k + 2 : ℕ) ≤ Real.sqrt (k + 1 + 2 : ℕ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast (show k + 2 ≤ k + 1 + 2 by omega))
  linarith

/-- For all `M ≥ 2`, `1 ≤ 2 * √M - shiftedHarmonicSqrtPrefix (M - 2) ≤ 3`, so
`|shiftedHarmonicSqrtPrefix (M - 2) - 2 * √M| ≤ 3`. -/
theorem shiftedHarmonicSqrtPrefix_sub_two_bounds {M : ℕ} (hM : 2 ≤ M) :
    1 ≤ 2 * Real.sqrt (M : ℝ) - shiftedHarmonicSqrtPrefix (M - 2) ∧
      2 * Real.sqrt (M : ℝ) - shiftedHarmonicSqrtPrefix (M - 2) ≤ 3 := by
  have h1 := shiftedHarmonicSqrtPrefix_le_two_mul_sqrt_succ_sub_one (M - 2)
  have h2 := two_mul_sqrt_add_two_sub_three_le_shiftedHarmonicSqrtPrefix (M - 2)
  have hcast2 : (M - 2 + 2 : ℕ) = M := by omega
  rw [hcast2] at h2
  have hle : Real.sqrt (M - 2 + 1 : ℕ) ≤ Real.sqrt (M : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast (show M - 2 + 1 ≤ M by omega))
  constructor <;> linarith

theorem abs_shiftedHarmonicSqrtPrefix_sub_two_mul_sqrt_le_three {M : ℕ} (hM : 2 ≤ M) :
    |shiftedHarmonicSqrtPrefix (M - 2) - 2 * Real.sqrt (M : ℝ)| ≤ 3 := by
  have hb := shiftedHarmonicSqrtPrefix_sub_two_bounds hM
  rw [abs_le]
  constructor <;> linarith

/-- **Harmonic-Weighted Mertens-Deviation Action:**
`mertensDeviationHarmonicAction M = ∑_{k < M - 2} shiftedHarmonicSqrtPrefix (k + 1) * (mertensSum (k + 2) - log (k + 2) + γ)`. -/
def mertensDeviationHarmonicAction (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (M - 2),
    shiftedHarmonicSqrtPrefix (k + 1) *
      (mertensSum (k + 2) - Real.log (k + 2 : ℕ) + Real.eulerMascheroniConstant)

/-- **Square-Root-Weighted Mertens-Deviation Action:**
`mertensDeviationSqrtAction M = ∑_{k < M - 2} 2 √(k + 2) * (mertensSum (k + 2) - log (k + 2) + γ)`. -/
def mertensDeviationSqrtAction (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (M - 2),
    2 * Real.sqrt (k + 2 : ℕ) *
      (mertensSum (k + 2) - Real.log (k + 2 : ℕ) + Real.eulerMascheroniConstant)

/-- Pointwise bounds `0 ≤ (d + 1) * log ((d + 1) / d) - 1 ≤ 1 / d` for `d ≥ 1`. -/
theorem mul_log_succ_div_sub_one_bounds {d : ℕ} (hd : 1 ≤ d) :
    0 ≤ ((d + 1 : ℕ) : ℝ) * Real.log (((d + 1 : ℕ) : ℝ) / (d : ℝ)) - 1 ∧
      ((d + 1 : ℕ) : ℝ) * Real.log (((d + 1 : ℕ) : ℝ) / (d : ℝ)) - 1 ≤ 1 / (d : ℝ) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hcast : ((d + 1 : ℕ) : ℝ) = (d : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have hup : Real.log (((d : ℝ) + 1) / d) ≤ 1 / (d : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((d : ℝ) + 1) / d by positivity)
    have e : ((d : ℝ) + 1) / d - 1 = 1 / (d : ℝ) := by field_simp; ring
    linarith
  have hlow : 1 / ((d : ℝ) + 1) ≤ Real.log (((d : ℝ) + 1) / d) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (d : ℝ) / (d + 1) by positivity)
    have e1 : (d : ℝ) / (d + 1) - 1 = -(1 / ((d : ℝ) + 1)) := by field_simp; ring
    have e2 : Real.log ((d : ℝ) / (d + 1)) = -Real.log (((d : ℝ) + 1) / d) := by
      rw [← Real.log_inv, inv_div]
    linarith
  constructor
  · have hmul := mul_le_mul_of_nonneg_left hlow (show (0 : ℝ) ≤ (d : ℝ) + 1 by positivity)
    have heq : ((d : ℝ) + 1) * (1 / ((d : ℝ) + 1)) = 1 := by field_simp
    linarith
  · have hmul := mul_le_mul_of_nonneg_left hup (show (0 : ℝ) ≤ (d : ℝ) + 1 by positivity)
    have heq : ((d : ℝ) + 1) * (1 / (d : ℝ)) - 1 = 1 / (d : ℝ) := by field_simp; ring
    linarith

/-- The logarithmic curvature remainder sum in `integerLagCesaroSum_eq_terminal_sub_sum_lagBracket_diff`
lies in `[0, 4 * √M]` for all `M : ℕ`. -/
theorem sum_shiftedHarmonicSqrtPrefix_mul_log_curvature_bounds (M : ℕ) :
    0 ≤ ∑ k ∈ Finset.range (M - 2),
        shiftedHarmonicSqrtPrefix (k + 1) *
          (((k + 3 : ℕ) : ℝ) * Real.log (((k + 3 : ℕ) : ℝ) / (k + 2 : ℕ)) - 1) ∧
      (∑ k ∈ Finset.range (M - 2),
        shiftedHarmonicSqrtPrefix (k + 1) *
          (((k + 3 : ℕ) : ℝ) * Real.log (((k + 3 : ℕ) : ℝ) / (k + 2 : ℕ)) - 1)) ≤
        4 * Real.sqrt (M : ℝ) := by
  constructor
  · apply Finset.sum_nonneg
    intro k _
    have h1 := shiftedHarmonicSqrtPrefix_nonneg (k + 1)
    have h2 := (mul_log_succ_div_sub_one_bounds (d := k + 2) (by omega)).1
    exact mul_nonneg h1 h2
  · have hterm : ∀ k ∈ Finset.range (M - 2),
        shiftedHarmonicSqrtPrefix (k + 1) *
          (((k + 3 : ℕ) : ℝ) * Real.log (((k + 3 : ℕ) : ℝ) / (k + 2 : ℕ)) - 1) ≤
          2 * (shiftedHarmonicSqrtPrefix (k + 1) - shiftedHarmonicSqrtPrefix k) := by
      intro k _
      have hk0 : (0 : ℝ) < (k + 2 : ℕ) := by positivity
      have hsk : 0 < Real.sqrt (k + 2 : ℕ) := Real.sqrt_pos.mpr hk0
      have hsq : Real.sqrt (k + 2 : ℕ) * Real.sqrt (k + 2 : ℕ) = (k + 2 : ℕ) :=
        Real.mul_self_sqrt hk0.le
      have hpref := shiftedHarmonicSqrtPrefix_le_two_mul_sqrt_succ (k + 1)
      have hcurv := (mul_log_succ_div_sub_one_bounds (d := k + 2) (by omega)).2
      have hcurv0 := (mul_log_succ_div_sub_one_bounds (d := k + 2) (by omega)).1
      have hpref0 := shiftedHarmonicSqrtPrefix_nonneg (k + 1)
      rw [shiftedHarmonicSqrtPrefix_succ_sub]
      calc
        shiftedHarmonicSqrtPrefix (k + 1) *
            (((k + 3 : ℕ) : ℝ) * Real.log (((k + 3 : ℕ) : ℝ) / (k + 2 : ℕ)) - 1) ≤
          (2 * Real.sqrt (k + 2 : ℕ)) * (1 / (k + 2 : ℕ)) :=
          mul_le_mul hpref hcurv hcurv0 (by positivity)
        _ = 2 * (Real.sqrt (k + 2 : ℕ) / (Real.sqrt (k + 2 : ℕ) * Real.sqrt (k + 2 : ℕ))) := by
          rw [hsq]; ring
        _ = 2 * (1 / Real.sqrt (k + 2 : ℕ)) := by
          congr 1
          field_simp [hsk.ne']
    have htel :
        (∑ k ∈ Finset.range (M - 2),
            2 * (shiftedHarmonicSqrtPrefix (k + 1) - shiftedHarmonicSqrtPrefix k)) =
          2 * shiftedHarmonicSqrtPrefix (M - 2) := by
      rw [← Finset.mul_sum, Finset.sum_range_sub (fun k => shiftedHarmonicSqrtPrefix k),
        shiftedHarmonicSqrtPrefix_zero, sub_zero]
    rcases lt_or_ge M 2 with hM2 | hM2
    · have h0 : M - 2 = 0 := by omega
      rw [h0]
      simp [Real.sqrt_nonneg]
    · have hbound : shiftedHarmonicSqrtPrefix (M - 2) ≤ 2 * Real.sqrt (M : ℝ) := by
        have h := (shiftedHarmonicSqrtPrefix_sub_two_bounds hM2).1
        linarith
      calc
        (∑ k ∈ Finset.range (M - 2),
            shiftedHarmonicSqrtPrefix (k + 1) *
              (((k + 3 : ℕ) : ℝ) * Real.log (((k + 3 : ℕ) : ℝ) / (k + 2 : ℕ)) - 1)) ≤
          ∑ k ∈ Finset.range (M - 2),
            2 * (shiftedHarmonicSqrtPrefix (k + 1) - shiftedHarmonicSqrtPrefix k) :=
          Finset.sum_le_sum hterm
        _ = 2 * shiftedHarmonicSqrtPrefix (M - 2) := htel
        _ ≤ 4 * Real.sqrt (M : ℝ) := by linarith

/-- The trivial-zero series remainder sum in `integerLagCesaroSum_eq_terminal_sub_sum_lagBracket_diff`
has absolute value at most `2 * √M` for all `M : ℕ`. -/
theorem abs_sum_shiftedHarmonicSqrtPrefix_mul_trivialZeroSeries_diff_le (M : ℕ) :
    |∑ k ∈ Finset.range (M - 2),
        shiftedHarmonicSqrtPrefix (k + 1) *
          (trivialZeroSeriesReal (k + 3 : ℕ) - trivialZeroSeriesReal (k + 2 : ℕ))| ≤
      2 * Real.sqrt (M : ℝ) := by
  have hterm : ∀ k ∈ Finset.range (M - 2),
      |shiftedHarmonicSqrtPrefix (k + 1) *
          (trivialZeroSeriesReal (k + 3 : ℕ) - trivialZeroSeriesReal (k + 2 : ℕ))| ≤
        2 * Real.sqrt (M : ℝ) *
          (trivialZeroSeriesReal (k + 2 : ℕ) - trivialZeroSeriesReal (k + 3 : ℕ)) := by
    intro k hk
    have hkM : k < M - 2 := Finset.mem_range.mp hk
    have hpref0 := shiftedHarmonicSqrtPrefix_nonneg (k + 1)
    have hpref : shiftedHarmonicSqrtPrefix (k + 1) ≤ 2 * Real.sqrt (M : ℝ) := by
      calc
        shiftedHarmonicSqrtPrefix (k + 1) ≤ 2 * Real.sqrt (k + 2 : ℕ) :=
          shiftedHarmonicSqrtPrefix_le_two_mul_sqrt_succ (k + 1)
        _ ≤ 2 * Real.sqrt (M : ℝ) := by
          gcongr
          exact_mod_cast (show k + 2 ≤ M by omega)
    have hanti : trivialZeroSeriesReal (k + 3 : ℕ) ≤ trivialZeroSeriesReal (k + 2 : ℕ) :=
      trivialZeroSeriesReal_anti (by exact_mod_cast (show 1 ≤ k + 2 by omega))
        (by exact_mod_cast (show k + 2 ≤ k + 3 by omega))
    rw [abs_mul, abs_of_nonneg hpref0, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hanti)]
    exact mul_le_mul_of_nonneg_right hpref (sub_nonneg.mpr hanti)
  have htel :
      (∑ k ∈ Finset.range (M - 2),
          (trivialZeroSeriesReal (k + 2 : ℕ) - trivialZeroSeriesReal (k + 3 : ℕ))) =
        trivialZeroSeriesReal (2 : ℕ) - trivialZeroSeriesReal (M - 2 + 2 : ℕ) := by
    have h := Finset.sum_range_sub' (fun k => trivialZeroSeriesReal (k + 2 : ℕ)) (M - 2)
    simpa [Nat.add_assoc] using h
  have hS2 : trivialZeroSeriesReal (2 : ℕ) ≤ 1 :=
    trivialZeroSeriesReal_le_one (by norm_num)
  have hSM : 0 ≤ trivialZeroSeriesReal (M - 2 + 2 : ℕ) :=
    trivialZeroSeriesReal_nonneg (by exact_mod_cast (show 1 ≤ M - 2 + 2 by omega))
  calc
    |∑ k ∈ Finset.range (M - 2),
        shiftedHarmonicSqrtPrefix (k + 1) *
          (trivialZeroSeriesReal (k + 3 : ℕ) - trivialZeroSeriesReal (k + 2 : ℕ))| ≤
      ∑ k ∈ Finset.range (M - 2),
        |shiftedHarmonicSqrtPrefix (k + 1) *
          (trivialZeroSeriesReal (k + 3 : ℕ) - trivialZeroSeriesReal (k + 2 : ℕ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (M - 2),
        2 * Real.sqrt (M : ℝ) *
          (trivialZeroSeriesReal (k + 2 : ℕ) - trivialZeroSeriesReal (k + 3 : ℕ)) :=
      Finset.sum_le_sum hterm
    _ = 2 * Real.sqrt (M : ℝ) *
        (trivialZeroSeriesReal (2 : ℕ) - trivialZeroSeriesReal (M - 2 + 2 : ℕ)) := by
      rw [← Finset.mul_sum, htel]
    _ ≤ 2 * Real.sqrt (M : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = 2 * Real.sqrt (M : ℝ) := mul_one _

/-- **Exact `6 √M` Elimination of Interior Chebyshev `ψ` from `integerLagCesaroSum M`:**
For all `M ≥ 2`, `integerLagCesaroSum M` equals
`shiftedHarmonicSqrtPrefix (M - 2) * lagBracket M - mertensDeviationHarmonicAction M`
within `6 * √M`. -/
theorem abs_integerLagCesaroSum_sub_terminal_add_mertensDeviationHarmonicAction_le
    {M : ℕ} (hM : 2 ≤ M) :
    |integerLagCesaroSum M -
        (shiftedHarmonicSqrtPrefix (M - 2) * lagBracket M -
          mertensDeviationHarmonicAction M)| ≤
      6 * Real.sqrt (M : ℝ) := by
  have hM2 : M - 2 + 2 = M := by omega
  have hident :
      integerLagCesaroSum M -
          (shiftedHarmonicSqrtPrefix (M - 2) * lagBracket M -
            mertensDeviationHarmonicAction M) =
        (∑ k ∈ Finset.range (M - 2),
            shiftedHarmonicSqrtPrefix (k + 1) *
              (((k + 3 : ℕ) : ℝ) * Real.log (((k + 3 : ℕ) : ℝ) / (k + 2 : ℕ)) - 1)) -
          ∑ k ∈ Finset.range (M - 2),
            shiftedHarmonicSqrtPrefix (k + 1) *
              (trivialZeroSeriesReal (k + 3 : ℕ) - trivialZeroSeriesReal (k + 2 : ℕ)) := by
    rw [integerLagCesaroSum_eq_terminal_sub_sum_lagBracket_diff M, hM2]
    unfold mertensDeviationHarmonicAction
    have hsum :
        (∑ k ∈ Finset.range (M - 2),
            shiftedHarmonicSqrtPrefix (k + 1) * (lagBracket (k + 3) - lagBracket (k + 2))) =
          (∑ k ∈ Finset.range (M - 2),
              shiftedHarmonicSqrtPrefix (k + 1) *
                (mertensSum (k + 2) - Real.log (k + 2 : ℕ) + Real.eulerMascheroniConstant)) -
            (∑ k ∈ Finset.range (M - 2),
              shiftedHarmonicSqrtPrefix (k + 1) *
                (((k + 3 : ℕ) : ℝ) * Real.log (((k + 3 : ℕ) : ℝ) / (k + 2 : ℕ)) - 1)) +
            ∑ k ∈ Finset.range (M - 2),
              shiftedHarmonicSqrtPrefix (k + 1) *
                (trivialZeroSeriesReal (k + 3 : ℕ) - trivialZeroSeriesReal (k + 2 : ℕ)) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      have hstep := lagBracket_succ_sub_eq (d := k + 2) (by omega)
      rw [show k + 2 + 1 = k + 3 by omega] at hstep
      rw [hstep]
      push_cast
      ring
    rw [hsum]
    ring
  rw [hident]
  have hcurv := sum_shiftedHarmonicSqrtPrefix_mul_log_curvature_bounds M
  have habs_curv :
      |∑ k ∈ Finset.range (M - 2),
          shiftedHarmonicSqrtPrefix (k + 1) *
            (((k + 3 : ℕ) : ℝ) * Real.log (((k + 3 : ℕ) : ℝ) / (k + 2 : ℕ)) - 1)| ≤
        4 * Real.sqrt (M : ℝ) := by
    rw [abs_of_nonneg hcurv.1]
    exact hcurv.2
  have htriv := abs_sum_shiftedHarmonicSqrtPrefix_mul_trivialZeroSeries_diff_le M
  calc
    |(∑ k ∈ Finset.range (M - 2),
          shiftedHarmonicSqrtPrefix (k + 1) *
            (((k + 3 : ℕ) : ℝ) * Real.log (((k + 3 : ℕ) : ℝ) / (k + 2 : ℕ)) - 1)) -
        ∑ k ∈ Finset.range (M - 2),
          shiftedHarmonicSqrtPrefix (k + 1) *
            (trivialZeroSeriesReal (k + 3 : ℕ) - trivialZeroSeriesReal (k + 2 : ℕ))| ≤
      |∑ k ∈ Finset.range (M - 2),
          shiftedHarmonicSqrtPrefix (k + 1) *
            (((k + 3 : ℕ) : ℝ) * Real.log (((k + 3 : ℕ) : ℝ) / (k + 2 : ℕ)) - 1)| +
        |∑ k ∈ Finset.range (M - 2),
          shiftedHarmonicSqrtPrefix (k + 1) *
            (trivialZeroSeriesReal (k + 3 : ℕ) - trivialZeroSeriesReal (k + 2 : ℕ))| :=
      abs_sub _ _
    _ ≤ 4 * Real.sqrt (M : ℝ) + 2 * Real.sqrt (M : ℝ) := add_le_add habs_curv htriv
    _ = 6 * Real.sqrt (M : ℝ) := by ring

/-! ## Section 2: Direct Terminal-Lag / Mertens-Deviation Actions and `-M * integerLag M` Coupling -/

/-- **Harmonic-Weighted Terminal-Lag / Mertens-Deviation Action:**
`integerLagMertensHarmonicAction M = (4 / 3) * M * integerLag M - 2 * shiftedHarmonicSqrtPrefix (M - 2) * lagBracket M + 2 * mertensDeviationHarmonicAction M`. -/
def integerLagMertensHarmonicAction (M : ℕ) : ℝ :=
  (4 / 3 : ℝ) * (M : ℝ) * integerLag M -
    2 * shiftedHarmonicSqrtPrefix (M - 2) * lagBracket M +
    2 * mertensDeviationHarmonicAction M

/-- **Canonical Terminal-Lag / Mertens-Deviation Action:**
Replacing `shiftedHarmonicSqrtPrefix (M - 2)` by `2 * √M` and using `lagBracket M = √M * integerLag M`
combines `(4 / 3) * M * integerLag M - 4 * M * integerLag M = -(8 / 3) * M * integerLag M`. -/
def integerLagMertensCanonicalAction (M : ℕ) : ℝ :=
  -(8 / 3 : ℝ) * (M : ℝ) * integerLag M + 2 * mertensDeviationHarmonicAction M

/-- **Square-Root-Weighted Terminal-Lag / Mertens-Deviation Action:**
`integerLagMertensSqrtAction M = -(8 / 3) * M * integerLag M + 2 * mertensDeviationSqrtAction M`. -/
def integerLagMertensSqrtAction (M : ℕ) : ℝ :=
  -(8 / 3 : ℝ) * (M : ℝ) * integerLag M + 2 * mertensDeviationSqrtAction M

/-- **Unconditional `12 √M` Bridge Between `integerLagLinearCesaroAction` and
`integerLagMertensHarmonicAction`:**
For all `M ≥ 2`,
`|integerLagLinearCesaroAction M - integerLagMertensHarmonicAction M| ≤ 12 * √M`. -/
theorem abs_integerLagLinearCesaroAction_sub_mertensHarmonicAction_le {M : ℕ} (hM : 2 ≤ M) :
    |integerLagLinearCesaroAction M - integerLagMertensHarmonicAction M| ≤
      12 * Real.sqrt (M : ℝ) := by
  have h1 := abs_integerLagCesaroSum_sub_terminal_add_mertensDeviationHarmonicAction_le hM
  have hident :
      integerLagLinearCesaroAction M - integerLagMertensHarmonicAction M =
        -2 * (integerLagCesaroSum M -
          (shiftedHarmonicSqrtPrefix (M - 2) * lagBracket M -
            mertensDeviationHarmonicAction M)) := by
    unfold integerLagLinearCesaroAction integerLagMertensHarmonicAction
    ring
  rw [hident, abs_mul, show |(-2 : ℝ)| = 2 by norm_num]
  linarith

/-- **Unconditional `O(√M)` Bridge Between `completedSourceObserverJetSqrtMassAction` and
`integerLagMertensHarmonicAction`:**
For all `M ≥ 3`,
`|completedSourceObserverJetSqrtMassAction M - integerLagMertensHarmonicAction M| ≤ (6 * (7 + |2γ|) + 92) * √M`. -/
theorem abs_completedSourceObserverJetSqrtMassAction_sub_mertensHarmonicAction_le
    {M : ℕ} (hM : 3 ≤ M) :
    |completedSourceObserverJetSqrtMassAction M - integerLagMertensHarmonicAction M| ≤
      (6 * (7 + |2 * Real.eulerMascheroniConstant|) + 92) * Real.sqrt (M : ℝ) := by
  have h1 := abs_completedSourceObserverJetSqrtMassAction_sub_linearCesaroAction_le hM
  have h2 := abs_integerLagLinearCesaroAction_sub_mertensHarmonicAction_le (by omega : 2 ≤ M)
  calc
    |completedSourceObserverJetSqrtMassAction M - integerLagMertensHarmonicAction M| =
      |(completedSourceObserverJetSqrtMassAction M - integerLagLinearCesaroAction M) +
        (integerLagLinearCesaroAction M - integerLagMertensHarmonicAction M)| := by ring_nf
    _ ≤ |completedSourceObserverJetSqrtMassAction M - integerLagLinearCesaroAction M| +
        |integerLagLinearCesaroAction M - integerLagMertensHarmonicAction M| := abs_add_le _ _
    _ ≤ (6 * (7 + |2 * Real.eulerMascheroniConstant|) + 80) * Real.sqrt (M : ℝ) +
        12 * Real.sqrt (M : ℝ) := add_le_add h1 h2
    _ = (6 * (7 + |2 * Real.eulerMascheroniConstant|) + 92) * Real.sqrt (M : ℝ) := by ring

/-- Exact identity `lagBracket M = √M * integerLag M` for `M ≥ 2`. -/
theorem lagBracket_eq_sqrt_mul_integerLag {M : ℕ} (hM : 2 ≤ M) :
    lagBracket M = Real.sqrt (M : ℝ) * integerLag M := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hsM : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hM0
  rw [integerLag_eq_lagBracket hM, mul_div_cancel₀ _ hsM.ne']

/-- For all `M ≥ 2`,
`|integerLagMertensHarmonicAction M - integerLagMertensCanonicalAction M| ≤ 6 * √M * |integerLag M| ≤ 120 * M`. -/
theorem abs_integerLagMertensHarmonicAction_sub_canonicalAction_le_six_mul_sqrt_mul_abs
    {M : ℕ} (hM : 2 ≤ M) :
    |integerLagMertensHarmonicAction M - integerLagMertensCanonicalAction M| ≤
      6 * Real.sqrt (M : ℝ) * |integerLag M| := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hsq : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) := Real.mul_self_sqrt hM0.le
  have hident :
      integerLagMertensHarmonicAction M - integerLagMertensCanonicalAction M =
        2 * (2 * Real.sqrt (M : ℝ) - shiftedHarmonicSqrtPrefix (M - 2)) *
          (Real.sqrt (M : ℝ) * integerLag M) := by
    unfold integerLagMertensHarmonicAction integerLagMertensCanonicalAction
    rw [lagBracket_eq_sqrt_mul_integerLag hM]
    calc
      (4 / 3 : ℝ) * (M : ℝ) * integerLag M -
          2 * shiftedHarmonicSqrtPrefix (M - 2) * (Real.sqrt (M : ℝ) * integerLag M) +
          2 * mertensDeviationHarmonicAction M -
        (-(8 / 3 : ℝ) * (M : ℝ) * integerLag M + 2 * mertensDeviationHarmonicAction M) =
        4 * (M : ℝ) * integerLag M -
          2 * shiftedHarmonicSqrtPrefix (M - 2) * (Real.sqrt (M : ℝ) * integerLag M) := by ring
      _ = 4 * (Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ)) * integerLag M -
          2 * shiftedHarmonicSqrtPrefix (M - 2) * (Real.sqrt (M : ℝ) * integerLag M) := by
        rw [hsq]
      _ = 2 * (2 * Real.sqrt (M : ℝ) - shiftedHarmonicSqrtPrefix (M - 2)) *
          (Real.sqrt (M : ℝ) * integerLag M) := by ring
  rw [hident, abs_mul, abs_mul, abs_mul, show |(2 : ℝ)| = 2 by norm_num,
    abs_of_pos (Real.sqrt_pos.mpr hM0)]
  have hb := abs_shiftedHarmonicSqrtPrefix_sub_two_mul_sqrt_le_three hM
  rw [abs_sub_comm] at hb
  calc
    2 * |2 * Real.sqrt (M : ℝ) - shiftedHarmonicSqrtPrefix (M - 2)| *
        (Real.sqrt (M : ℝ) * |integerLag M|) ≤
      2 * 3 * (Real.sqrt (M : ℝ) * |integerLag M|) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by norm_num)) (by positivity)
    _ = 6 * Real.sqrt (M : ℝ) * |integerLag M| := by ring

theorem abs_integerLagMertensHarmonicAction_sub_canonicalAction_le_linear
    {M : ℕ} (hM : 2 ≤ M) :
    |integerLagMertensHarmonicAction M - integerLagMertensCanonicalAction M| ≤
      120 * (M : ℝ) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hsq : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) := Real.mul_self_sqrt hM0.le
  have h1 := abs_integerLagMertensHarmonicAction_sub_canonicalAction_le_six_mul_sqrt_mul_abs hM
  have h2 := abs_integerLag_le_twenty_mul_sqrt hM
  calc
    |integerLagMertensHarmonicAction M - integerLagMertensCanonicalAction M| ≤
      6 * Real.sqrt (M : ℝ) * |integerLag M| := h1
    _ ≤ 6 * Real.sqrt (M : ℝ) * (20 * Real.sqrt (M : ℝ)) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 120 * (Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ)) := by ring
    _ = 120 * (M : ℝ) := by rw [hsq]

/-- Comparison between `mertensDeviationSqrtAction M` and `mertensDeviationHarmonicAction M`:
for all `M : ℕ`, `|mertensDeviationSqrtAction M - mertensDeviationHarmonicAction M| ≤ 21 * M`. -/
theorem abs_mertensDeviationSqrtAction_sub_harmonicAction_le (M : ℕ) :
    |mertensDeviationSqrtAction M - mertensDeviationHarmonicAction M| ≤
      21 * (M : ℝ) := by
  unfold mertensDeviationSqrtAction mertensDeviationHarmonicAction
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ k ∈ Finset.range (M - 2),
      |2 * Real.sqrt (k + 2 : ℕ) *
          (mertensSum (k + 2) - Real.log (k + 2 : ℕ) + Real.eulerMascheroniConstant) -
        shiftedHarmonicSqrtPrefix (k + 1) *
          (mertensSum (k + 2) - Real.log (k + 2 : ℕ) + Real.eulerMascheroniConstant)| ≤ 21 := by
    intro k _
    have hdiff :
        2 * Real.sqrt (k + 2 : ℕ) *
            (mertensSum (k + 2) - Real.log (k + 2 : ℕ) + Real.eulerMascheroniConstant) -
          shiftedHarmonicSqrtPrefix (k + 1) *
            (mertensSum (k + 2) - Real.log (k + 2 : ℕ) + Real.eulerMascheroniConstant) =
        (2 * Real.sqrt (k + 2 : ℕ) - shiftedHarmonicSqrtPrefix (k + 1)) *
          (mertensSum (k + 2) - Real.log (k + 2 : ℕ) + Real.eulerMascheroniConstant) := by ring
    rw [hdiff, abs_mul]
    have hb1 := one_le_two_mul_sqrt_add_two_sub_shiftedHarmonicSqrtPrefix_succ k
    have hb2 := two_mul_sqrt_add_two_sub_shiftedHarmonicSqrtPrefix_succ_le_three k
    have habs1 : |2 * Real.sqrt (k + 2 : ℕ) - shiftedHarmonicSqrtPrefix (k + 1)| ≤ 3 := by
      rw [abs_of_nonneg (by linarith)]
      exact hb2
    have hM7 := abs_mertensDeviation_le_seven (d := k + 2) (by omega)
    calc
      |2 * Real.sqrt (k + 2 : ℕ) - shiftedHarmonicSqrtPrefix (k + 1)| *
          |mertensSum (k + 2) - Real.log (k + 2 : ℕ) + Real.eulerMascheroniConstant| ≤
        3 * 7 := mul_le_mul habs1 hM7 (abs_nonneg _) (by norm_num)
      _ = 21 := by norm_num
  have hle : ((M - 2 : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.sub_le M 2
  calc
    |∑ k ∈ Finset.range (M - 2),
        (2 * Real.sqrt (k + 2 : ℕ) *
            (mertensSum (k + 2) - Real.log (k + 2 : ℕ) + Real.eulerMascheroniConstant) -
          shiftedHarmonicSqrtPrefix (k + 1) *
            (mertensSum (k + 2) - Real.log (k + 2 : ℕ) + Real.eulerMascheroniConstant))| ≤
      ∑ k ∈ Finset.range (M - 2), (21 : ℝ) :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
    _ = 21 * ((M - 2 : ℕ) : ℝ) := by simp [mul_comm]
    _ ≤ 21 * (M : ℝ) := mul_le_mul_of_nonneg_left hle (by norm_num)

/-- Comparison between `integerLagMertensCanonicalAction M` and `integerLagMertensSqrtAction M`:
for all `M : ℕ`, `|integerLagMertensCanonicalAction M - integerLagMertensSqrtAction M| ≤ 42 * M`. -/
theorem abs_integerLagMertensCanonicalAction_sub_sqrtAction_le (M : ℕ) :
    |integerLagMertensCanonicalAction M - integerLagMertensSqrtAction M| ≤
      42 * (M : ℝ) := by
  have h := abs_mertensDeviationSqrtAction_sub_harmonicAction_le M
  have hident :
      integerLagMertensCanonicalAction M - integerLagMertensSqrtAction M =
        -2 * (mertensDeviationSqrtAction M - mertensDeviationHarmonicAction M) := by
    unfold integerLagMertensCanonicalAction integerLagMertensSqrtAction
    ring
  rw [hident, abs_mul, show |(-2 : ℝ)| = 2 by norm_num]
  linarith

/-- Uniform `O(M)` comparison between `mobiusDivisorSquareRootAbelMoment M` and
`(3 / 8) * integerLagMertensCanonicalAction M = -(M : ℝ) * integerLag M + (3 / 4) * mertensDeviationHarmonicAction M`. -/
theorem exists_abs_mobiusDivisorSquareRootAbel_sub_mertensCanonicalAction_linear :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, 3 ≤ M →
      |mobiusDivisorSquareRootAbelMoment M -
        (3 / 8 : ℝ) * integerLagMertensCanonicalAction M| ≤ B * (M : ℝ) := by
  obtain ⟨B₀, hB₀, h0⟩ := exists_abs_mobiusDivisorSquareRootAbel_sub_linearCesaroAction_linear
  refine ⟨B₀ + 50, by positivity, fun M hM => ?_⟩
  have h1 := h0 M hM
  have h2 := abs_integerLagLinearCesaroAction_sub_mertensHarmonicAction_le (by omega : 2 ≤ M)
  have h3 := abs_integerLagMertensHarmonicAction_sub_canonicalAction_le_linear (by omega : 2 ≤ M)
  have hsqrt_le : Real.sqrt (M : ℝ) ≤ (M : ℝ) := by
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
    have hsq : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    have hs1 : (1 : ℝ) ≤ Real.sqrt (M : ℝ) := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hM1
    nlinarith
  have h23 :
      |integerLagLinearCesaroAction M - integerLagMertensCanonicalAction M| ≤
        132 * (M : ℝ) := by
    calc
      |integerLagLinearCesaroAction M - integerLagMertensCanonicalAction M| =
        |(integerLagLinearCesaroAction M - integerLagMertensHarmonicAction M) +
          (integerLagMertensHarmonicAction M - integerLagMertensCanonicalAction M)| := by ring_nf
      _ ≤ |integerLagLinearCesaroAction M - integerLagMertensHarmonicAction M| +
          |integerLagMertensHarmonicAction M - integerLagMertensCanonicalAction M| :=
        abs_add_le _ _
      _ ≤ 12 * Real.sqrt (M : ℝ) + 120 * (M : ℝ) := add_le_add h2 h3
      _ ≤ 132 * (M : ℝ) := by linarith
  calc
    |mobiusDivisorSquareRootAbelMoment M -
        (3 / 8 : ℝ) * integerLagMertensCanonicalAction M| =
      |(mobiusDivisorSquareRootAbelMoment M - (3 / 8 : ℝ) * integerLagLinearCesaroAction M) +
        (3 / 8 : ℝ) * (integerLagLinearCesaroAction M - integerLagMertensCanonicalAction M)| := by
      ring_nf
    _ ≤ |mobiusDivisorSquareRootAbelMoment M - (3 / 8 : ℝ) * integerLagLinearCesaroAction M| +
        |(3 / 8 : ℝ) * (integerLagLinearCesaroAction M - integerLagMertensCanonicalAction M)| :=
      abs_add_le _ _
    _ = |mobiusDivisorSquareRootAbelMoment M - (3 / 8 : ℝ) * integerLagLinearCesaroAction M| +
        (3 / 8 : ℝ) * |integerLagLinearCesaroAction M - integerLagMertensCanonicalAction M| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 8)]
    _ ≤ B₀ * (M : ℝ) + (3 / 8 : ℝ) * (132 * (M : ℝ)) :=
      add_le_add h1 (mul_le_mul_of_nonneg_left h23 (by norm_num))
    _ ≤ (B₀ + 50) * (M : ℝ) := by linarith

/-- **Direct Coupling Law Between `mobiusDivisorSquareRootAbelMoment M`, `-M * integerLag M`, and
`mertensDeviationSqrtAction M`:**
There exists `B ≥ 0` such that for all `M ≥ 3`,
`|mobiusDivisorSquareRootAbelMoment M - (-(M : ℝ) * integerLag M + (3 / 4) * mertensDeviationSqrtAction M)| ≤ B * M`. -/
theorem exists_abs_mobiusDivisorSquareRootAbel_sub_neg_mul_integerLag_add_mertensSqrtAction_linear :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, 3 ≤ M →
      |mobiusDivisorSquareRootAbelMoment M -
        (-(M : ℝ) * integerLag M + (3 / 4 : ℝ) * mertensDeviationSqrtAction M)| ≤ B * (M : ℝ) := by
  obtain ⟨B₀, hB₀, h0⟩ := exists_abs_mobiusDivisorSquareRootAbel_sub_mertensCanonicalAction_linear
  refine ⟨B₀ + 16, by positivity, fun M hM => ?_⟩
  have h1 := h0 M hM
  have h2 := abs_integerLagMertensCanonicalAction_sub_sqrtAction_le M
  have hscale :
      -(M : ℝ) * integerLag M + (3 / 4 : ℝ) * mertensDeviationSqrtAction M =
        (3 / 8 : ℝ) * integerLagMertensSqrtAction M := by
    unfold integerLagMertensSqrtAction
    ring
  rw [hscale]
  calc
    |mobiusDivisorSquareRootAbelMoment M -
        (3 / 8 : ℝ) * integerLagMertensSqrtAction M| =
      |(mobiusDivisorSquareRootAbelMoment M - (3 / 8 : ℝ) * integerLagMertensCanonicalAction M) +
        (3 / 8 : ℝ) * (integerLagMertensCanonicalAction M - integerLagMertensSqrtAction M)| := by
      ring_nf
    _ ≤ |mobiusDivisorSquareRootAbelMoment M - (3 / 8 : ℝ) * integerLagMertensCanonicalAction M| +
        |(3 / 8 : ℝ) * (integerLagMertensCanonicalAction M - integerLagMertensSqrtAction M)| :=
      abs_add_le _ _
    _ = |mobiusDivisorSquareRootAbelMoment M - (3 / 8 : ℝ) * integerLagMertensCanonicalAction M| +
        (3 / 8 : ℝ) * |integerLagMertensCanonicalAction M - integerLagMertensSqrtAction M| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 8)]
    _ ≤ B₀ * (M : ℝ) + (3 / 8 : ℝ) * (42 * (M : ℝ)) :=
      add_le_add h1 (mul_le_mul_of_nonneg_left h2 (by norm_num))
    _ ≤ (B₀ + 16) * (M : ℝ) := by linarith

/-- **One-sided upper RH equivalence for `integerLagMertensSqrtAction`:**
RH holds iff `-(8 / 3) * M * integerLag M + 2 * mertensDeviationSqrtAction M ≤ C * M` for all `M ≥ 3`. -/
theorem riemannHypothesis_iff_integerLagMertensSqrtAction_boundedAbove :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ M : ℕ, 3 ≤ M →
        integerLagMertensSqrtAction M ≤ C * (M : ℝ) := by
  obtain ⟨B, _hB0, hB⟩ :=
    exists_abs_mobiusDivisorSquareRootAbel_sub_neg_mul_integerLag_add_mertensSqrtAction_linear
  have hscale : ∀ M : ℕ,
      -(M : ℝ) * integerLag M + (3 / 4 : ℝ) * mertensDeviationSqrtAction M =
        (3 / 8 : ℝ) * integerLagMertensSqrtAction M := by
    intro M; unfold integerLagMertensSqrtAction; ring
  rw [riemannHypothesis_iff_mobiusDivisorSquareRootAbel_boundedAbove]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨(8 / 3 : ℝ) * (C + B), fun M hM3 => ?_⟩
    have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    have h1 := (div_le_iff₀ hMpos).mp (hC M (by omega))
    have h2 := hB M hM3
    rw [hscale M] at h2
    have h2' := (abs_sub_le_iff.mp h2).2
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
      have h2 := hB M hM_ge_3
      rw [hscale M] at h2
      have h2' := (abs_sub_le_iff.mp h2).1
      have hdiv : mobiusDivisorSquareRootAbelMoment M / (M : ℝ) ≤ (3 / 8 : ℝ) * C + B :=
        (div_le_iff₀ hMpos).mpr (by linarith)
      exact hdiv.trans hM3

/-- **One-sided lower RH equivalence for `integerLagMertensSqrtAction`:**
RH holds iff `-C * M ≤ -(8 / 3) * M * integerLag M + 2 * mertensDeviationSqrtAction M` for all `M ≥ 3`. -/
theorem riemannHypothesis_iff_integerLagMertensSqrtAction_boundedBelow :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ M : ℕ, 3 ≤ M →
        -C * (M : ℝ) ≤ integerLagMertensSqrtAction M := by
  obtain ⟨B, _hB0, hB⟩ :=
    exists_abs_mobiusDivisorSquareRootAbel_sub_neg_mul_integerLag_add_mertensSqrtAction_linear
  have hscale : ∀ M : ℕ,
      -(M : ℝ) * integerLag M + (3 / 4 : ℝ) * mertensDeviationSqrtAction M =
        (3 / 8 : ℝ) * integerLagMertensSqrtAction M := by
    intro M; unfold integerLagMertensSqrtAction; ring
  rw [riemannHypothesis_iff_mobiusDivisorSquareRootAbel_boundedBelow]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨(8 / 3 : ℝ) * (-C + B), fun M hM3 => ?_⟩
    have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    have h1 := (le_div_iff₀ hMpos).mp (hC M (by omega))
    have h2 := hB M hM3
    rw [hscale M] at h2
    have h2' := (abs_sub_le_iff.mp h2).1
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
      have h2 := hB M hM_ge_3
      rw [hscale M] at h2
      have h2' := (abs_sub_le_iff.mp h2).2
      have hdiv : -((3 / 8 : ℝ) * C + B) ≤ mobiusDivisorSquareRootAbelMoment M / (M : ℝ) :=
        (le_div_iff₀ hMpos).mpr (by linarith)
      exact (neg_le_neg hM3).trans hdiv

/-- **Polynomial-schedule (`M = N^m`) upper RH equivalence for `integerLagMertensSqrtAction`.** -/
theorem riemannHypothesis_iff_integerLagMertensSqrtAction_pow_bddAbove
    {m : ℕ} (hm : 1 ≤ m) :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ N : ℕ, 3 ≤ N →
        integerLagMertensSqrtAction (N ^ m) ≤ C * ((N ^ m : ℕ) : ℝ) := by
  obtain ⟨B, _hB0, hB⟩ :=
    exists_abs_mobiusDivisorSquareRootAbel_sub_neg_mul_integerLag_add_mertensSqrtAction_linear
  have hscale : ∀ M : ℕ,
      -(M : ℝ) * integerLag M + (3 / 4 : ℝ) * mertensDeviationSqrtAction M =
        (3 / 8 : ℝ) * integerLagMertensSqrtAction M := by
    intro M; unfold integerLagMertensSqrtAction; ring
  rw [riemannHypothesis_iff_mobiusDivisorSquareRootAbel_pow_bddAbove hm]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨(8 / 3 : ℝ) * (C + B), fun N hN3 => ?_⟩
    have hNm3 : 3 ≤ N ^ m :=
      le_trans hN3 (Nat.le_self_pow (by omega : m ≠ 0) N)
    have hpos : (0 : ℝ) < (N ^ m : ℕ) := by exact_mod_cast (show 0 < N ^ m by omega)
    have h1 := (div_le_iff₀ hpos).mp (hC N (by omega))
    have h2 := hB (N ^ m) hNm3
    rw [hscale (N ^ m)] at h2
    have h2' := (abs_sub_le_iff.mp h2).2
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
      have h2 := hB (N ^ m) hNm3
      rw [hscale (N ^ m)] at h2
      have h2' := (abs_sub_le_iff.mp h2).1
      have hdiv : mobiusDivisorSquareRootAbelMoment (N ^ m) / (N ^ m : ℕ) ≤
          (3 / 8 : ℝ) * C + B :=
        (div_le_iff₀ hpos).mpr (by linarith)
      exact hdiv.trans hM3

/-- **Polynomial-schedule (`M = N^m`) lower RH equivalence for `integerLagMertensSqrtAction`.** -/
theorem riemannHypothesis_iff_integerLagMertensSqrtAction_pow_bddBelow
    {m : ℕ} (hm : 1 ≤ m) :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ N : ℕ, 3 ≤ N →
        -C * ((N ^ m : ℕ) : ℝ) ≤ integerLagMertensSqrtAction (N ^ m) := by
  obtain ⟨B, _hB0, hB⟩ :=
    exists_abs_mobiusDivisorSquareRootAbel_sub_neg_mul_integerLag_add_mertensSqrtAction_linear
  have hscale : ∀ M : ℕ,
      -(M : ℝ) * integerLag M + (3 / 4 : ℝ) * mertensDeviationSqrtAction M =
        (3 / 8 : ℝ) * integerLagMertensSqrtAction M := by
    intro M; unfold integerLagMertensSqrtAction; ring
  rw [riemannHypothesis_iff_mobiusDivisorSquareRootAbel_pow_bddBelow hm]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨(8 / 3 : ℝ) * (-C + B), fun N hN3 => ?_⟩
    have hNm3 : 3 ≤ N ^ m :=
      le_trans hN3 (Nat.le_self_pow (by omega : m ≠ 0) N)
    have hpos : (0 : ℝ) < (N ^ m : ℕ) := by exact_mod_cast (show 0 < N ^ m by omega)
    have h1 := (le_div_iff₀ hpos).mp (hC N (by omega))
    have h2 := hB (N ^ m) hNm3
    rw [hscale (N ^ m)] at h2
    have h2' := (abs_sub_le_iff.mp h2).1
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
      have h2 := hB (N ^ m) hNm3
      rw [hscale (N ^ m)] at h2
      have h2' := (abs_sub_le_iff.mp h2).2
      have hdiv : -((3 / 8 : ℝ) * C + B) ≤
          mobiusDivisorSquareRootAbelMoment (N ^ m) / (N ^ m : ℕ) :=
        (le_div_iff₀ hpos).mpr (by linarith)
      exact (neg_le_neg hM3).trans hdiv

/-! ## Section 3: Prime-Jump-Free Mertens Bound for `lagPrimeChordCharge` and
Super-`√n` Lag Mesh Sampling -/

/-- **Brun–Titchmarsh-Free Mertens Bound for `lagPrimeChordCharge`:**
Keeping `1 / j` inside the sum and using `min (u (j - n)) (v (m - j)) ≤ u * v * (m - n)` for
`u + v = 1` bounds `lagPrimeChordCharge m n m u v` directly by
`u * v * (m - n) * (mertensSum m - mertensSum n)`, improving `lagPrimeChordCharge_le_psi` both by
preserving the `1 / j` weight and by retaining the `u * v ≤ 1 / 4` variance factor. -/
theorem lagPrimeChordCharge_le_mertensSum_sub {n m : ℕ} (hnm : n ≤ m)
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1) :
    lagPrimeChordCharge m n m u v ≤
      u * v * ((m : ℝ) - n) * (mertensSum m - mertensSum n) := by
  classical
  rw [mertensSum_sub_eq hnm, Finset.mul_sum]
  unfold lagPrimeChordCharge
  have hsplit : Finset.Icc 1 m = Finset.Icc 1 n ∪ Finset.Ioc n m := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 n) (Finset.Ioc n m) := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at h1 h2
    omega
  rw [hsplit, Finset.sum_union hdisj]
  have hlow : ∑ j ∈ Finset.Icc 1 n, vonMangoldt j *
      min (u * max (1 - (n : ℝ) / j) 0) (v * max ((m : ℝ) / j - 1) 0) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    have hj' := Finset.mem_Icc.mp hj
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
    have hjn : (j : ℝ) ≤ n := by exact_mod_cast hj'.2
    have h1 : 1 - (n : ℝ) / j ≤ 0 := by
      rw [sub_nonpos, le_div_iff₀ hj0]; linarith
    rw [max_eq_right h1, mul_zero, min_eq_left (by positivity), mul_zero]
  rw [hlow, zero_add]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj' := Finset.mem_Ioc.mp hj
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
  have hnj : (n : ℝ) ≤ j := by exact_mod_cast hj'.1.le
  have hjm : (j : ℝ) ≤ m := by exact_mod_cast hj'.2
  have h1 : 0 ≤ 1 - (n : ℝ) / j := by
    rw [sub_nonneg, div_le_one hj0]; exact hnj
  have h2 : 0 ≤ (m : ℝ) / j - 1 := by
    rw [sub_nonneg, one_le_div hj0]; exact hjm
  have hweight :
      min (u * max (1 - (n : ℝ) / j) 0) (v * max ((m : ℝ) / j - 1) 0) ≤
        u * v * ((m : ℝ) - n) / (j : ℝ) := by
    rw [max_eq_left h1, max_eq_left h2]
    have hmin1 := min_le_left (u * (1 - (n : ℝ) / j)) (v * ((m : ℝ) / j - 1))
    have hmin2 := min_le_right (u * (1 - (n : ℝ) / j)) (v * ((m : ℝ) / j - 1))
    calc
      min (u * (1 - (n : ℝ) / j)) (v * ((m : ℝ) / j - 1)) =
        (v + u) * min (u * (1 - (n : ℝ) / j)) (v * ((m : ℝ) / j - 1)) := by
        rw [add_comm, huv, one_mul]
      _ = v * min (u * (1 - (n : ℝ) / j)) (v * ((m : ℝ) / j - 1)) +
          u * min (u * (1 - (n : ℝ) / j)) (v * ((m : ℝ) / j - 1)) := by ring
      _ ≤ v * (u * (1 - (n : ℝ) / j)) + u * (v * ((m : ℝ) / j - 1)) :=
        add_le_add (mul_le_mul_of_nonneg_left hmin1 hv) (mul_le_mul_of_nonneg_left hmin2 hu)
      _ = u * v * ((m : ℝ) - n) / (j : ℝ) := by
        field_simp [hj0.ne']
        ring
  calc
    vonMangoldt j * min (u * max (1 - (n : ℝ) / j) 0) (v * max ((m : ℝ) / j - 1) 0) ≤
      vonMangoldt j * (u * v * ((m : ℝ) - n) / (j : ℝ)) :=
      mul_le_mul_of_nonneg_left hweight ArithmeticFunction.vonMangoldt_nonneg
    _ = u * v * ((m : ℝ) - n) * (vonMangoldt j / (j : ℝ)) := by ring

/-- Quadratic + Mertens-deviation bound for `mertensSum m - mertensSum n`:
for `1 ≤ n ≤ m`,
`mertensSum m - mertensSum n ≤ (m - n) / n + |mertensSum m - log m + γ| + |mertensSum n - log n + γ|`. -/
theorem mertensSum_sub_le_div_add_mertensDeviation {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    mertensSum m - mertensSum n ≤
      ((m : ℝ) - n) / n +
        |mertensSum m - Real.log (m : ℝ) + Real.eulerMascheroniConstant| +
        |mertensSum n - Real.log (n : ℝ) + Real.eulerMascheroniConstant| := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (hn.trans hnm)
  have hlog : Real.log (m : ℝ) - Real.log (n : ℝ) ≤ ((m : ℝ) - n) / n := by
    rw [← Real.log_div hm0.ne' hn0.ne']
    have h := Real.log_le_sub_one_of_pos (div_pos hm0 hn0)
    have e : (m : ℝ) / n - 1 = ((m : ℝ) - n) / n := by field_simp
    linarith
  have hm_dev := le_abs_self (mertensSum m - Real.log (m : ℝ) + Real.eulerMascheroniConstant)
  have hn_dev := neg_le_abs (mertensSum n - Real.log (n : ℝ) + Real.eulerMascheroniConstant)
  linarith

/-- **Brun–Titchmarsh-Free Lower Chord Interpolation for `integerLag`:**
For `2 ≤ n ≤ k ≤ m` and `k = u * n + v * m` (`u, v ≥ 0`, `u + v = 1`),
`min 0 (min (integerLag n) (integerLag m)) - (u * v * (m - n) * (mertensSum m - mertensSum n) + 1) / √k ≤ integerLag k`. -/
theorem integerLag_ge_endpoint_floor_mertens {n k m : ℕ} (hn : 2 ≤ n) (hnk : n ≤ k) (hkm : k ≤ m)
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1) (hmean : (k : ℝ) = u * n + v * m) :
    min 0 (min (integerLag n) (integerLag m)) -
        (u * v * ((m : ℝ) - n) * (mertensSum m - mertensSum n) + 1) / Real.sqrt k ≤
      integerLag k := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hexact := sqrt_integerLag_chord_exact hn hnk hkm hu hv huv hmean
  have hLD : 0 ≤ u * n * Real.log n + v * m * Real.log m - k * Real.log k := by
    have h := Real.convexOn_mul_log.2 (Set.mem_Ici.mpr (Nat.cast_nonneg n))
      (Set.mem_Ici.mpr (Nat.cast_nonneg m)) hu hv huv
    simp only [smul_eq_mul] at h
    rw [hmean]
    linarith
  have hSD : u * trivialZeroSeriesReal n + v * trivialZeroSeriesReal m - trivialZeroSeriesReal k
      ≤ 1 := by
    have h1 := trivialZeroSeriesReal_le_one hn1
    have h2 := trivialZeroSeriesReal_le_one hm1
    have h3 := trivialZeroSeriesReal_nonneg hk1
    nlinarith
  have hPC := lagPrimeChordCharge_le_mertensSum_sub (hnk.trans hkm) hu hv huv
  set μ := min 0 (min (integerLag n) (integerLag m))
  have hμ0 : μ ≤ 0 := min_le_left _ _
  have hμn : μ ≤ integerLag n := (min_le_right _ _).trans (min_le_left _ _)
  have hμm : μ ≤ integerLag m := (min_le_right _ _).trans (min_le_right _ _)
  have hsn := Real.sqrt_nonneg (n : ℝ)
  have hsm := Real.sqrt_nonneg (m : ℝ)
  have hsk : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hconc : u * Real.sqrt n + v * Real.sqrt m ≤ Real.sqrt k := by
    apply Real.le_sqrt_of_sq_le
    have hnn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (by linarith)
    have hmm : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt (by linarith)
    have hamgm : 2 * (Real.sqrt n * Real.sqrt m) ≤ n + m := by
      nlinarith [sq_nonneg (Real.sqrt n - Real.sqrt m)]
    rw [hmean]
    have hv' : v = 1 - u := by linarith
    subst hv'
    nlinarith [mul_nonneg hu hv]
  have hend : μ * Real.sqrt k ≤
      u * (Real.sqrt n * integerLag n) + v * (Real.sqrt m * integerLag m) := by
    calc μ * Real.sqrt k ≤ μ * (u * Real.sqrt n + v * Real.sqrt m) :=
          mul_le_mul_of_nonpos_left hconc hμ0
      _ = u * (Real.sqrt n * μ) + v * (Real.sqrt m * μ) := by ring
      _ ≤ u * (Real.sqrt n * integerLag n) + v * (Real.sqrt m * integerLag m) :=
          add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hμn hsn) hu)
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hμm hsm) hv)
  have hmain : μ * Real.sqrt k -
      (u * v * ((m : ℝ) - n) * (mertensSum m - mertensSum n) + 1) ≤
        Real.sqrt k * integerLag k := by
    linarith
  have hdiv : μ - (u * v * ((m : ℝ) - n) * (mertensSum m - mertensSum n) + 1) / Real.sqrt k =
      (μ * Real.sqrt k -
        (u * v * ((m : ℝ) - n) * (mertensSum m - mertensSum n) + 1)) / Real.sqrt k := by
    field_simp [hsk.ne']
  rw [hdiv, div_le_iff₀ hsk]
  linarith

/-- **Upper Bounds Transfer Along Super-`√n` Meshes (`O(√k * exp(c * √(log k)))` gaps):**
If `c > 0` and `C ≥ 0` witness the exponentially damped Lipschitz bound
`|integerLag n - integerLag k| ≤ C * ((n - k) / √k) * exp(-c * √(log k)) + 2 / √k`,
then any set `A` that samples `[k, n]` with `(n - k) / √k ≤ K * exp(c * √(log k))` transfers upper
bounds on `A` to all of `ℕ_{\ge 2}`. -/
theorem integerLag_le_of_exp_sqrt_log_samples {A : Set ℕ} {M K c C : ℝ} {N₁ : ℕ}
    (hC : 0 ≤ C)
    (hlip : ∀ {k n : ℕ}, 2 ≤ k → k ≤ n → n ≤ 2 * k →
      |integerLag n - integerLag k| ≤
        C * (((n - k : ℕ) : ℝ) / Real.sqrt (k : ℝ)) *
          Real.exp (-c * Real.sqrt (Real.log (k : ℝ))) + 2 / Real.sqrt (k : ℝ))
    (hA : ∀ k ∈ A, 2 ≤ k → integerLag k ≤ M)
    (hdense : ∀ n : ℕ, N₁ ≤ n → ∃ k ∈ A, 2 ≤ k ∧ k ≤ n ∧ n ≤ 2 * k ∧
      ((n - k : ℕ) : ℝ) / Real.sqrt (k : ℝ) ≤ K * Real.exp (c * Real.sqrt (Real.log (k : ℝ)))) :
    ∃ M' : ℝ, ∀ n : ℕ, 2 ≤ n → integerLag n ≤ M' := by
  classical
  set B : ℝ := (Finset.range (N₁ + 2)).sup' ⟨0, by simp⟩ fun n => integerLag n
  refine ⟨max B (M + C * K + 2), fun n hn => ?_⟩
  rcases lt_or_ge n N₁ with hlt | hge
  · exact le_max_of_le_left (Finset.le_sup' (fun n => integerLag n)
      (Finset.mem_range.mpr (by omega)))
  · refine le_max_of_le_right ?_
    obtain ⟨k, hkA, hk2, hkn, hn2k, hgap⟩ := hdense n hge
    have hd := (abs_le.mp (hlip hk2 hkn hn2k)).2
    have hsk1 : (1 : ℝ) ≤ Real.sqrt (k : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ k by omega))
    have hdiv2 : 2 / Real.sqrt (k : ℝ) ≤ 2 := div_le_self (by norm_num) hsk1
    have hexp_cancel :
        K * Real.exp (c * Real.sqrt (Real.log (k : ℝ))) *
          Real.exp (-c * Real.sqrt (Real.log (k : ℝ))) = K := by
      rw [mul_assoc, ← Real.exp_add]
      have h0 : c * Real.sqrt (Real.log (k : ℝ)) + -c * Real.sqrt (Real.log (k : ℝ)) = 0 := by ring
      rw [h0, Real.exp_zero, mul_one]
    have hterm :
        C * (((n - k : ℕ) : ℝ) / Real.sqrt (k : ℝ)) *
          Real.exp (-c * Real.sqrt (Real.log (k : ℝ))) ≤ C * K := by
      calc
        C * (((n - k : ℕ) : ℝ) / Real.sqrt (k : ℝ)) *
            Real.exp (-c * Real.sqrt (Real.log (k : ℝ))) ≤
          C * (K * Real.exp (c * Real.sqrt (Real.log (k : ℝ)))) *
            Real.exp (-c * Real.sqrt (Real.log (k : ℝ))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgap hC) (Real.exp_pos _).le
        _ = C * (K * Real.exp (c * Real.sqrt (Real.log (k : ℝ))) *
            Real.exp (-c * Real.sqrt (Real.log (k : ℝ)))) := by ring
        _ = C * K := by rw [hexp_cancel]
    have hkM := hA k hkA hk2
    linarith

/-- **Lower Bounds Transfer Along Super-`√n` Meshes (`O(√k * exp(c * √(log k)))` gaps).** -/
theorem le_integerLag_of_exp_sqrt_log_samples {A : Set ℕ} {M K c C : ℝ} {N₁ : ℕ}
    (hC : 0 ≤ C)
    (hlip : ∀ {k n : ℕ}, 2 ≤ k → k ≤ n → n ≤ 2 * k →
      |integerLag n - integerLag k| ≤
        C * (((n - k : ℕ) : ℝ) / Real.sqrt (k : ℝ)) *
          Real.exp (-c * Real.sqrt (Real.log (k : ℝ))) + 2 / Real.sqrt (k : ℝ))
    (hA : ∀ k ∈ A, 2 ≤ k → M ≤ integerLag k)
    (hdense : ∀ n : ℕ, N₁ ≤ n → ∃ k ∈ A, 2 ≤ k ∧ k ≤ n ∧ n ≤ 2 * k ∧
      ((n - k : ℕ) : ℝ) / Real.sqrt (k : ℝ) ≤ K * Real.exp (c * Real.sqrt (Real.log (k : ℝ)))) :
    ∃ M' : ℝ, ∀ n : ℕ, 2 ≤ n → M' ≤ integerLag n := by
  classical
  set B : ℝ := (Finset.range (N₁ + 2)).inf' ⟨0, by simp⟩ fun n => integerLag n
  refine ⟨min B (M - C * K - 2), fun n hn => ?_⟩
  rcases lt_or_ge n N₁ with hlt | hge
  · exact min_le_of_left_le (Finset.inf'_le (fun n => integerLag n)
      (Finset.mem_range.mpr (by omega)))
  · refine min_le_of_right_le ?_
    obtain ⟨k, hkA, hk2, hkn, hn2k, hgap⟩ := hdense n hge
    have hd := (abs_le.mp (hlip hk2 hkn hn2k)).1
    have hsk1 : (1 : ℝ) ≤ Real.sqrt (k : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ k by omega))
    have hdiv2 : 2 / Real.sqrt (k : ℝ) ≤ 2 := div_le_self (by norm_num) hsk1
    have hexp_cancel :
        K * Real.exp (c * Real.sqrt (Real.log (k : ℝ))) *
          Real.exp (-c * Real.sqrt (Real.log (k : ℝ))) = K := by
      rw [mul_assoc, ← Real.exp_add]
      have h0 : c * Real.sqrt (Real.log (k : ℝ)) + -c * Real.sqrt (Real.log (k : ℝ)) = 0 := by ring
      rw [h0, Real.exp_zero, mul_one]
    have hterm :
        C * (((n - k : ℕ) : ℝ) / Real.sqrt (k : ℝ)) *
          Real.exp (-c * Real.sqrt (Real.log (k : ℝ))) ≤ C * K := by
      calc
        C * (((n - k : ℕ) : ℝ) / Real.sqrt (k : ℝ)) *
            Real.exp (-c * Real.sqrt (Real.log (k : ℝ))) ≤
          C * (K * Real.exp (c * Real.sqrt (Real.log (k : ℝ)))) *
            Real.exp (-c * Real.sqrt (Real.log (k : ℝ))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgap hC) (Real.exp_pos _).le
        _ = C * (K * Real.exp (c * Real.sqrt (Real.log (k : ℝ))) *
            Real.exp (-c * Real.sqrt (Real.log (k : ℝ)))) := by ring
        _ = C * K := by rw [hexp_cancel]
    have hkM := hA k hkA hk2
    linarith

/-- **Unconditional Super-`√n` Mesh Sampling Theorem for RH:**
There exists an unconditional constant `c > 0` such that for any sampling set `A ⊆ ℕ` meeting
every super-`√n` window `(n - k) / √k ≤ K * exp(c * √(log k))` (`2 ≤ k ≤ n ≤ 2k`) for `n ≥ N₁`,
the Riemann Hypothesis is equivalent both to `integerLag` being bounded above on `A` and to
`integerLag` being bounded below on `A`. -/
theorem exists_exp_sqrt_log_mesh_riemannHypothesis_criteria :
    ∃ c > 0, ∀ (A : Set ℕ) (K : ℝ) (N₁ : ℕ),
      (∀ n : ℕ, N₁ ≤ n → ∃ k ∈ A, 2 ≤ k ∧ k ≤ n ∧ n ≤ 2 * k ∧
        ((n - k : ℕ) : ℝ) / Real.sqrt (k : ℝ) ≤
          K * Real.exp (c * Real.sqrt (Real.log (k : ℝ)))) →
      ((RiemannHypothesis ↔ ∃ M : ℝ, ∀ k ∈ A, 2 ≤ k → integerLag k ≤ M) ∧
        (RiemannHypothesis ↔ ∃ M : ℝ, ∀ k ∈ A, 2 ≤ k → M ≤ integerLag k)) := by
  obtain ⟨c, hc0, C, hC0, hlip⟩ := exists_exponentially_damped_integerLag_lipschitz
  refine ⟨c, hc0, fun A K N₁ hdense => ⟨?_, ?_⟩⟩
  · constructor
    · intro hRH
      obtain ⟨M, hM⟩ := riemannHypothesis_iff_integerLag_bddAbove.mp hRH
      exact ⟨M, fun k _ hk => hM k hk⟩
    · rintro ⟨M, hM⟩
      exact riemannHypothesis_iff_integerLag_bddAbove.mpr
        (integerLag_le_of_exp_sqrt_log_samples hC0 (fun hk2 hkn hn2k => (hlip hk2 hkn hn2k).2)
          hM hdense)
  · constructor
    · intro hRH
      obtain ⟨M, hM⟩ := riemannHypothesis_iff_integerLag_bddBelow.mp hRH
      exact ⟨M, fun k _ hk => hM k hk⟩
    · rintro ⟨M, hM⟩
      exact riemannHypothesis_iff_integerLag_bddBelow.mpr
        (le_integerLag_of_exp_sqrt_log_samples hC0 (fun hk2 hkn hn2k => (hlip hk2 hkn hn2k).2)
          hM hdense)

end

end GaloisForLFunctions.RHTower
