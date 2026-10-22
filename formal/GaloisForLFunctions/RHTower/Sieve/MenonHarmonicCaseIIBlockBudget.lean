import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicCaseIIBlockBounds

/-!
# Size of the Case II Perron budget for one prime block

The Case II Perron budget of a prime block `(a, Y]` is
`P · C · (π - 2 arctan(cells/2)) + 2 · cells · C · (log a)^{-300}`, where `P` is the Heath-Brown
fixed polylogarithmic bound, `C` the wide-interval kernel majorant and
`cells = ceil((log a)^{200})`. Combining `P ≤ K_P (log a)^{134}`, `C ≤ K(C0) a (log a)^{40}` and the
arctan tail `≤ 4/cells`, this module shows that the budget is `O(a/(log a)^{20})` with an explicit
constant.

## Main results

- `menonHarmonicCaseIIBudgetConstant`: the constant `4 K_P K(C0) + 4 K(C0)`.
- `menonHarmonicCaseIIBudget_le`: for `C0 ≥ 0`, `a ≥ 64`, `log a ≥ 1` and `a < Y ≤ 2a`, the budget
  is at most `menonHarmonicCaseIIBudgetConstant C0 · a / (log a)^{20}`.

## Hypotheses

The result is unconditional, under the stated ranges `C0 ≥ 0`, `64 ≤ a`, `1 ≤ log a`,
`a < Y ≤ 2a`.
-/

namespace RHTower.Sieve

noncomputable section

/-- Budget constant `4 K_P K(C0) + 4 K(C0)` from the fixed polylog and kernel constants. -/
def menonHarmonicCaseIIBudgetConstant (C0 : ℝ) : ℝ :=
  4 * menonHarmonicCaseIIFixedPolylogConstant *
      menonHarmonicCaseIIKernelConstant C0 +
    4 * menonHarmonicCaseIIKernelConstant C0

/-- For `C0 ≥ 0`, `a ≥ 64`, `log a ≥ 1` and `a < Y ≤ 2a`, the Case II Perron budget is at most
`menonHarmonicCaseIIBudgetConstant C0 · a / (log a)^{20}`. -/
theorem menonHarmonicCaseIIBudget_le
    {C0 : ℝ} (hC0 : 0 ≤ C0) {a Y : ℕ} (ha64 : 64 ≤ a)
    (hlog : 1 ≤ Real.log (a : ℝ)) (haY : a < Y) (hYa : Y ≤ 2 * a) :
    menonHarmonicCaseIIBudget C0 a Y ≤
      menonHarmonicCaseIIBudgetConstant C0 * (a : ℝ) /
        (Real.log (a : ℝ)) ^ (20 : ℕ) := by
  let la : ℝ := Real.log (a : ℝ)
  let cells := menonHarmonicCaseIICells a
  let C := menonWideIntervalAmbientKernelMajorant C0 (4 * Y)
    (menonHarmonicCaseIISmoothingWidth a) (menonHarmonicCaseIISigma Y)
  let P := heathBrownWindowRelevantFixedPolylogBound a (4 * Y) 3 (a : ℝ)
    (menonHarmonicCaseIISigma Y)
  have ha : 1 < a := by omega
  have hla0 : 0 < la := by dsimp only [la]; linarith
  have hcells := menonHarmonicCaseIICells_cast_bounds hlog
  have hcells0 : (0 : ℝ) < (cells : ℝ) := by
    exact_mod_cast menonHarmonicCaseIICells_pos ha
  have hC : C ≤ menonHarmonicCaseIIKernelConstant C0 * (a : ℝ) * la ^ (40 : ℕ) := by
    simpa only [C, la] using
      menonWideIntervalAmbientKernelMajorant_caseII_le hC0 ha hlog haY hYa
  have hC0' : 0 ≤ C := (menonWideIntervalAmbientKernelMajorant_pos hC0
    (menonHarmonicCaseIISmoothingWidth_pos ha)
    (zero_lt_one.trans (menonHarmonicCaseIISigma_gt_one (Nat.zero_lt_of_lt haY)))).le
  have hK0 : 0 ≤ menonHarmonicCaseIIKernelConstant C0 := by
    rw [menonHarmonicCaseIIKernelConstant]
    positivity
  have hKP0 : 0 ≤ menonHarmonicCaseIIFixedPolylogConstant := by
    rw [menonHarmonicCaseIIFixedPolylogConstant]
    positivity
  have hP : P ≤ menonHarmonicCaseIIFixedPolylogConstant * la ^ (134 : ℕ) := by
    simpa only [P, la] using
      heathBrownWindowRelevantFixedPolylogBound_caseII_le ha64 hlog haY hYa
  have hP0 : 0 ≤ P := by
    dsimp only [P]
    exact heathBrownWindowRelevantFixedPolylogBound_nonneg (by positivity)
  have htail := menonHarmonicCaseII_arctanTail_le (a := a) ha
  have htail0 : 0 ≤ Real.pi - 2 * Real.arctan ((cells : ℝ) / 2) := by
    have := Real.arctan_lt_pi_div_two ((cells : ℝ) / 2)
    linarith
  have hterm1 : P * C *
        (Real.pi - 2 * Real.arctan ((cells : ℝ) / 2)) ≤
      4 * menonHarmonicCaseIIFixedPolylogConstant *
        menonHarmonicCaseIIKernelConstant C0 * (a : ℝ) /
          la ^ (26 : ℕ) := by
    have hupper0 : 0 ≤
        (menonHarmonicCaseIIFixedPolylogConstant * la ^ (134 : ℕ)) *
          (menonHarmonicCaseIIKernelConstant C0 * (a : ℝ) * la ^ (40 : ℕ)) := by
      positivity
    have hinv : 4 / (cells : ℝ) ≤ 4 / la ^ (200 : ℕ) := by
      gcongr
      simpa only [cells, la] using hcells.1
    calc
      P * C * (Real.pi - 2 * Real.arctan ((cells : ℝ) / 2)) ≤
          (menonHarmonicCaseIIFixedPolylogConstant * la ^ (134 : ℕ)) *
            (menonHarmonicCaseIIKernelConstant C0 * (a : ℝ) * la ^ (40 : ℕ)) *
              (4 / (cells : ℝ)) := by gcongr
      _ ≤ (menonHarmonicCaseIIFixedPolylogConstant * la ^ (134 : ℕ)) *
            (menonHarmonicCaseIIKernelConstant C0 * (a : ℝ) * la ^ (40 : ℕ)) *
              (4 / la ^ (200 : ℕ)) := mul_le_mul_of_nonneg_left hinv hupper0
      _ = 4 * menonHarmonicCaseIIFixedPolylogConstant *
            menonHarmonicCaseIIKernelConstant C0 * (a : ℝ) /
              la ^ (26 : ℕ) := by
        field_simp [ne_of_gt hla0]
  have hterm1' : P * C *
        (Real.pi - 2 * Real.arctan ((cells : ℝ) / 2)) ≤
      4 * menonHarmonicCaseIIFixedPolylogConstant *
        menonHarmonicCaseIIKernelConstant C0 * (a : ℝ) /
          la ^ (20 : ℕ) := by
    refine hterm1.trans ?_
    have hpow : la ^ (20 : ℕ) ≤ la ^ (26 : ℕ) :=
      pow_le_pow_right₀ hlog (by norm_num)
    exact div_le_div_of_nonneg_left (by positivity [hKP0, hK0]) (pow_pos hla0 20) hpow
  have hrpow : la ^ (-300 : ℝ) = 1 / la ^ (300 : ℕ) := by
    rw [Real.rpow_neg hla0.le]
    rw [show la ^ (300 : ℝ) = la ^ (300 : ℕ) by
      simpa only [Nat.cast_ofNat] using Real.rpow_natCast la 300]
    simp only [one_div]
  have hterm2 : 2 * (cells : ℝ) * C * la ^ (-300 : ℝ) ≤
      4 * menonHarmonicCaseIIKernelConstant C0 * (a : ℝ) /
        la ^ (60 : ℕ) := by
    rw [hrpow]
    calc
      2 * (cells : ℝ) * C * (1 / la ^ (300 : ℕ)) ≤
          2 * (2 * la ^ (200 : ℕ)) *
            (menonHarmonicCaseIIKernelConstant C0 * (a : ℝ) * la ^ (40 : ℕ)) *
              (1 / la ^ (300 : ℕ)) := by
        gcongr
        simpa only [cells, la] using hcells.2
      _ = 4 * menonHarmonicCaseIIKernelConstant C0 * (a : ℝ) /
          la ^ (60 : ℕ) := by
        field_simp [ne_of_gt hla0]
        ring
  have hterm2' : 2 * (cells : ℝ) * C * la ^ (-300 : ℝ) ≤
      4 * menonHarmonicCaseIIKernelConstant C0 * (a : ℝ) /
        la ^ (20 : ℕ) := by
    refine hterm2.trans ?_
    have hpow : la ^ (20 : ℕ) ≤ la ^ (60 : ℕ) :=
      pow_le_pow_right₀ hlog (by norm_num)
    exact div_le_div_of_nonneg_left (by positivity [hK0]) (pow_pos hla0 20) hpow
  rw [menonHarmonicCaseIIBudget]
  change P * C * (Real.pi - 2 * Real.arctan ((cells : ℝ) / 2)) +
      2 * (cells : ℝ) * C * la ^ (-300 : ℝ) ≤ _
  rw [menonHarmonicCaseIIBudgetConstant]
  calc
    P * C * (Real.pi - 2 * Real.arctan ((cells : ℝ) / 2)) +
        2 * (cells : ℝ) * C * la ^ (-300 : ℝ) ≤
      4 * menonHarmonicCaseIIFixedPolylogConstant *
          menonHarmonicCaseIIKernelConstant C0 * (a : ℝ) / la ^ (20 : ℕ) +
        4 * menonHarmonicCaseIIKernelConstant C0 * (a : ℝ) / la ^ (20 : ℕ) :=
      add_le_add hterm1' hterm2'
    _ = (4 * menonHarmonicCaseIIFixedPolylogConstant *
          menonHarmonicCaseIIKernelConstant C0 +
        4 * menonHarmonicCaseIIKernelConstant C0) * (a : ℝ) / la ^ (20 : ℕ) := by ring

end

end RHTower.Sieve
