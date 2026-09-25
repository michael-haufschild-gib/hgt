import GaloisForLFunctions.RHTower.MobiusDivisorCriticalPrimeAbelMellinFactorization
import GaloisForLFunctions.RHTower.MobiusDivisorAdaptiveTerminalCriticalSource

/-!
# First-omission source law for arbitrary terminal cores

When every unprocessed active prime has quotient at most two, its exact critical Abel
child is a positive first-cell displacement. The terminal head is therefore the
completed source plus one explicit, nonnegative sum. This is the finite source
identity behind the paper first-omission old-cutoff obstruction; it does not by
itself give an asymptotic prime count, an all-history payment, or RH.
-/

noncomputable section
open Complex Finset
namespace RHTower

private theorem psiDefect_one_local :
    psiDefect 1 = 2 * Real.eulerMascheroniConstant - 1 := by
  simp [psiDefect, chebyshevPsi]
  ring

/-- The literal critical Abel source on its first quotient cell. -/
theorem criticalContinuousAbel_unit_cell
    {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 2) :
    criticalContinuousAbel x =
      (Real.sqrt x - 1) * (2 * Real.eulerMascheroniConstant - 1) := by
  have hbetween := squareRootSummatoryPrimitive_between criticalSourceCoeff
    (k := 1) (by omega)
    (show ((1 : ℕ) : ℝ) ≤ x by simpa using hx1)
    (show x ≤ (((1 : ℕ) + 1 : ℕ) : ℝ) by simpa using hx2)
  have hzero := criticalContinuousAbel_eq_zero_le_one (x := 1) le_rfl
  have hsum := criticalSourceCoeff_cumulative 1 (by omega)
  rw [criticalContinuousAbel] at hzero ⊢
  rw [hbetween, hsum] at ⊢
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, Nat.cast_one,
    Real.sqrt_one] at ⊢
  rw [hzero, psiDefect_one_local]
  ring

/-- Exact first-cell head for any terminal core, with no prime-prefix assumption. -/
theorem adaptive_terminal_head_first_cell
    (M : ℕ) (P : Finset ℕ)
    (hM : 1 ≤ M)
    (hcover : ∀ p ∈ mobiusDivisorSelectionPrimes M, p * p ≤ M → p ∈ P)
    (hcell : ∀ p ∈ mobiusDivisorSelectionPrimes M \ P, M ≤ 2 * p) :
    mobiusDivisorSelectionFibre M P ∅ =
      criticalContinuousAbel (M : ℝ) +
        (2 * Real.eulerMascheroniConstant - 1) *
          ∑ p ∈ mobiusDivisorSelectionPrimes M \ P,
            (Real.sqrt (M : ℝ) - Real.sqrt (p : ℝ)) := by
  rw [adaptive_terminal_head_source M P hcover,
    ← criticalContinuousAbel_nat_eq_dilation_sum M hM]
  rw [mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  have hpp : p.Prime := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2
  have hpM : p < M := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).1
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hq1 : (1 : ℝ) ≤ (M : ℝ) / p := by
    apply (le_div_iff₀ hp0).mpr
    simpa using (show (p : ℝ) ≤ (M : ℝ) by exact_mod_cast hpM.le)
  have hq2 : (M : ℝ) / p ≤ 2 := by
    apply (div_le_iff₀ hp0).mpr
    exact_mod_cast hcell p hp
  have hmul : Real.sqrt (p : ℝ) * Real.sqrt ((M : ℝ) / p) = Real.sqrt (M : ℝ) := by
    rw [← Real.sqrt_mul (le_of_lt hp0)]
    congr 1
    field_simp
  rw [criticalContinuousAbel_unit_cell hq1 hq2]
  calc
    _ = (Real.sqrt (p : ℝ) * Real.sqrt ((M : ℝ) / p) - Real.sqrt (p : ℝ)) *
          (2 * Real.eulerMascheroniConstant - 1) := by ring
    _ = _ := by rw [hmul]; ring

end RHTower
