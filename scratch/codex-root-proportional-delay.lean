import GaloisForLFunctions.RHTower.MobiusDivisorCriticalPrimeAbelMellinFactorization
import GaloisForLFunctions.RHTower.MobiusDivisorAdaptiveTerminalCriticalSource

noncomputable section
open Complex Finset
namespace RHTower

private theorem psiDefect_one_local :
    psiDefect 1 = 2 * Real.eulerMascheroniConstant - 1 := by
  simp [psiDefect, chebyshevPsi]
  ring

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

theorem criticalContinuousAbel_pos_unit_cell
    {x : ℝ} (hx1 : 1 < x) (hx2 : x ≤ 2) :
    0 < criticalContinuousAbel x := by
  rw [criticalContinuousAbel_unit_cell hx1.le hx2]
  have hroot : 1 < Real.sqrt x := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) hx1
  have hgamma : 0 < 2 * Real.eulerMascheroniConstant - 1 := by
    have h := Real.one_half_lt_eulerMascheroniConstant
    linarith
  exact mul_pos (sub_pos.mpr hroot) hgamma

/-- Literal fixed-ratio admission front, used only as a diagnostic candidate. -/
def proportionalAdmissionCore (c : ℝ) (M : ℕ) : Finset ℕ :=
  (mobiusDivisorSelectionPrimes M).filter
    (fun p => c * (p : ℝ) ≤ (M : ℝ))

theorem proportionalAdmissionCore_terminal
    (c : ℝ) (M : ℕ) (hM : c ^ (2 : ℕ) ≤ (M : ℝ)) :
    ∀ p ∈ mobiusDivisorSelectionPrimes M,
      p * p ≤ M → p ∈ proportionalAdmissionCore c M := by
  intro p hp hpp
  have hp2 : (p : ℝ) * (p : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast hpp
  have hcp : c * (p : ℝ) ≤ (M : ℝ) := by
    nlinarith [sq_nonneg (c - (p : ℝ))]
  exact Finset.mem_filter.mpr ⟨hp, hcp⟩

theorem proportionalAdmissionCore_head_source
    (c : ℝ) (M : ℕ) (hM : 1 ≤ M)
    (hMc : c ^ (2 : ℕ) ≤ (M : ℝ)) :
    mobiusDivisorSelectionFibre M (proportionalAdmissionCore c M) ∅ =
      criticalContinuousAbel (M : ℝ) +
        ∑ p ∈ (mobiusDivisorSelectionPrimes M).filter
          (fun p : ℕ => (M : ℝ) < c * (p : ℝ)),
          Real.sqrt (p : ℝ) * criticalContinuousAbel ((M : ℝ) / (p : ℝ)) := by
  have hbase := adaptive_terminal_head_source M
    (proportionalAdmissionCore c M)
    (proportionalAdmissionCore_terminal c M hMc)
  have hset : mobiusDivisorSelectionPrimes M \ proportionalAdmissionCore c M =
      (mobiusDivisorSelectionPrimes M).filter
        (fun p : ℕ => (M : ℝ) < c * (p : ℝ)) := by
    ext p
    by_cases hpM : p ∈ mobiusDivisorSelectionPrimes M
    · simp [Finset.mem_sdiff, Finset.mem_filter,
        proportionalAdmissionCore, hpM, not_le]
    · simp [Finset.mem_sdiff, Finset.mem_filter,
        proportionalAdmissionCore, hpM]
  rw [hset, ← criticalContinuousAbel_nat_eq_dilation_sum M hM] at hbase
  exact hbase

end RHTower
