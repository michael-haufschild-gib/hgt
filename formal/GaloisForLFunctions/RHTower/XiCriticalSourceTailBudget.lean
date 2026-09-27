import GaloisForLFunctions.RHTower.XiCriticalResidualSourceImprovement

/-!
# Quantitative capacity of the high critical source

Above squared heat height `R`, the complete critical fourth-trace reserve is
at most the zeroth arithmetic source divided by `R`. This controls all high
critical copies at once, not only a selected Hardy pair. The low shell is a
finite actual divisor set; its critical reserve approximates the total
critical reserve with this explicit error.
-/

open scoped Real BigOperators
open Complex
noncomputable section

namespace RHTower

def xiCriticalFourthTraceTailAtom (R : ℝ) (q : XiZeroCopy) : ℝ :=
  if R < (xiSpectralPoint q ^ 2).re then xiFourthTraceCriticalAtom q else 0

def xiCriticalFourthTraceTail (R : ℝ) : ℝ :=
  ∑' q : XiZeroCopy, xiCriticalFourthTraceTailAtom R q

/-- The finite actual heat shell; only its critical copies contribute to the reserve. -/
def xiCriticalSourceShell (R : ℝ) : Finset XiZeroCopy :=
  (finite_xiHeatShell R).toFinset

theorem xiCriticalFourthTraceTailAtom_nonneg (R : ℝ) (q : XiZeroCopy) :
    0 ≤ xiCriticalFourthTraceTailAtom R q := by
  unfold xiCriticalFourthTraceTailAtom
  split_ifs
  · exact xiFourthTraceCriticalAtom_nonneg q
  · exact le_rfl

theorem summable_xiCriticalFourthTraceTailAtom (R : ℝ) :
    Summable (xiCriticalFourthTraceTailAtom R) := by
  apply Summable.of_nonneg_of_le (xiCriticalFourthTraceTailAtom_nonneg R)
    (fun q => ?_) summable_xiFourthTraceCriticalAtom
  unfold xiCriticalFourthTraceTailAtom
  split_ifs
  · exact le_rfl
  · exact xiFourthTraceCriticalAtom_nonneg q

/-- A critical atom above `R` spends at most `1/R` times its positive first-trace mass. -/
theorem xiCriticalFourthTraceTailAtom_le_firstSource
    (R : {R : ℝ // 0 < R}) (q : XiZeroCopy) :
    xiCriticalFourthTraceTailAtom R q ≤ xiThermalNode q / (R : ℝ) := by
  unfold xiCriticalFourthTraceTailAtom
  split_ifs with hhigh
  · by_cases hreal : (xiSpectralPoint q).im = 0
    · let x := (xiSpectralPoint q).re
      have hx : xiSpectralPoint q = (x : ℂ) := by
        apply Complex.ext
        · rfl
        · simpa only [Complex.ofReal_im] using hreal
      have hx0 : x ≠ 0 := by
        intro h
        apply xiSpectralPoint_ne_zero q
        rw [hx, h, Complex.ofReal_zero]
      have hR : (R : ℝ) < x ^ 2 := by
        simpa only [hx, ← Complex.ofReal_pow, Complex.ofReal_re] using hhigh
      have hnode : xiThermalNode q = 1 / x ^ 2 := by
        rw [xiThermalNode, xiZeroCopyReciprocalSquare, hx]
        simp only [← Complex.ofReal_inv, ← Complex.ofReal_pow, Complex.ofReal_re,
          inv_pow, one_div]
      rw [xiFourthTraceCriticalAtom_at_real x ⟨q, hx⟩, hnode]
      apply (le_div_iff₀ R.property).mpr
      calc
        (1 / x ^ 4) * (R : ℝ) ≤ (1 / x ^ 4) * x ^ 2 :=
          mul_le_mul_of_nonneg_left hR.le (by positivity)
        _ = 1 / x ^ 2 := by field_simp
    · rw [xiFourthTraceCriticalAtom, if_neg hreal]
      exact div_nonneg (xiThermalNode_pos q).le R.property.le
  · exact div_nonneg (xiThermalNode_pos q).le R.property.le

theorem xiCriticalFourthTraceTail_nonneg (R : ℝ) :
    0 ≤ xiCriticalFourthTraceTail R :=
  tsum_nonneg (xiCriticalFourthTraceTailAtom_nonneg R)

/-- The entire high critical source has an arithmetic `1/R` capacity bound. -/
theorem xiCriticalFourthTraceTail_le_firstSource (R : {R : ℝ // 0 < R}) :
    xiCriticalFourthTraceTail R ≤ normalizedPrimeArchMoment 0 / (R : ℝ) := by
  have hs : Summable xiThermalNode := by
    simpa only [zero_add, pow_one] using summable_xiThermalNode_pow 0
  have hm : (∑' q : XiZeroCopy, xiThermalNode q) = normalizedPrimeArchMoment 0 := by
    simpa only [xiThermalPositiveMoment, zero_add, pow_one] using
      xiThermalPositiveMoment_zero_eq_source
  have h := (summable_xiCriticalFourthTraceTailAtom R).tsum_le_tsum
    (xiCriticalFourthTraceTailAtom_le_firstSource R) (hs.div_const (R : ℝ))
  simpa only [xiCriticalFourthTraceTail, tsum_div_const, hm] using h

/-- Every finite high selection obeys the same bound, independently of its size. -/
theorem xiCriticalFourthTraceReserve_high_le_firstSource
    (R : {R : ℝ // 0 < R}) (E : Finset XiZeroCopy) :
    xiCriticalFourthTraceReserve
      (E.filter (fun q => (R : ℝ) < (xiSpectralPoint q ^ 2).re)) ≤
        normalizedPrimeArchMoment 0 / (R : ℝ) := by
  classical
  have h := (summable_xiCriticalFourthTraceTailAtom R).sum_le_tsum E
    (fun q _ => xiCriticalFourthTraceTailAtom_nonneg R q)
  have he : (∑ q ∈ E, xiCriticalFourthTraceTailAtom R q) =
      xiCriticalFourthTraceReserve (E.filter (fun q => (R : ℝ) < (xiSpectralPoint q ^ 2).re)) := by
    simp only [xiCriticalFourthTraceTailAtom, xiCriticalFourthTraceReserve, Finset.sum_filter]
  rw [he] at h
  exact h.trans (xiCriticalFourthTraceTail_le_firstSource R)

/-- The finite low reserve and complete high critical tail account for every critical copy. -/
theorem xiCriticalFourthTraceReserve_shell_add_tail (R : ℝ) :
    xiCriticalFourthTraceReserve (xiCriticalSourceShell R) + xiCriticalFourthTraceTail R =
      ∑' q : XiZeroCopy, xiFourthTraceCriticalAtom q := by
  classical
  have h := summable_xiFourthTraceCriticalAtom.sum_add_tsum_compl
    (s := xiCriticalSourceShell R)
  have he : (∑' q : ↑((↑(xiCriticalSourceShell R) : Set XiZeroCopy)ᶜ),
      xiFourthTraceCriticalAtom q.1) = xiCriticalFourthTraceTail R := by
    rw [tsum_subtype]
    apply tsum_congr
    intro q
    simp only [Set.indicator_apply, Set.mem_compl_iff, Finset.mem_coe, xiCriticalSourceShell,
      Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_le,
      xiCriticalFourthTraceTailAtom]
  simpa only [xiCriticalFourthTraceReserve, he] using h

/-- The remaining source equals the whole off-critical mass plus a quantitatively small
critical tail. No off-critical zero is presumed absent. -/
theorem xiCriticalFourthTraceResidual_shell_eq_off_add_tail (R : ℝ) :
    xiCriticalFourthTraceResidual (xiCriticalSourceShell R) =
      (∑' q : XiZeroCopy, xiFourthTraceOffAtom q) + xiCriticalFourthTraceTail R := by
  have h := xiCriticalFourthTraceReserve_shell_add_tail R
  have he := tsum_xiFourthTraceCritical_add_off_eq_source
  unfold xiCriticalFourthTraceResidual
  linarith only [h, he]

/-- An explicit approximation error for the finite critical-source subtraction. -/
theorem xiCriticalFourthTraceResidual_shell_error (R : {R : ℝ // 0 < R}) :
    0 ≤ xiCriticalFourthTraceResidual (xiCriticalSourceShell R) -
      (∑' q : XiZeroCopy, xiFourthTraceOffAtom q) ∧
    xiCriticalFourthTraceResidual (xiCriticalSourceShell R) -
      (∑' q : XiZeroCopy, xiFourthTraceOffAtom q) ≤
        normalizedPrimeArchMoment 0 / (R : ℝ) := by
  rw [xiCriticalFourthTraceResidual_shell_eq_off_add_tail, add_sub_cancel_left]
  exact ⟨xiCriticalFourthTraceTail_nonneg R, xiCriticalFourthTraceTail_le_firstSource R⟩

end RHTower
