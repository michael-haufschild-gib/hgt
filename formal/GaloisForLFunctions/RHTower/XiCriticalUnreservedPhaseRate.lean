import GaloisForLFunctions.RHTower.XiCriticalResidualSourceImprovement

/-!
# An omitted critical copy limits the half-time decay rate

The exact residual source still pays for every critical copy outside the
finite reserve. Its reciprocal fourth-power charge forces the adaptive gap
below twice that copy's squared ordinate. This constrains the explicit
phase ceiling, without asserting a negative actual Hankel value.
-/

open scoped Real BigOperators
open Complex
noncomputable section

namespace RHTower

theorem xiFourthTraceCriticalAtom_le_residual_unreserved (F : Finset XiZeroCopy)
    (q : {q : XiZeroCopy // q ∉ F}) :
    xiFourthTraceCriticalAtom q.1 ≤ xiCriticalFourthTraceResidual F := by
  have h := xiCriticalFourthTraceResidual_nonneg (insert q.1 F)
  unfold xiCriticalFourthTraceResidual xiCriticalFourthTraceReserve at *
  rw [Finset.sum_insert q.property] at h
  linarith only [h]

/-- Source subtraction must capture a selected copy to escape this rate obstruction. -/
theorem xiCriticalResidualPhaseGap_lt_twice_unreserved_sq (F : Finset XiZeroCopy)
    (q : {q : XiZeroCopy // q ∉ F ∧ (xiSpectralPoint q).im = 0}) :
    xiCriticalResidualPhaseGap F < 2 * (xiSpectralPoint q.1).re ^ 2 := by
  let γ := (xiSpectralPoint q.1).re
  have hreal : xiSpectralPoint q.1 = (γ : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using q.property.2
  have hγ : 0 < γ ^ 2 :=
    (by positivity : (0 : ℝ) < 32).trans (xiSpectral_re_sq_gt_thirtytwo q.1)
  have hγ4 : 0 < γ ^ 4 := by nlinarith only [sq_pos_of_pos hγ]
  have hδ := xiCriticalFourthTraceResidual_pos F
  have hcharge := xiFourthTraceCriticalAtom_le_residual_unreserved F ⟨q.1, q.property.1⟩
  rw [xiFourthTraceCriticalAtom_at_real γ ⟨q.1, hreal⟩] at hcharge
  have hscaled : 1 ≤ xiCriticalFourthTraceResidual F * γ ^ 4 :=
    (div_le_iff₀ hγ4).mp hcharge
  have hreserve : 0 ≤ xiCriticalFourthTraceReserve F :=
    Finset.sum_nonneg fun r _ => xiFourthTraceCriticalAtom_nonneg r
  have hcap : xiCriticalFourthTraceResidual F < 17 / 200000 := by
    have h := xiCriticalFourthTraceResidual_lt_source_cap F
    linarith only [h, hreserve]
  have hlow : 108 < γ ^ 2 := by
    by_contra! h
    have hs := (sq_le_sq₀ hγ.le (by positivity : (0 : ℝ) ≤ 108)).mpr h
    have hp := mul_lt_mul_of_pos_right hcap hγ4
    nlinarith only [hscaled, hs, hp]
  have hfixed : xiGaussianCertifiedPhaseGap < 2 * γ ^ 2 := by
    rw [xiGaussianCertifiedPhaseGap_eq]
    linarith only [hlow]
  have hroot : Real.sqrt ((82 / 21 : ℝ) / xiCriticalFourthTraceResidual F) <
      2 * γ ^ 2 := by
    apply (Real.sqrt_lt' (mul_pos (by positivity) hγ)).mpr
    rw [div_lt_iff₀ hδ]
    nlinarith only [hscaled]
  exact max_lt_iff.mpr ⟨hfixed, by linarith only [hroot]⟩

theorem xiCriticalResidualPhaseGap_empty_lt_twice_sq
    (q : {q : XiZeroCopy // (xiSpectralPoint q).im = 0}) :
    xiCriticalResidualPhaseGap ∅ < 2 * (xiSpectralPoint q.1).re ^ 2 :=
  xiCriticalResidualPhaseGap_lt_twice_unreserved_sq ∅
    ⟨q.1, Finset.notMem_empty _, q.property⟩

end RHTower
