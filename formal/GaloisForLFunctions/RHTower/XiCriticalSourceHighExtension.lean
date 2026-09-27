import GaloisForLFunctions.RHTower.XiCriticalSourceTailBudget

/-!
# A quantitative limit on improving the source using only high critical nodes

The source gained from any number of copies above `R` is at most `M₀/R`.
For every finite starting selection an explicit cutoff therefore prevents
all high extensions from even halving its residual. This is an obstruction
to a depletion argument based only on successively higher Hardy pairs,
not an obstruction to RH or to using the complete low critical core.
-/

open scoped Real BigOperators
open Complex
noncomputable section

namespace RHTower

def xiCriticalHighExtension (F : Finset XiZeroCopy) (R : ℝ)
    (E : Finset XiZeroCopy) : Finset XiZeroCopy :=
  F ∪ E.filter (fun q => R < (xiSpectralPoint q ^ 2).re)

theorem subset_xiCriticalHighExtension (F E : Finset XiZeroCopy) (R : ℝ) :
    F ⊆ xiCriticalHighExtension F R E := Finset.subset_union_left

/-- Arbitrarily many high copies can spend no more than the entire high-source capacity. -/
theorem xiCriticalHighExtension_residual_gain
    (F E : Finset XiZeroCopy) (R : {R : ℝ // 0 < R}) :
    0 ≤ xiCriticalFourthTraceResidual F -
      xiCriticalFourthTraceResidual (xiCriticalHighExtension F R E) ∧
    xiCriticalFourthTraceResidual F -
      xiCriticalFourthTraceResidual (xiCriticalHighExtension F R E) ≤
        normalizedPrimeArchMoment 0 / (R : ℝ) := by
  classical
  constructor
  · exact sub_nonneg.mpr (xiCriticalFourthTraceResidual_antitone
      (subset_xiCriticalHighExtension F E R))
  · let T := E.filter (fun q => (R : ℝ) < (xiSpectralPoint q ^ 2).re)
    have he := Finset.sum_union_inter (s₁ := F) (s₂ := T) (f := xiFourthTraceCriticalAtom)
    have hnonneg : 0 ≤ ∑ q ∈ F ∩ T, xiFourthTraceCriticalAtom q :=
      Finset.sum_nonneg fun q _ => xiFourthTraceCriticalAtom_nonneg q
    have hcap := xiCriticalFourthTraceReserve_high_le_firstSource R E
    change xiCriticalFourthTraceReserve T ≤ _ at hcap
    unfold xiCriticalFourthTraceResidual xiCriticalFourthTraceReserve xiCriticalHighExtension
    change (normalizedPrimeArchMoment 1 - ∑ q ∈ F, xiFourthTraceCriticalAtom q) -
      (normalizedPrimeArchMoment 1 - ∑ q ∈ F ∪ T, xiFourthTraceCriticalAtom q) ≤ _
    unfold xiCriticalFourthTraceReserve at hcap
    linarith only [he, hnonneg, hcap]

def xiCriticalSourceProtectionRadius (F : Finset XiZeroCopy) : ℝ :=
  1 + 2 * normalizedPrimeArchMoment 0 / xiCriticalFourthTraceResidual F

theorem xiCriticalSourceProtectionRadius_pos (F : Finset XiZeroCopy) :
    0 < xiCriticalSourceProtectionRadius F := by
  unfold xiCriticalSourceProtectionRadius
  exact add_pos zero_lt_one
    (div_pos (mul_pos (by positivity) normalizedPrimeArchMoment_zero_pos)
      (xiCriticalFourthTraceResidual_pos F))

theorem firstSource_div_protectionRadius_lt_half_residual (F : Finset XiZeroCopy) :
    normalizedPrimeArchMoment 0 / xiCriticalSourceProtectionRadius F <
      xiCriticalFourthTraceResidual F / 2 := by
  have hδ := xiCriticalFourthTraceResidual_pos F
  have hprod : xiCriticalSourceProtectionRadius F * xiCriticalFourthTraceResidual F =
      xiCriticalFourthTraceResidual F + 2 * normalizedPrimeArchMoment 0 := by
    unfold xiCriticalSourceProtectionRadius
    field_simp
  apply (div_lt_iff₀ (xiCriticalSourceProtectionRadius_pos F)).mpr
  nlinarith only [hprod, hδ]

/-- A finite starting selection cannot have its residual halved by adding only copies beyond
this explicit squared-height cutoff, regardless of how many are added. -/
theorem half_residual_lt_every_protected_high_extension (F E : Finset XiZeroCopy) :
    xiCriticalFourthTraceResidual F / 2 <
      xiCriticalFourthTraceResidual
        (xiCriticalHighExtension F (xiCriticalSourceProtectionRadius F) E) := by
  have h := (xiCriticalHighExtension_residual_gain F E
    ⟨xiCriticalSourceProtectionRadius F, xiCriticalSourceProtectionRadius_pos F⟩).2
  have hsmall := firstSource_div_protectionRadius_lt_half_residual F
  linarith only [h, hsmall]

def xiCriticalProtectedPhaseGapCap (F : Finset XiZeroCopy) : ℝ :=
  max xiGaussianCertifiedPhaseGap
    (Real.sqrt ((164 / 21 : ℝ) / xiCriticalFourthTraceResidual F) - 1 / 2)

/-- Source protection also bounds the adaptive spectral gap achievable by high extensions. -/
theorem xiCriticalResidualPhaseGap_high_extension_le_cap (F E : Finset XiZeroCopy) :
    xiCriticalResidualPhaseGap
        (xiCriticalHighExtension F (xiCriticalSourceProtectionRadius F) E) ≤
      xiCriticalProtectedPhaseGapCap F := by
  unfold xiCriticalResidualPhaseGap xiCriticalProtectedPhaseGapCap
  apply max_le_max_left
  apply sub_le_sub_right
  apply Real.sqrt_le_sqrt
  have h := div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ 82 / 21)
    (half_pos (xiCriticalFourthTraceResidual_pos F))
    (half_residual_lt_every_protected_high_extension F E).le
  calc
    _ ≤ (82 / 21 : ℝ) / (xiCriticalFourthTraceResidual F / 2) := h
    _ = _ := by ring

/-- Even the scalar whole-phase ceilings have a positive common floor under all such high
extensions. This is a bound on the estimates, not a lower bound on actual imaginary energy. -/
theorem protected_high_extension_phaseBudget_lower (F E : Finset XiZeroCopy) (N : ℕ)
    (s : {s : ℝ // 0 < s}) (t : {t : {t : ℝ // 0 < t} // (s : ℝ) ≤ (t : ℝ)}) :
    (21 / 41 : ℝ) * xiCriticalFourthTraceResidual F *
        Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiCriticalProtectedPhaseGapCap F)) *
          xiGaussianFourthTraceEnvelope N s ≤
      xiGaussianResidualPhaseBudget
        (xiCriticalHighExtension F (xiCriticalSourceProtectionRadius F) E) N s t.1 := by
  let E' := xiCriticalHighExtension F (xiCriticalSourceProtectionRadius F) E
  have he : Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiCriticalProtectedPhaseGapCap F)) ≤
      Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiCriticalResidualPhaseGap E')) := by
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (mul_le_mul_of_nonneg_left
      (xiCriticalResidualPhaseGap_high_extension_le_cap F E) (sub_nonneg.mpr t.property))
  have hδ : (21 / 41 : ℝ) * xiCriticalFourthTraceResidual F ≤
      (42 / 41 : ℝ) * xiCriticalFourthTraceResidual E' := by
    have h := half_residual_lt_every_protected_high_extension F E
    change xiCriticalFourthTraceResidual F / 2 < xiCriticalFourthTraceResidual E' at h
    linarith only [h]
  have h := mul_le_mul hδ he (Real.exp_pos _).le
    (mul_nonneg (by positivity) (xiCriticalFourthTraceResidual_nonneg E'))
  exact mul_le_mul_of_nonneg_right h (xiGaussianFourthTraceEnvelope_nonneg N s)

/-- The common lower bound for the phase ceilings is strictly positive for every nonempty
order and every admissible pair of heat times. -/
theorem protected_high_extension_phaseBudget_lower_pos (F : Finset XiZeroCopy) (n : ℕ)
    (s : {s : ℝ // 0 < s}) (t : ℝ) :
    0 < (21 / 41 : ℝ) * xiCriticalFourthTraceResidual F *
      Real.exp (-((t - (s : ℝ)) * xiCriticalProtectedPhaseGapCap F)) *
        xiGaussianFourthTraceEnvelope (n + 1) s :=
  mul_pos (mul_pos (mul_pos (by positivity) (xiCriticalFourthTraceResidual_pos F))
    (Real.exp_pos _)) (xiGaussianFourthTraceEnvelope_pos n s)

end RHTower
